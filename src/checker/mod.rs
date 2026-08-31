//! A proof checker for Alethe proofs
pub mod error;
mod parallel;
mod rules;
mod sat_refutation;

use crate::{
    CarcaraResult, Error, Status,
    ast::{
        ContextStack, Polyeq, Problem, ProblemPrelude, Proof, ProofCommand, ProofIter, ProofStep,
        Rc, Term, pool::Pool, rare_rules::Rules,
    },
    benchmarking::{CollectResults, OnlineBenchmarkResults},
    external::{ExternalTool, SatTools},
};

use carcara_macros::GenerateSetters;
use error::{CheckerError, SubproofError};
use indexmap::{IndexMap, IndexSet};
use rules::{Premise, RuleArgs, RuleResult, get_rule};
use std::{
    collections::HashSet,
    fmt,
    path::Path,
    time::{Duration, Instant},
};

// The elaborator needs to use this function to elaborate `bfun_elim` steps
pub(crate) use rules::clausification::apply_bfun_elim;
pub(crate) use rules::linear_arithmetic::la_generic_partial;

pub use parallel::ParallelChecker;

/// Benchmarking statistics collected while checking a proof.
#[derive(Clone)]
pub struct CheckerStatistics<'s, CR: CollectResults + Send + Default> {
    /// The name of the proof file being checked.
    pub file_name: &'s str,

    /// Total time spent on `polyeq` operations during checking.
    pub polyeq_time: Duration,

    /// Total time spent checking `assume` steps.
    pub assume_time: Duration,

    /// Time spent comparing `assume` terms with their corresponding `assert` premise, excluding the
    /// time spent searching for the right premise.
    pub assume_core_time: Duration,

    /// The collected benchmarking results.
    pub results: CR,
}

impl<CR: CollectResults + Send + Default> fmt::Debug for CheckerStatistics<'_, CR> {
    // Since `self.results` does not implement `Debug`, we can't just `#[derive(Debug)]` and instead
    // have to implement it manually, removing that field.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CheckerStatistics")
            .field("file_name", &self.file_name)
            .field("polyeq_time", &self.polyeq_time)
            .field("assume_time", &self.assume_time)
            .field("assume_core_time", &self.assume_core_time)
            .finish()
    }
}

/// Configuration for checking `sat_refutation` steps using external tools.
#[derive(Debug, Default, Clone)]
pub enum SatRefConfig {
    /// Don't check `sat_refutation` steps at all.
    #[default]
    None,

    /// Use a single dedicated checker for `sat_refutation`.
    Dedicated(ExternalTool),

    /// Validate the step using a SAT-based pipeline, consisting of a SAT solver, a DRAT checker,
    /// and an SMT solver. See [`SatTools`].
    Sat(SatTools),
}

/// Configuration options for the proof checker.
#[derive(Debug, Default, Clone, GenerateSetters)]
pub struct Config {
    /// If `true`, the checker will assume that the proof is elaborated, and enforce extra
    /// restrictions when checking it.
    ///
    /// Currently, if enabled, the following rules are affected:
    /// - `assume` and `refl`: implicit reordering of equalities is not allowed
    /// - `resolution` and `th_resolution`: the pivots must be provided as arguments
    elaborated: bool,

    /// If `true`, the checker will skip any steps with rules that it does not recognize, and will
    /// consider them as holes. Normally, using an unknown rule is considered an error.
    ignore_unknown_rules: bool,

    /// If `true`, the checker will check resolution steps using only Reverse Unit Propagation
    /// (RUP). Normally, we use a greedy algorithm first, and use RUP as a fallback.
    rup_resolution: bool,

    /// A set of rule names that the checker will allow, considering them holes in the proof.
    #[skip_setter]
    allowed_rules: HashSet<String>,

    /// A map from rule names to external checkers, which are called to check the steps that use
    /// those rules.
    rule_checkers: IndexMap<String, ExternalTool>,

    /// The configuration for checking `sat_refutation` steps. See [`SatRefConfig`].
    sat_ref_config: SatRefConfig,
}

impl Config {
    /// Constructs a new `Config` with all options set to their default values.
    pub fn new() -> Self {
        Self::default()
    }

    /// A set of rule names that the checker will allow, considering them holes in the proof.
    pub fn allowed_rules(mut self, values: impl IntoIterator<Item = impl Into<String>>) -> Self {
        self.allowed_rules = values.into_iter().map(Into::into).collect();
        self
    }
}

/// A proof checker for Alethe.
pub struct Checker<'c> {
    pool: &'c mut Pool,
    config: Config,
    context: ContextStack,
    reached_empty_clause: bool,
    is_holey: bool,
    rare_rules: &'c Rules,
}

impl<'c> Checker<'c> {
    /// Constructs a new `ProofChecker` with a given pool, set of rare rules, and `Config`.
    pub fn new(pool: &'c mut Pool, rare_rules: &'c Rules, config: Config) -> Self {
        Self {
            pool,
            config,
            context: ContextStack::new(),
            reached_empty_clause: false,
            is_holey: false,
            rare_rules,
        }
    }

    /// Checks that `proof` is a valid proof for the given problem.
    ///
    /// Returns `Ok` if the proof is valid, with the proof status.
    pub fn check(&mut self, problem: &Problem, proof: &Proof) -> CarcaraResult<Status> {
        let null_stats = None::<&mut CheckerStatistics<OnlineBenchmarkResults>>;
        let status =
            self.check_commands(problem, &proof.filename, &proof.commands, 0, null_stats)?;
        if self.reached_empty_clause {
            Ok(status)
        } else {
            Err(Error::DoesNotReachEmptyClause { file: proof.filename.clone() })
        }
    }

    /// Checks that `proof` is a valid proof for the given problem, collecting benchmarking
    /// statistics into `stats`.
    pub fn check_with_stats<CR: CollectResults + Send + Default>(
        &mut self,
        problem: &Problem,
        proof: &Proof,
        stats: &mut CheckerStatistics<CR>,
    ) -> CarcaraResult<Status> {
        let status =
            self.check_commands(problem, &proof.filename, &proof.commands, 0, Some(stats))?;
        if self.reached_empty_clause {
            Ok(status)
        } else {
            Err(Error::DoesNotReachEmptyClause { file: proof.filename.clone() })
        }
    }

    /// Checks a sequence of commands.
    ///
    /// This must be a contiguous slice of commands at the proof root level, that is, not inside
    /// a subproof.
    fn check_commands<CR: CollectResults + Send + Default>(
        &mut self,
        problem: &Problem,
        proof_filename: &Path,
        commands: &[ProofCommand],
        start_positon: usize,
        mut stats: Option<&mut CheckerStatistics<CR>>,
    ) -> CarcaraResult<Status> {
        // Similarly to the parser, to avoid stack overflows in proofs with many nested subproofs,
        // we check the subproofs iteratively, instead of recursively
        let mut iter = ProofIter::new_at_position(commands, start_positon);
        while let Some(command) = iter.next() {
            match command {
                ProofCommand::Step(step) => {
                    let is_end_of_subproof = iter.is_end_step();

                    // If this step ends a subproof, it might need to implicitly reference the
                    // previous command in the subproof
                    let previous_command = if is_end_of_subproof {
                        let subproof = iter.current_subproof().unwrap();
                        let index = subproof.len() - 2;
                        subproof
                            .get(index)
                            .map(|command| Premise::new((iter.depth(), index), command))
                    } else {
                        None
                    };
                    self.check_step(step, previous_command, &iter, &mut stats, &problem.prelude)
                        .map_err(|e| Error::Checker {
                            inner: Box::new(e),
                            rule: step.rule.as_str().into(),
                            step: step.id.as_str().into(),
                            file: proof_filename.to_path_buf(),
                        })?;

                    // If this is the last command of a subproof, we have to pop the subproof
                    // commands off of the stack. The parser already ensures that the last command
                    // in a subproof is always a `step` command
                    if is_end_of_subproof {
                        self.context.pop();
                    }

                    // Note that for the purpose of whether the proof of the input assumptions
                    // concludes the empty clause this test must be made only when the context is
                    // empty, i.e., when we are not in a subproof
                    if step.clause.is_empty() && self.context.is_empty() {
                        self.reached_empty_clause = true;
                    }
                }
                ProofCommand::Subproof(s) => {
                    let time = Instant::now();
                    let step_id = command.id();

                    self.context.push(&s.args);

                    if let Some(stats) = &mut stats {
                        let rule_name = match s.commands.last() {
                            Some(ProofCommand::Step(step)) => format!("anchor({})", &step.rule),
                            _ => "anchor".to_owned(),
                        };
                        stats.results.add_step_measurement(
                            stats.file_name,
                            step_id,
                            &rule_name,
                            time.elapsed(),
                        );
                    }
                }
                ProofCommand::Assume { id, term } => {
                    if !self.check_assume(id, term, &problem.premises, &iter, &mut stats) {
                        return Err(Error::Checker {
                            inner: Box::new(CheckerError::Assume(term.clone())),
                            rule: "assume".into(),
                            step: id.as_str().into(),
                            file: proof_filename.to_path_buf(),
                        });
                    }
                }
            }
        }
        Ok(if self.is_holey {
            Status::Holey
        } else {
            Status::Valid
        })
    }

    fn check_assume<'i, CR: CollectResults + Send + Default>(
        &mut self,
        id: &str,
        term: &Rc<Term>,
        premises: &IndexSet<Rc<Term>>,
        iter: &'i ProofIter<'i>,
        stats: &mut Option<&mut CheckerStatistics<CR>>,
    ) -> bool {
        // Some subproofs contain `assume` commands inside them. These don't refer to the original
        // problem premises, but are instead local assumptions that are discharged by the subproof's
        // final step, so we ignore the `assume` command if it is inside a subproof.
        if iter.is_in_subproof() {
            return true;
        }

        let time = Instant::now();

        // Check for exact match first
        if premises.contains(term) {
            let total_time = time.elapsed();
            if let Some(s) = stats {
                s.assume_time += total_time;
                s.results
                    .add_assume_measurement(s.file_name, id, true, total_time);
            }
            return true;
        }

        // If elaborated mode, no polyeq checking allowed
        if self.config.elaborated {
            return false;
        }

        // Perform polyeq checking
        let mut found = false;
        let mut polyeq_time = Duration::ZERO;
        let mut core_time = Duration::ZERO;

        for p in premises {
            let mut this_polyeq_time = Duration::ZERO;

            let mut comp = Polyeq::new().mod_reordering(true).mod_nary(true);
            let result = comp.eq_with_time(term, p, &mut this_polyeq_time);
            let depth = comp.max_depth();

            polyeq_time += this_polyeq_time;

            if let Some(s) = &mut *stats {
                s.results.add_polyeq_depth(depth);
            }
            if result {
                core_time = this_polyeq_time;
                found = true;
                break;
            }
        }

        let total_time = time.elapsed();

        if let Some(s) = stats {
            s.assume_time += total_time;
            s.assume_core_time += core_time;
            s.polyeq_time += polyeq_time;
            s.results
                .add_assume_measurement(s.file_name, id, false, total_time);
        }

        found
    }

    fn check_step<'i, CR: CollectResults + Send + Default>(
        &mut self,
        step: &ProofStep,
        previous_command: Option<Premise>,
        iter: &'i ProofIter<'i>,
        stats: &mut Option<&mut CheckerStatistics<CR>>,
        prelude: &ProblemPrelude,
    ) -> RuleResult {
        let time = Instant::now();

        if self.config.allowed_rules.contains(&step.rule) {
            self.is_holey = true;
            return Ok(());
        }
        if !step.discharge.is_empty() && step.rule != "subproof" {
            return Err(CheckerError::Subproof(SubproofError::DischargeInWrongRule));
        }

        // Collect premises and discharge
        let premises: Vec<_> = step
            .premises
            .iter()
            .map(|&p| {
                let command = iter.get_premise(p);
                Premise::new(p, command)
            })
            .collect();
        let discharge: Vec<_> = step
            .discharge
            .iter()
            .map(|&i| iter.get_premise(i))
            .collect();

        // The sat refutation checking needs the actual premise steps, so we have some special
        // casing here
        if step.rule == "sat_refutation" {
            let premises_steps: Vec<_> =
                step.premises.iter().map(|&p| iter.get_premise(p)).collect();
            return sat_refutation::sat_refutation(
                self.pool,
                premises_steps,
                prelude,
                &self.config.sat_ref_config,
            );
        }

        // Prepare rule arguments
        let mut polyeq_time = Duration::ZERO;
        let rule_args = RuleArgs {
            conclusion: &step.clause,
            premises: &premises,
            args: &step.args,
            pool: self.pool,
            context: &mut self.context,
            previous_command,
            discharge: &discharge,
            polyeq_time: &mut polyeq_time,
            rare_rules: self.rare_rules,
        };
        if let Some(custom_checker) = self.config.rule_checkers.get(&step.rule) {
            return check_external(rule_args.args, custom_checker);
        }

        let rule = match get_rule(
            &step.rule,
            self.config.elaborated,
            self.config.rup_resolution,
        ) {
            Some(r) => r,
            None if self.config.ignore_unknown_rules => {
                self.is_holey = true;
                return Ok(());
            }
            None => {
                return Err(CheckerError::UnknownRule);
            }
        };

        if step.rule == "hole" || step.rule == "lia_generic" {
            self.is_holey = true;
        }

        // Execute the rule with the provided arguments
        rule(rule_args)?;

        if iter.is_end_step()
            && let Some(subproof) = iter.current_subproof()
        {
            check_discharge(subproof, iter.depth(), &step.discharge)?;
        }

        if let Some(s) = stats {
            let elapsed = time.elapsed();
            s.results
                .add_step_measurement(s.file_name, &step.id, &step.rule, elapsed);
            s.polyeq_time += polyeq_time;
        }
        Ok(())
    }
}

fn check_discharge(
    subproof: &[ProofCommand],
    depth: usize,
    discharge: &[(usize, usize)],
) -> RuleResult {
    let discharge: IndexSet<_> = discharge.iter().collect();
    if let Some((_, not_discharged)) = subproof
        .iter()
        .enumerate()
        .find(|&(i, command)| command.is_assume() && !discharge.contains(&(depth, i)))
    {
        Err(CheckerError::Subproof(
            SubproofError::LocalAssumeNotDischarged(not_discharged.id().to_owned()),
        ))
    } else {
        Ok(())
    }
}

fn check_external(args: &[Rc<Term>], checker: &ExternalTool) -> RuleResult {
    let args_str: Vec<String> = args.iter().map(|t| format!("{}", t)).collect();
    let string = format!("(\n{}\n)", args_str.join("\n"));

    let output = checker.call(string.as_bytes())?;

    if !output.status.success() {
        if let Ok(s) = std::str::from_utf8(&output.stderr)
            && s.contains("interrupted by timeout.")
        {
            return Err(CheckerError::Unspecified);
        }
        return Err(CheckerError::Unspecified);
    }
    let res = output.stdout.as_slice();
    if res == b"true\n" {
        return Ok(());
    }
    Err(CheckerError::Explanation(format!(
        "External checker {} did not validate step",
        checker
    )))
}
