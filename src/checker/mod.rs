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
    benchmarking::CollectStats,
    external::{ExternalError, ExternalTool, SatTools},
};

use carcara_macros::GenerateSetters;
use error::{CheckerError, err};
use indexmap::{IndexMap, IndexSet};
use rules::{Premise, RuleArgs, RuleResult, get_rule};
use std::{
    collections::HashSet,
    path::Path,
    time::{Duration, Instant},
};

// The elaborator needs to use this function to elaborate `bfun_elim` steps
pub(crate) use rules::clausification::apply_bfun_elim;
pub(crate) use rules::linear_arithmetic::la_generic_partial;

pub use parallel::ParallelChecker;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct CheckingStats {
    /// Total time spent checking the proof.
    pub total: Duration,

    /// Total time spent on `polyeq` operations during checking.
    pub polyeq_time: Duration,

    /// Total time spent checking `assume` steps.
    pub assume_time: Duration,

    /// Time spent comparing `assume` terms with their corresponding `assert` premise.
    ///
    /// This excludes the time spent searching for the right premise.
    pub assume_compare_time: Duration,
}

impl CheckingStats {
    fn combine(self, other: Self) -> Self {
        Self {
            total: self.total + other.total,
            polyeq_time: self.polyeq_time + other.polyeq_time,
            assume_time: self.assume_time + other.assume_time,
            assume_compare_time: self.assume_compare_time + other.assume_compare_time,
        }
    }

    pub fn polyeq_ratio(&self) -> f64 {
        self.polyeq_time.as_secs_f64() / self.total.as_secs_f64()
    }

    pub fn assume_ratio(&self) -> f64 {
        self.assume_time.as_secs_f64() / self.total.as_secs_f64()
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
    run_stats: CheckingStats,
}

impl<'c> Checker<'c> {
    /// Constructs a new `Checker` with a given pool, set of rare rules, and `Config`.
    pub fn new(pool: &'c mut Pool, rare_rules: &'c Rules, config: Config) -> Self {
        Self {
            pool,
            config,
            context: ContextStack::new(),
            reached_empty_clause: false,
            is_holey: false,
            rare_rules,
            run_stats: CheckingStats::default(),
        }
    }

    /// Checks that `proof` is a valid proof for the given problem.
    ///
    /// Returns `Ok` if the proof is valid, with the proof status.
    pub fn check(&mut self, problem: &Problem, proof: &Proof) -> CarcaraResult<Status> {
        let (status, _) = self.check_with_stats(problem, proof, &mut ())?;
        Ok(status)
    }

    /// Checks that `proof` is a valid proof for the given problem, collecting benchmarking
    /// statistics into `stats`.
    pub fn check_with_stats<S: CollectStats>(
        &mut self,
        problem: &Problem,
        proof: &Proof,
        stats: &mut S,
    ) -> CarcaraResult<(Status, CheckingStats)> {
        let start = Instant::now();
        let result = self.check_commands(problem, &proof.filename, &proof.commands, 0, stats);
        self.run_stats.total = start.elapsed();

        // Restore checker state to default before returning
        let reached_empty_clause = std::mem::take(&mut self.reached_empty_clause);
        self.is_holey = false;
        self.context = ContextStack::new();
        let run_stats = std::mem::take(&mut self.run_stats);

        let status = result?;
        if !reached_empty_clause {
            return Err(Error::DoesNotReachEmptyClause { file: proof.filename.clone() });
        }
        Ok((status, run_stats))
    }

    /// Checks a sequence of commands.
    ///
    /// This must be a contiguous slice of commands at the proof root level, that is, not inside
    /// a subproof. Only the commands from `start_position` to the end of `commands` are actually
    /// checked; the preceding commands are used only to resolve premises and the subproof context.
    fn check_commands<S: CollectStats>(
        &mut self,
        problem: &Problem,
        proof_file_name: &Path,
        commands: &[ProofCommand],
        start_position: usize,
        stats: &mut S,
    ) -> CarcaraResult<Status> {
        // Similarly to the parser, to avoid stack overflows in proofs with many nested subproofs,
        // we check the subproofs iteratively, instead of recursively
        let mut iter = ProofIter::new_at_position(commands, start_position);
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

                    let time = Instant::now();
                    self.check_step(step, previous_command, &iter, &problem.prelude)
                        .and_then(|()| match iter.current_subproof() {
                            // The last step of a subproof must discharge all of its local
                            // assumptions
                            Some(subproof) if is_end_of_subproof => {
                                check_discharge(subproof, iter.depth(), &step.discharge)
                            }
                            _ => Ok(()),
                        })
                        .map_err(|e| e.at(&step.id, &step.rule, proof_file_name))?;
                    let time = time.elapsed();
                    stats.add_step_measurement(proof_file_name, &step.id, &step.rule, time);

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
                    self.context.push(&s.args);
                    let id = command.id();
                    stats.add_step_measurement(proof_file_name, id, "anchor", time.elapsed());
                }
                // Some subproofs contain `assume` commands inside them. These don't refer to the
                // original problem premises, but are instead local assumptions that are discharged
                // by the subproof's final step, so we ignore the `assume` command if it is inside
                // a subproof.
                ProofCommand::Assume { .. } if iter.is_in_subproof() => {}
                ProofCommand::Assume { id, term } => {
                    let time = Instant::now();
                    let was_easy = self
                        .check_assume(term, &problem.premises, stats)
                        .map_err(|e| e.at(id, "assume", proof_file_name))?;
                    stats.add_assume_measurement(proof_file_name, id, was_easy, time.elapsed());
                }
            }
        }
        Ok(if self.is_holey {
            Status::Holey
        } else {
            Status::Valid
        })
    }

    /// Checks an assume command, returning `Ok` if it is valid, and a boolean describing whether it
    /// was "easy", that is, did not require polyequality checking.
    fn check_assume<S: CollectStats>(
        &mut self,
        term: &Rc<Term>,
        premises: &IndexSet<Rc<Term>>,
        stats: &mut S,
    ) -> Result<bool, CheckerError> {
        let time = Instant::now();

        // Check for exact match first
        if premises.contains(term) {
            let total_time = time.elapsed();
            self.run_stats.assume_time += total_time;
            return Ok(true);
        }

        // If elaborated mode, no polyeq checking allowed
        if self.config.elaborated {
            return Err(CheckerError::Assume(term.clone()));
        }

        // Perform polyeq checking
        let mut found = false;
        let mut polyeq_time = Duration::ZERO;
        let mut compare_time = Duration::ZERO;

        for p in premises {
            let mut this_polyeq_time = Duration::ZERO;

            let mut comp = Polyeq::new().mod_reordering(true).mod_nary(true);
            let result = comp.eq_with_time(term, p, &mut this_polyeq_time);
            let depth = comp.max_depth();

            polyeq_time += this_polyeq_time;

            stats.add_polyeq_depth(depth);
            if result {
                compare_time = this_polyeq_time;
                found = true;
                break;
            }
        }

        let total_time = time.elapsed();

        self.run_stats.assume_time += total_time;
        self.run_stats.assume_compare_time += compare_time;
        self.run_stats.polyeq_time += polyeq_time;

        if found {
            Ok(false)
        } else {
            Err(CheckerError::Assume(term.clone()))
        }
    }

    fn check_step<'i>(
        &mut self,
        step: &ProofStep,
        previous_command: Option<Premise>,
        iter: &'i ProofIter<'i>,
        prelude: &ProblemPrelude,
    ) -> RuleResult {
        if self.config.allowed_rules.contains(&step.rule) {
            self.is_holey = true;
            return Ok(());
        }
        if !step.discharge.is_empty() && step.rule != "subproof" {
            return err!("only the `subproof` rule may discharge local assumptions");
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
                &step.clause,
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
        // TODO: only passing args, not conclusion?
        if let Some(custom_checker) = self.config.rule_checkers.get(&step.rule) {
            check_external(rule_args.args, custom_checker)?;
            return Ok(());
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

        self.run_stats.polyeq_time += polyeq_time;
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
        err!(
            "local assumption '{}' was not discharged",
            not_discharged.id(),
        )
    } else {
        Ok(())
    }
}

fn check_external(
    args: &[impl std::fmt::Display],
    checker: &ExternalTool,
) -> Result<(), ExternalError> {
    let args_str: Vec<String> = args.iter().map(|t| format!("{}", t)).collect();
    let string = format!("(\n{}\n)", args_str.join("\n"));

    let output = checker.call(string.as_bytes())?;

    if !output.status.success() {
        if let Ok(s) = std::str::from_utf8(&output.stderr)
            && s.contains("interrupted by timeout.")
        {
            return Err(ExternalError::Timeout);
        }
        return Err(ExternalError::FailedExit(output.status));
    }
    let res = output.stdout.as_slice();
    if res == b"true\n" {
        return Ok(());
    }
    Err(ExternalError::StepNotValidated(checker.clone()))
}
