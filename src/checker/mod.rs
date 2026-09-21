//! A proof checker for Alethe proofs
pub mod error;
mod parallel;
mod rules;
mod sat_refutation;
mod shared;

use crate::{
    CarcaraResult, Error, Status,
    ast::{
        ContextStack, Problem, ProblemPrelude, Proof, ProofCommand, ProofIter, ProofStep, Rc, Term,
        pool::PrimitivePool, rare_rules::Rules,
    },
    benchmarking::{CollectResults, OnlineBenchmarkResults},
    external::{ExternalTool, SatTools},
};
use carcara_macros::GenerateSetters;
use error::CheckerError;
use indexmap::{IndexMap, IndexSet};
use rules::{Premise, RuleArgs, RuleResult};
use shared::{StepCheckContext, check_assume_shared, check_step_core};
use std::{
    collections::HashSet,
    fmt,
    time::{Duration, Instant},
};

pub use parallel::{ParallelProofChecker, scheduler::Scheduler};

// The elaborator needs to use this function to elaborate `bfun_elim` steps
pub(crate) use rules::clausification::apply_bfun_elim;
pub(crate) use rules::linear_arithmetic::la_generic_partial;

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

/// Options for validating trusted theory-rewrite holes using RARE and egglog.
///
/// The checker integration is added by the accompanying RARE engine change; these options are
/// defined here so command-line configuration has a stable, engine-independent API.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RunEgglogOptions {
    /// Maximum number of goal-schedule rounds to execute for a proof step.
    pub max_goal_schedule_rounds: usize,

    /// Run schedules until goals are saturated instead of using the fixed round count.
    pub continuous_saturation: bool,

    /// Cooperative wall-clock budget for a proof step.
    pub timeout: Option<Duration>,

    /// Print the generated egglog program for each checked proof step.
    pub print_egglog: bool,
}

impl Default for RunEgglogOptions {
    fn default() -> Self {
        Self {
            max_goal_schedule_rounds: 3,
            continuous_saturation: false,
            timeout: None,
            print_egglog: false,
        }
    }
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

    /// Whether to validate trusted theory-rewrite holes using RARE and egglog.
    check_hole_rewrites: bool,

    /// Options that will control egglog checks of trusted theory rewrites.
    hole_rewrite_options: RunEgglogOptions,
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
pub struct ProofChecker<'c> {
    pool: &'c mut PrimitivePool,
    config: Config,
    context: ContextStack,
    reached_empty_clause: bool,
    is_holey: bool,
    rare_rules: &'c Rules,
}

impl<'c> ProofChecker<'c> {
    /// Constructs a new `ProofChecker` with a given pool, set of rare rules, and `Config`.
    pub fn new(pool: &'c mut PrimitivePool, rare_rules: &'c Rules, config: Config) -> Self {
        ProofChecker {
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
        self.check_impl(
            problem,
            proof,
            None::<&mut CheckerStatistics<OnlineBenchmarkResults>>,
        )
    }

    /// Checks that `proof` is a valid proof for the given problem, collecting benchmarking
    /// statistics into `stats`.
    pub fn check_with_stats<CR: CollectResults + Send + Default>(
        &mut self,
        problem: &Problem,
        proof: &Proof,
        stats: &mut CheckerStatistics<CR>,
    ) -> CarcaraResult<Status> {
        self.check_impl(problem, proof, Some(stats))
    }

    fn check_impl<CR: CollectResults + Send + Default>(
        &mut self,
        problem: &Problem,
        proof: &Proof,
        mut stats: Option<&mut CheckerStatistics<CR>>,
    ) -> CarcaraResult<Status> {
        // Similarly to the parser, to avoid stack overflows in proofs with many nested subproofs,
        // we check the subproofs iteratively, instead of recursively
        let mut iter = proof.iter();
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
                            file: proof.filename.clone(),
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
                            file: proof.filename.clone(),
                        });
                    }
                }
            }
        }
        if self.reached_empty_clause {
            Ok(if self.is_holey {
                Status::Holey
            } else {
                Status::Valid
            })
        } else {
            Err(Error::DoesNotReachEmptyClause { file: proof.filename.clone() })
        }
    }

    fn check_assume<'i, CR: CollectResults + Send + Default>(
        &mut self,
        id: &str,
        term: &Rc<Term>,
        premises: &IndexSet<Rc<Term>>,
        iter: &'i ProofIter<'i>,
        stats: &mut Option<&mut CheckerStatistics<CR>>,
    ) -> bool {
        check_assume_shared(
            id,
            term,
            premises,
            &self.config,
            iter.is_in_subproof(),
            stats,
        )
    }

    fn check_step<'i, CR: CollectResults + Send + Default>(
        &mut self,
        step: &ProofStep,
        previous_command: Option<Premise>,
        iter: &'i ProofIter<'i>,
        stats: &mut Option<&mut CheckerStatistics<CR>>,
        prelude: &ProblemPrelude,
    ) -> RuleResult {
        let mut polyeq_time = Duration::ZERO;

        // Collect premises and discharge - this part is iterator-specific
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

        // TODO: for now, sat refutation and calling external solvers is only supported in
        // sequential checking mode
        if step.rule == "sat_refutation" && !self.config.allowed_rules.contains("sat_refutation") {
            let premises_steps: Vec<_> =
                step.premises.iter().map(|&p| iter.get_premise(p)).collect();
            return sat_refutation::sat_refutation(
                self.pool,
                premises_steps,
                prelude,
                &self.config.sat_ref_config,
            );
        }

        // Prepare rule arguments - this is pool-specific
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

        // Use shared core logic
        let context = StepCheckContext {
            config: &self.config,
            is_end_step: iter.is_end_step(),
            current_subproof: iter.current_subproof(),
            subproof_depth: iter.depth(),
            is_holey: &mut self.is_holey,
        };

        let result = check_step_core(step, rule_args, context, stats);

        // Update polyeq time in stats (this was previously done in the core,
        // but polyeq_time is updated via the mutable reference in rule_args)
        if let Some(s) = stats {
            s.polyeq_time += polyeq_time;
        }

        result
    }
}
