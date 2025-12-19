pub mod error;
mod parallel;
mod rules;
mod shared;

use crate::{
    ast::{rare_rules::Rules, *},
    benchmarking::{CollectResults, OnlineBenchmarkResults},
    CarcaraResult, Error,
};
use error::CheckerError;
use indexmap::IndexSet;
pub use parallel::{scheduler::Scheduler, ParallelProofChecker};
use rules::{Premise, Rule, RuleArgs, RuleResult};
use shared::{check_assume_shared, check_step_core, get_rule_shared, StepCheckContext};
use std::{
    collections::HashSet,
    fmt,
    time::{Duration, Instant},
};

pub(crate) use rules::clausification::apply_bfun_elim;

#[derive(Clone)]
pub struct CheckerStatistics<'s, CR: CollectResults + Send + Default> {
    pub file_name: &'s str,
    pub polyeq_time: Duration,
    pub assume_time: Duration,

    // This is the time to compare the `assume` term with the `assert` that matches it. That is,
    // this excludes the time spent searching for the correct `assert` premise.
    pub assume_core_time: Duration,
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

#[derive(Debug, Default, Clone)]
pub struct Config {
    /// If `true`, the checker will assume that the proof is elaborated, and enforce extra
    /// restrictions when checking it.
    ///
    /// Currently, if enabled, the following rules are affected:
    /// - `assume` and `refl`: implicit reordering of equalities is not allowed
    /// - `resolution` and `th_resolution`: the pivots must be provided as arguments
    pub elaborated: bool,

    /// If `true`, the checker will skip any steps with rules that it does not recognize, and will
    /// consider them as holes. Normally, using an unknown rule is considered an error.
    pub ignore_unknown_rules: bool,

    /// A set of rule names that the checker will allow, considering them holes in the proof.
    pub allowed_rules: HashSet<String>,
}

impl Config {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn elaborated(mut self, value: bool) -> Self {
        self.elaborated = value;
        self
    }

    pub fn ignore_unknown_rules(mut self, value: bool) -> Self {
        self.ignore_unknown_rules = value;
        self
    }
}

pub struct ProofChecker<'c> {
    pool: &'c mut PrimitivePool,
    config: Config,
    context: ContextStack,
    reached_empty_clause: bool,
    is_holey: bool,
    rare_rules: &'c Rules,
}

impl<'c> ProofChecker<'c> {
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

    pub fn check(&mut self, problem: &Problem, proof: &Proof) -> CarcaraResult<bool> {
        self.check_impl(
            problem,
            proof,
            None::<&mut CheckerStatistics<OnlineBenchmarkResults>>,
        )
    }

    pub fn check_with_stats<CR: CollectResults + Send + Default>(
        &mut self,
        problem: &Problem,
        proof: &Proof,
        stats: &mut CheckerStatistics<CR>,
    ) -> CarcaraResult<bool> {
        self.check_impl(problem, proof, Some(stats))
    }

    fn check_impl<CR: CollectResults + Send + Default>(
        &mut self,
        problem: &Problem,
        proof: &Proof,
        mut stats: Option<&mut CheckerStatistics<CR>>,
    ) -> CarcaraResult<bool> {
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
                    self.check_step(step, previous_command, &iter, &mut stats)
                        .map_err(|e| Error::Checker {
                            inner: e,
                            rule: step.rule.as_str().into(),
                            step: step.id.as_str().into(),
                        })?;

                    // If this is the last command of a subproof, we have to pop the subproof
                    // commands off of the stack. The parser already ensures that the last command
                    // in a subproof is always a `step` command
                    if is_end_of_subproof {
                        self.context.pop();
                    }

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
                            inner: CheckerError::Assume(term.clone()),
                            rule: "assume".into(),
                            step: id.as_str().into(),
                        });
                    }
                }
            }
        }
        if self.reached_empty_clause {
            Ok(self.is_holey)
        } else {
            Err(Error::DoesNotReachEmptyClause)
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

    pub fn get_rule(rule_name: &str, elaborated: bool) -> Option<Rule> {
        get_rule_shared(rule_name, elaborated)
    }
}
