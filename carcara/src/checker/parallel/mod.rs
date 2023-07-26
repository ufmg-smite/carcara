pub mod scheduler;

use super::error::CheckerError;
use super::rules::{Premise, RuleArgs, RuleResult};
use super::{lia_generic, Config};
use crate::benchmarking::{CollectResults, OnlineBenchmarkResults};
use crate::checker::CheckerStatistics;
use crate::{
    ast::{pool::advanced::*, *},
    CarcaraResult, Error,
};
use ahash::AHashSet;
pub use scheduler::{ScheduleIter, Scheduler};
use std::{
    ops::ControlFlow,
    sync::{Arc, RwLock},
    thread,
    time::{Duration, Instant},
};

pub struct ParallelProofChecker<'c> {
    pool: Arc<PrimitivePool>,
    config: Config,
    prelude: &'c ProblemPrelude,
    context: ContextStack,
    reached_empty_clause: bool,
    is_holey: bool,
    stack_size: usize,
}

impl<'c> ParallelProofChecker<'c> {
    pub fn new(
        pool: Arc<PrimitivePool>,
        config: Config,
        prelude: &'c ProblemPrelude,
        stack_size: usize,
    ) -> Self {
        ParallelProofChecker {
            pool,
            config,
            prelude,
            context: ContextStack::new(),
            reached_empty_clause: false,
            is_holey: false,
            stack_size,
        }
    }

    /// Copies the proof checker and instantiate parallel fields to be shared between threads
    pub fn share(&self) -> Self {
        ParallelProofChecker {
            pool: self.pool.clone(),
            config: self.config.clone(),
            prelude: self.prelude,
            context: ContextStack::new(),
            reached_empty_clause: false,
            is_holey: false,
            stack_size: self.stack_size,
        }
    }

    pub fn check<'s>(&'s mut self, proof: &Proof, scheduler: &'s Scheduler) -> CarcaraResult<bool> {
        // Used to estimulate threads to abort prematurely (only happens when a
        // thread already found out an invalid step)
        let premature_abort = Arc::new(RwLock::new(false));
        let context_pool = ContextPool::from_global(&self.pool);
        //
        thread::scope(|s| {
            let threads: Vec<_> = scheduler
                .loads
                .iter()
                .enumerate()
                .map(|(i, schedule)| {
                    // Shares the self between threads
                    let mut local_self = self.share();
                    let mut local_pool = LocalPool::from_previous(&context_pool);
                    let should_abort = premature_abort.clone();

                    thread::Builder::new()
                        .name(format!("worker-{i}"))
                        .stack_size(self.stack_size)
                        .spawn_scoped(s, move || -> CarcaraResult<(bool, bool)> {
                            let mut iter = schedule.iter(&proof.commands[..]);
                            let mut last_depth = 0;

                            while let Some(command) = iter.next() {
                                // If there is any depth difference between the current and last step
                                while (last_depth - iter.depth() as i64 > 0)
                                    || (last_depth - iter.depth() as i64 == 0
                                        && matches!(command, ProofCommand::Subproof(_)))
                                {
                                    // If this is the last command of a subproof, we have to pop off the subproof
                                    // commands of the stack. The parser already ensures that the last command
                                    // in a subproof is always a `step` command
                                    local_self.context.pop();
                                    last_depth -= 1;
                                }
                                last_depth = iter.depth() as i64;

                                match command {
                                    ProofCommand::Step(step) => {
                                        // If this step ends a subproof, it might need to implicitly reference the
                                        // previous command in the subproof
                                        let previous_command = if iter.is_end_step() {
                                            let subproof = iter.current_subproof().unwrap();
                                            let index = subproof.len() - 2;
                                            subproof.get(index).map(|command| {
                                                Premise::new((iter.depth(), index), command)
                                            })
                                        } else {
                                            None
                                        };

                                        local_self
                                            .check_step(
                                                step,
                                                previous_command,
                                                &iter,
                                                &mut local_pool,
                                                None::<
                                                    &mut CheckerStatistics<OnlineBenchmarkResults>,
                                                >,
                                            )
                                            .map_err(|e| {
                                                // Signalize to other threads to stop the proof checking
                                                *should_abort.write().unwrap() = true;
                                                Error::Checker {
                                                    inner: e,
                                                    rule: step.rule.clone(),
                                                    step: step.id.clone(),
                                                }
                                            })?;

                                        if step.clause.is_empty() {
                                            local_self.reached_empty_clause = true;
                                        }
                                    }
                                    ProofCommand::Subproof(s) => {
                                        let step_id = command.id();

                                        local_self
                                            .context
                                            .push(
                                                &mut local_pool,
                                                &s.assignment_args,
                                                &s.variable_args,
                                            )
                                            .map_err(|e| {
                                                // Signalize to other threads to stop the proof checking
                                                *should_abort.write().unwrap() = true;
                                                Error::Checker {
                                                    inner: e.into(),
                                                    rule: "anchor".into(),
                                                    step: step_id.to_owned(),
                                                }
                                            })?;
                                    }
                                    ProofCommand::Assume { id, term } => {
                                        if !local_self.check_assume(
                                            id,
                                            term,
                                            &proof.premises,
                                            &iter,
                                            None::<&mut CheckerStatistics<OnlineBenchmarkResults>>,
                                        ) {
                                            // Signalize to other threads to stop the proof checking
                                            *should_abort.write().unwrap() = true;
                                            return Err(Error::Checker {
                                                inner: CheckerError::Assume(term.clone()),
                                                rule: "assume".into(),
                                                step: id.clone(),
                                            });
                                        }
                                    }
                                }
                                // Verify if any of the other threads found an error and abort in case of positive
                                if *should_abort.read().unwrap() {
                                    break;
                                }
                            }

                            // Returns Ok(reached empty clause, isHoley, current thread statistics)
                            if local_self.config.is_running_test || local_self.reached_empty_clause
                            {
                                Ok((true, local_self.is_holey))
                            } else {
                                Ok((false, local_self.is_holey))
                            }
                        })
                        .unwrap()
                })
                .collect();

            // Unify the results of all threads and generate the final result based on them
            let (mut reached, mut holey) = (false, false);
            let mut err: Result<_, Error> = Ok(());

            // Wait until the threads finish and merge the results and statistics
            threads
                .into_iter()
                .map(|t| t.join().unwrap())
                .try_for_each(|opt| {
                    match opt {
                        Ok((_reached, _holey)) => {
                            // Mask the result booleans
                            (reached, holey) = (reached | _reached, holey | _holey);
                            ControlFlow::Continue(())
                        }
                        Err(e) => {
                            err = Err(e);
                            ControlFlow::Break(())
                        }
                    }
                });

            // If an error happend
            err?;

            if reached {
                Ok(holey)
            } else {
                Err(Error::DoesNotReachEmptyClause)
            }
        })
    }

    pub fn check_with_stats<'s, CR: CollectResults + Send + Default>(
        &'s mut self,
        proof: &Proof,
        scheduler: &'s Scheduler,
        stats: &'s mut CheckerStatistics<CR>,
    ) -> CarcaraResult<bool> {
        // Used to estimulate threads to abort prematurely (only happens when a
        // thread already found out an invalid step)
        let premature_abort = Arc::new(RwLock::new(false));
        let context_pool = ContextPool::from_global(&self.pool);
        //
        thread::scope(|s| {
            let threads: Vec<_> = scheduler
                .loads
                .iter()
                .enumerate()
                .map(|(i, schedule)| {
                    let mut local_stats = CheckerStatistics {
                        file_name: "",
                        elaboration_time: Duration::ZERO,
                        polyeq_time: Duration::ZERO,
                        assume_time: Duration::ZERO,
                        assume_core_time: Duration::ZERO,
                        results: CR::new(),
                    };
                    // Shares the proof checker between threads
                    let mut local_self = self.share();
                    let mut local_pool = LocalPool::from_previous(&context_pool);
                    let should_abort = premature_abort.clone();

                    thread::Builder::new()
                        .name(format!("worker-{i}"))
                        .stack_size(self.stack_size)
                        .spawn_scoped(
                            s,
                            move || -> CarcaraResult<(bool, bool, CheckerStatistics<CR>)> {
                                let mut iter = schedule.iter(&proof.commands[..]);
                                let mut last_depth = 0;

                                while let Some(command) = iter.next() {
                                    // If there is any depth difference between the current and last step
                                    while (last_depth - iter.depth() as i64 > 0)
                                        || (last_depth - iter.depth() as i64 == 0
                                            && matches!(command, ProofCommand::Subproof(_)))
                                    {
                                        // If this is the last command of a subproof, we have to pop off the subproof
                                        // commands of the stack. The parser already ensures that the last command
                                        // in a subproof is always a `step` command
                                        local_self.context.pop();
                                        last_depth -= 1;
                                    }
                                    last_depth = iter.depth() as i64;

                                    match command {
                                        ProofCommand::Step(step) => {
                                            // If this step ends a subproof, it might need to implicitly reference the
                                            // previous command in the subproof
                                            let previous_command = if iter.is_end_step() {
                                                let subproof = iter.current_subproof().unwrap();
                                                let index = subproof.len() - 2;
                                                subproof.get(index).map(|command| {
                                                    Premise::new((iter.depth(), index), command)
                                                })
                                            } else {
                                                None
                                            };

                                            local_self
                                                .check_step(
                                                    step,
                                                    previous_command,
                                                    &iter,
                                                    &mut local_pool,
                                                    Some(&mut local_stats),
                                                )
                                                .map_err(|e| {
                                                    // Signalize to other threads to stop the proof checking
                                                    *should_abort.write().unwrap() = true;
                                                    Error::Checker {
                                                        inner: e,
                                                        rule: step.rule.clone(),
                                                        step: step.id.clone(),
                                                    }
                                                })?;

                                            if step.clause.is_empty() {
                                                local_self.reached_empty_clause = true;
                                            }
                                        }
                                        ProofCommand::Subproof(s) => {
                                            let time = Instant::now();
                                            let step_id = command.id();

                                            local_self
                                                .context
                                                .push(
                                                    &mut local_pool,
                                                    &s.assignment_args,
                                                    &s.variable_args,
                                                )
                                                .map_err(|e| {
                                                    // Signalize to other threads to stop the proof checking
                                                    *should_abort.write().unwrap() = true;
                                                    Error::Checker {
                                                        inner: e.into(),
                                                        rule: "anchor".into(),
                                                        step: step_id.to_owned(),
                                                    }
                                                })?;

                                            // Collects statistics
                                            let rule_name = match s.commands.last() {
                                                Some(ProofCommand::Step(step)) => {
                                                    format!("anchor({})", &step.rule)
                                                }
                                                _ => "anchor".to_owned(),
                                            };

                                            local_stats.results.add_step_measurement(
                                                local_stats.file_name,
                                                step_id,
                                                &rule_name,
                                                time.elapsed(),
                                            );
                                        }
                                        ProofCommand::Assume { id, term } => {
                                            if !local_self.check_assume(
                                                id,
                                                term,
                                                &proof.premises,
                                                &iter,
                                                Some(&mut local_stats),
                                            ) {
                                                // Signalize to other threads to stop the proof checking
                                                *should_abort.write().unwrap() = true;
                                                return Err(Error::Checker {
                                                    inner: CheckerError::Assume(term.clone()),
                                                    rule: "assume".into(),
                                                    step: id.clone(),
                                                });
                                            }
                                        }
                                    }
                                    // Verify if any of the other threads found an error and abort in case of positive
                                    if *should_abort.read().unwrap() {
                                        break;
                                    }
                                }

                                // Returns Ok(reached empty clause, isHoley, current thread statistics)
                                if local_self.config.is_running_test
                                    || local_self.reached_empty_clause
                                {
                                    Ok((true, local_self.is_holey, local_stats))
                                } else {
                                    Ok((false, local_self.is_holey, local_stats))
                                }
                            },
                        )
                        .unwrap()
                })
                .collect();

            // Unify the results of all threads and generate the final result based on them
            let (mut reached, mut holey) = (false, false);
            let mut err: Result<_, Error> = Ok(());

            // Wait until the threads finish and merge the results and statistics
            threads
                .into_iter()
                .map(|t| t.join().unwrap())
                .for_each(|opt| {
                    match opt {
                        Ok((_reached, _holey, mut local_stats)) => {
                            // Combine the statistics
                            // Takes the external and local benchmark results to local variables and combine them
                            let main = std::mem::take(&mut stats.results);
                            let to_merge = std::mem::take(&mut local_stats.results);
                            stats.results = CR::combine(main, to_merge);

                            // Make sure other times are updated
                            stats.elaboration_time += local_stats.elaboration_time;
                            stats.polyeq_time += local_stats.polyeq_time;
                            stats.assume_time += local_stats.assume_time;
                            stats.assume_core_time += local_stats.assume_core_time;

                            // Mask the result booleans
                            (reached, holey) = (reached | _reached, holey | _holey);
                        }
                        Err(e) => {
                            // Since we want the statistics of the whole run
                            // (even in a error case) we cannot abort at this
                            // point, since we can have more threads to be
                            // evaluated and their statistics colleted
                            err = Err(e);
                        }
                    }
                });

            // If an error happend
            err?;

            if reached {
                Ok(holey)
            } else {
                Err(Error::DoesNotReachEmptyClause)
            }
        })
    }

    fn check_assume<CR: CollectResults + Send + Default>(
        &mut self,
        id: &str,
        term: &Rc<Term>,
        premises: &AHashSet<Rc<Term>>,
        iter: &ScheduleIter,
        mut stats: Option<&mut CheckerStatistics<CR>>,
    ) -> bool {
        let time = Instant::now();

        // Some subproofs contain `assume` commands inside them. These don't refer
        // to the original problem premises, so we ignore the `assume` command if
        // it is inside a subproof. Since the unit tests for the rules don't define the
        // original problem, but sometimes use `assume` commands, we also skip the
        // command if we are in a testing context.
        if self.config.is_running_test || iter.is_in_subproof() {
            return true;
        }

        if premises.contains(term) {
            if let Some(s) = stats {
                let time = time.elapsed();
                s.assume_time += time;
                s.results
                    .add_assume_measurement(s.file_name, id, true, time);
            }
            return true;
        }

        if self.config.strict {
            return false;
        }

        let mut found = None;
        let mut polyeq_time = Duration::ZERO;
        let mut core_time = Duration::ZERO;

        for p in premises {
            let mut this_polyeq_time = Duration::ZERO;
            let (result, depth) = tracing_polyeq(term, p, &mut this_polyeq_time);
            polyeq_time += this_polyeq_time;
            if let Some(s) = &mut stats {
                s.results.add_polyeq_depth(depth);
            }
            if result {
                core_time = this_polyeq_time;
                found = Some(p.clone());
                break;
            }
        }

        if found.is_none() {
            return false;
        }

        if let Some(s) = stats {
            let time = time.elapsed();
            s.assume_time += time;
            s.assume_core_time += core_time;
            s.polyeq_time += polyeq_time;
            s.results
                .add_assume_measurement(s.file_name, id, false, time);
        }

        true
    }

    fn check_step<'a, CR: CollectResults + Send + Default>(
        &mut self,
        step: &'a ProofStep,
        previous_command: Option<Premise<'a>>,
        iter: &'a ScheduleIter<'a>,
        pool: &mut LocalPool,
        stats: Option<&'a mut CheckerStatistics<CR>>,
    ) -> RuleResult {
        let time = Instant::now();
        let mut polyeq_time = Duration::ZERO;

        if step.rule == "lia_generic" {
            if self.config.lia_via_cvc5 {
                let is_hole = lia_generic::lia_generic_multi_thread(&step.clause, self.prelude);
                self.is_holey = self.is_holey || is_hole;
            } else {
                log::warn!("encountered \"lia_generic\" rule, ignoring");
                self.is_holey = true;
            }
        } else {
            let rule = match super::ProofChecker::get_rule(&step.rule, self.config.strict) {
                Some(r) => r,
                None if self.config.skip_unknown_rules => {
                    self.is_holey = true;
                    return Ok(());
                }
                None => return Err(CheckerError::UnknownRule),
            };

            if step.rule == "hole" {
                self.is_holey = true;
            }

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

            let rule_args = RuleArgs {
                conclusion: &step.clause,
                premises: &premises,
                args: &step.args,
                pool,
                context: &mut self.context,
                previous_command,
                discharge: &discharge,
                polyeq_time: &mut polyeq_time,
            };

            rule(rule_args)?;
        }

        if let Some(s) = stats {
            let time = time.elapsed();
            s.results
                .add_step_measurement(s.file_name, &step.id, &step.rule, time);
            s.polyeq_time += polyeq_time;
        }
        Ok(())
    }
}
