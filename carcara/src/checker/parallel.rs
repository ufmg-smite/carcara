#![allow(unused_imports)]
#![allow(dead_code)]

use super::error::CheckerError;
use super::rules::{Premise, Rule, RuleArgs, RuleResult};
#[cfg(feature = "thread-safety")]
use super::scheduler::{iter::ScheduleIter, Scheduler::Scheduler};
use super::{context::*, lia_generic, CheckerStatistics, Config};
use crate::{ast::*, CarcaraResult, Error};
use ahash::AHashSet;
use std::sync::RwLock;
use std::{
    sync::{Arc, Mutex},
    time::{Duration, Instant},
};

unsafe impl Sync for CheckerStatistics<'_> {}
unsafe impl Send for CheckerStatistics<'_> {}

pub struct ParallelProofChecker<'c> {
    config: Config<'c>,
    prelude: Rc<ProblemPrelude>,
    context: ContextStack,
    reached_empty_clause: bool,
    is_holey: bool,
}

#[cfg(feature = "thread-safety")]
impl<'c> ParallelProofChecker<'c> {
    pub fn new(config: Config<'c>, prelude: ProblemPrelude, context_usage: &Vec<usize>) -> Self {
        ParallelProofChecker {
            config,
            prelude: Rc::new(prelude),
            context: ContextStack::from_usage(context_usage),
            reached_empty_clause: false,
            is_holey: false,
        }
    }

    /// Copies the proof checker and instantiate parallel fields
    pub fn parallelize_self(&self) -> Self {
        ParallelProofChecker {
            config: Config {
                strict: self.config.strict,
                skip_unknown_rules: self.config.skip_unknown_rules,
                is_running_test: self.config.is_running_test,
                statistics: None,
                check_lia_using_cvc5: self.config.check_lia_using_cvc5,
            },
            prelude: Rc::clone(&self.prelude),
            context: ContextStack::from_previous(&self.context),
            reached_empty_clause: false,
            is_holey: false,
        }
    }

    pub fn check<'s, 'p>(
        &'s mut self,
        proof: &'p Proof,
        pool: &TermPool,
        scheduler: Scheduler,
    ) -> CarcaraResult<bool> {
        let dyn_pool = Arc::new(pool.dyn_pool.clone());

        crossbeam::scope(|s| {
            let threads: Vec<_> = scheduler
                .loads
                .into_iter()
                .enumerate()
                .map(|(i, schedule)| {
                    let mut local_self = self.parallelize_self();
                    let mut merged_pool = TermPool::from_previous(&dyn_pool);

                    s.builder()
                        .name(format!("worker-{i}"))
                        .spawn(move |_| -> CarcaraResult<(bool, bool)> {
                            let mut iter = schedule.iter();

                            while let Some(command) = iter.next() {
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
                                                &mut merged_pool,
                                            )
                                            .map_err(|e| Error::Checker {
                                                inner: e,
                                                rule: step.rule.clone(),
                                                step: step.id.clone(),
                                            })?;

                                        if step.clause.is_empty() {
                                            local_self.reached_empty_clause = true;
                                        }
                                    }
                                    ProofCommand::Subproof(s) => {
                                        let step_id = command.id();

                                        local_self
                                            .context
                                            .push_from_id(
                                                &mut merged_pool,
                                                &s.assignment_args,
                                                &s.variable_args,
                                                s.context_id,
                                            )
                                            .map_err(|e| Error::Checker {
                                                inner: e.into(),
                                                rule: "anchor".into(),
                                                step: step_id.to_owned(),
                                            })?;
                                    }
                                    ProofCommand::Assume { id, term } => {
                                        local_self.check_assume(
                                            id,
                                            term,
                                            &proof.premises,
                                            &iter,
                                        )?;
                                    }
                                    ProofCommand::Closing => {
                                        // If this is the last command of a subproof, we have to pop the subproof
                                        // commands off of the stack. The parser already ensures that the last command
                                        // in a subproof is always a `step` command
                                        local_self.context.pop();
                                    }
                                }
                            }

                            // Returns Ok(reached empty clause, isHoley)
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
            let mut err: Result<(bool, bool), Error> = Ok((false, false));

            for opt in threads.into_iter().map(|t| t.join().unwrap()) {
                match opt {
                    Ok((_reached, _holey)) => {
                        (reached, holey) = (reached | _reached, holey | _holey);
                    }
                    Err(_) => {
                        err = opt;
                        break;
                    }
                }
            }
            // If an error happend
            if let Err(x) = err {
                return Err(x);
            }

            if reached {
                Ok(holey)
            } else {
                Err(Error::DoesNotReachEmptyClause)
            }
        })
        .unwrap()
    }

    fn check_assume(
        &mut self,
        id: &str,
        term: &Rc<Term>,
        premises: &AHashSet<Rc<Term>>,
        iter: &ScheduleIter,
    ) -> CarcaraResult<()> {
        // Some subproofs contain `assume` commands inside them. These don't refer
        // to the original problem premises, so we ignore the `assume` command if
        // it is inside a subproof. Since the unit tests for the rules don't define the
        // original problem, but sometimes use `assume` commands, we also skip the
        // command if we are in a testing context.
        if self.config.is_running_test || iter.is_in_subproof() {
            return Ok(());
        }

        if premises.contains(term) {
            return Ok(());
        }

        let mut found = None;
        let mut deep_eq_time = Duration::ZERO;
        for p in premises {
            let mut this_deep_eq_time = Duration::ZERO;
            let (result, _) = tracing_deep_eq(term, p, &mut this_deep_eq_time);
            deep_eq_time += this_deep_eq_time;
            if result {
                found = Some(p.clone());
                break;
            }
        }

        if let Some(_) = found {
            Ok(())
        } else {
            Err(Error::Checker {
                inner: CheckerError::Assume(term.clone()),
                rule: "assume".into(),
                step: id.to_owned(),
            })
        }
    }

    fn check_step<'a>(
        &mut self,
        step: &'a ProofStep,
        previous_command: Option<Premise<'a>>,
        iter: &'a ScheduleIter<'a>,
        pool: &mut TermPool,
    ) -> RuleResult {
        let mut deep_eq_time = Duration::ZERO;

        if step.rule == "lia_generic" {
            if self.config.check_lia_using_cvc5 {
                let is_hole =
                    lia_generic::lia_generic(pool, &step.clause, &self.prelude, None, &step.id);
                self.is_holey = self.is_holey || is_hole;
            } else {
                log::warn!("encountered \"lia_generic\" rule, ignoring");
                self.is_holey = true;
            }
        } else {
            let rule = match Self::get_rule(&step.rule, self.config.strict) {
                Some(r) => r,
                None if self.config.skip_unknown_rules => {
                    self.is_holey = true;
                    return Ok(());
                }
                None => return Err(CheckerError::UnknownRule),
            };

            if step.rule == "hole" || step.rule == "trust" {
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
                deep_eq_time: &mut deep_eq_time,
            };

            rule(rule_args)?;
        }

        Ok(())
    }

    pub fn get_rule(rule_name: &str, strict: bool) -> Option<Rule> {
        use super::rules::*;

        Some(match rule_name {
            "true" => tautology::r#true,
            "false" => tautology::r#false,
            "not_not" => tautology::not_not,
            "and_pos" => tautology::and_pos,
            "and_neg" => tautology::and_neg,
            "or_pos" => tautology::or_pos,
            "or_neg" => tautology::or_neg,
            "xor_pos1" => tautology::xor_pos1,
            "xor_pos2" => tautology::xor_pos2,
            "xor_neg1" => tautology::xor_neg1,
            "xor_neg2" => tautology::xor_neg2,
            "implies_pos" => tautology::implies_pos,
            "implies_neg1" => tautology::implies_neg1,
            "implies_neg2" => tautology::implies_neg2,
            "equiv_pos1" => tautology::equiv_pos1,
            "equiv_pos2" => tautology::equiv_pos2,
            "equiv_neg1" => tautology::equiv_neg1,
            "equiv_neg2" => tautology::equiv_neg2,
            "ite_pos1" => tautology::ite_pos1,
            "ite_pos2" => tautology::ite_pos2,
            "ite_neg1" => tautology::ite_neg1,
            "ite_neg2" => tautology::ite_neg2,
            "eq_reflexive" => reflexivity::eq_reflexive,
            "eq_transitive" => transitivity::eq_transitive,
            "eq_congruent" => congruence::eq_congruent,
            "eq_congruent_pred" => congruence::eq_congruent_pred,
            "distinct_elim" => clausification::distinct_elim,
            "la_rw_eq" => linear_arithmetic::la_rw_eq,
            "la_generic" => linear_arithmetic::la_generic,
            "la_disequality" => linear_arithmetic::la_disequality,
            "la_totality" => linear_arithmetic::la_totality,
            "la_tautology" => linear_arithmetic::la_tautology,
            "forall_inst" => quantifier::forall_inst,
            "qnt_join" => quantifier::qnt_join,
            "qnt_rm_unused" => quantifier::qnt_rm_unused,
            "resolution" | "th_resolution" => resolution::resolution,
            "refl" if strict => reflexivity::strict_refl,
            "refl" => reflexivity::refl,
            "trans" => transitivity::trans,
            "cong" => congruence::cong,
            "ho_cong" => congruence::ho_cong,
            "and" => clausification::and,
            "tautology" => resolution::tautology,
            "not_or" => clausification::not_or,
            "or" => clausification::or,
            "not_and" => clausification::not_and,
            "xor1" => clausification::xor1,
            "xor2" => clausification::xor2,
            "not_xor1" => clausification::not_xor1,
            "not_xor2" => clausification::not_xor2,
            "implies" => clausification::implies,
            "not_implies1" => clausification::not_implies1,
            "not_implies2" => clausification::not_implies2,
            "equiv1" => tautology::equiv1,
            "equiv2" => tautology::equiv2,
            "not_equiv1" => tautology::not_equiv1,
            "not_equiv2" => tautology::not_equiv2,
            "ite1" => tautology::ite1,
            "ite2" => tautology::ite2,
            "not_ite1" => tautology::not_ite1,
            "not_ite2" => tautology::not_ite2,
            "ite_intro" => tautology::ite_intro,
            "contraction" => resolution::contraction,
            "connective_def" => tautology::connective_def,
            "ite_simplify" => simplification::ite_simplify,
            "eq_simplify" => simplification::eq_simplify,
            "and_simplify" => simplification::and_simplify,
            "or_simplify" => simplification::or_simplify,
            "not_simplify" => simplification::not_simplify,
            "implies_simplify" => simplification::implies_simplify,
            "equiv_simplify" => simplification::equiv_simplify,
            "bool_simplify" => simplification::bool_simplify,
            "qnt_simplify" => simplification::qnt_simplify,
            "div_simplify" => simplification::div_simplify,
            "prod_simplify" => simplification::prod_simplify,
            // Despite being separate rules in the specification, proofs generated by veriT don't
            // differentiate between `unary_minus_simplify` and `minus_simplify`. To account for
            // that, `simplification::minus_simplify` implements both rules in the same function.
            "unary_minus_simplify" | "minus_simplify" => simplification::minus_simplify,
            "sum_simplify" => simplification::sum_simplify,
            "comp_simplify" => simplification::comp_simplify,
            "nary_elim" => clausification::nary_elim,
            "ac_simp" => simplification::ac_simp,
            "bfun_elim" => clausification::bfun_elim,
            "bind" => subproof::bind,
            "qnt_cnf" => quantifier::qnt_cnf,
            "subproof" => subproof::subproof,
            "let" => subproof::r#let,
            "onepoint" => subproof::onepoint,
            "sko_ex" => subproof::sko_ex,
            "sko_forall" => subproof::sko_forall,
            "reordering" => extras::reordering,
            "symm" => extras::symm,
            "not_symm" => extras::not_symm,
            "eq_symmetric" => extras::eq_symmetric,
            "or_intro" => extras::or_intro,
            "bind_let" => extras::bind_let,
            "la_mult_pos" => extras::la_mult_pos,
            "la_mult_neg" => extras::la_mult_neg,

            // Special rules that always check as valid, and are used to indicate holes in the
            // proof.
            "hole" | "trust" => |_| Ok(()),

            // The Alethe specification does not yet describe how this more strict version of the
            // resolution rule will be called. Until that is decided and added to the specification,
            // we define a new specialized rule that calls it
            "strict_resolution" => resolution::strict_resolution,

            _ => return None,
        })
    }
}
