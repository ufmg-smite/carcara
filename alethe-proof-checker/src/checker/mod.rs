mod context;
pub mod error;
pub mod reconstruction;
mod rules;

use crate::{ast::*, benchmarking::CollectResults, AletheResult, Error};
use ahash::AHashSet;
use context::*;
use error::CheckerError;
use reconstruction::Reconstructor;
use rules::{Premise, ReconstructionRule, Rule, RuleArgs, RuleResult};
use std::{
    fmt,
    time::{Duration, Instant},
};

pub struct CheckerStatistics<'s> {
    pub file_name: &'s str,
    pub reconstruction_time: &'s mut Duration,
    pub deep_eq_time: &'s mut Duration,
    pub assume_time: &'s mut Duration,
    pub results: &'s mut dyn CollectResults,
}

impl fmt::Debug for CheckerStatistics<'_> {
    // Since `self.results` does not implement `Debug`, we can't just `#[derive(Debug)]` and instead
    // have to implement it manually, removing that field.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CheckerStatistics")
            .field("file_name", &self.file_name)
            .field("reconstruction_time", &self.reconstruction_time)
            .field("deep_eq_time", &self.deep_eq_time)
            .field("assume_time", &self.assume_time)
            .finish()
    }
}

#[derive(Debug, Default)]
pub struct Config<'c> {
    pub skip_unknown_rules: bool,
    pub is_running_test: bool,
    pub statistics: Option<CheckerStatistics<'c>>,
}

pub struct ProofChecker<'c> {
    pool: &'c mut TermPool,
    config: Config<'c>,
    context: ContextStack,
    reconstructor: Option<Reconstructor>,
    reached_empty_clause: bool,
}

impl<'c> ProofChecker<'c> {
    pub fn new(pool: &'c mut TermPool, config: Config<'c>) -> Self {
        ProofChecker {
            pool,
            config,
            context: ContextStack::new(),
            reconstructor: None,
            reached_empty_clause: false,
        }
    }

    pub fn check(&mut self, proof: &Proof) -> AletheResult<()> {
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
                    self.check_step(step, previous_command, &iter)
                        .map_err(|e| Error::Checker {
                            inner: e,
                            rule: step.rule.clone(),
                            step: step.id.clone(),
                        })?;

                    // If this is the last command of a subproof, we have to pop the subproof
                    // commands off of the stack. The parser already ensures that the last command
                    // in a subproof is always a `step` command
                    if is_end_of_subproof {
                        self.context.pop();
                        if let Some(reconstructor) = &mut self.reconstructor {
                            reconstructor.close_subproof();
                        }
                    }

                    if step.clause.is_empty() {
                        self.reached_empty_clause = true;
                    }
                }
                ProofCommand::Subproof(s) => {
                    let time = Instant::now();
                    let step_id = command.id();

                    self.context
                        .push(self.pool, &s.assignment_args, &s.variable_args)
                        .map_err(|e| Error::Checker {
                            inner: e.into(),
                            rule: "anchor".into(),
                            step: step_id.to_owned(),
                        })?;

                    if let Some(reconstructor) = &mut self.reconstructor {
                        reconstructor.open_subproof(s.commands.len());
                    }

                    if let Some(stats) = &mut self.config.statistics {
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
                    self.check_assume(id, term, &proof.premises, &iter)?;
                }
            }
        }
        if self.config.is_running_test || self.reached_empty_clause {
            Ok(())
        } else {
            Err(Error::DoesNotReachEmptyClause)
        }
    }

    pub fn check_and_reconstruct(&mut self, mut proof: Proof) -> AletheResult<Proof> {
        self.reconstructor = Some(Reconstructor::new());
        let result = self.check(&proof);

        // We reset `self.reconstructor` before returning any errors encountered while checking so
        // we don't leave the checker in an invalid state
        let mut reconstructor = self.reconstructor.take().unwrap();
        result?;

        let reconstruction_time = Instant::now();
        proof.commands = reconstructor.end(proof.commands);
        if let Some(stats) = &mut self.config.statistics {
            *stats.reconstruction_time += reconstruction_time.elapsed();
        }
        Ok(proof)
    }

    fn check_assume(
        &mut self,
        id: &str,
        term: &Rc<Term>,
        premises: &AHashSet<Rc<Term>>,
        iter: &ProofIter,
    ) -> AletheResult<()> {
        let time = Instant::now();

        // Some subproofs contain `assume` commands inside them. These don't refer
        // to the original problem premises, so we ignore the `assume` command if
        // it is inside a subproof. Since the unit tests for the rules don't define the
        // original problem, but sometimes use `assume` commands, we also skip the
        // command if we are in a testing context.
        if self.config.is_running_test || iter.is_in_subproof() {
            if let Some(reconstructor) = &mut self.reconstructor {
                reconstructor.assume(term);
            }
            return Ok(());
        }

        if premises.contains(term) {
            if let Some(s) = &mut self.config.statistics {
                let time = time.elapsed();
                *s.assume_time += time;
                s.results
                    .add_assume_measurement(s.file_name, id, true, time);
            }
            if let Some(reconstructor) = &mut self.reconstructor {
                reconstructor.assume(term);
            }
            return Ok(());
        }

        let mut found = None;
        let mut deep_eq_time = Duration::ZERO;
        for p in premises {
            let (result, depth) = tracing_deep_eq(term, p, &mut deep_eq_time);
            if let Some(s) = &mut self.config.statistics {
                s.results.add_deep_eq_depth(depth);
            }
            if result {
                found = Some(p.clone());
                break;
            }
        }

        if let Some(s) = &mut self.config.statistics {
            let time = time.elapsed();
            *s.assume_time += time;
            *s.deep_eq_time += deep_eq_time;
            s.results
                .add_assume_measurement(s.file_name, id, false, time);
        }

        if found.is_some() {
            if let Some(reconstructor) = &mut self.reconstructor {
                reconstructor.assume(term);
            }
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
        iter: &'a ProofIter<'a>,
    ) -> RuleResult {
        let time = Instant::now();

        let rule = match Self::get_rule(&step.rule) {
            Some(r) => r,
            None if self.config.skip_unknown_rules => {
                if let Some(reconstructor) = &mut self.reconstructor {
                    reconstructor.unchanged(&step.clause);
                }
                return Ok(());
            }
            None => return Err(CheckerError::UnknownRule),
        };

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
        let mut deep_eq_time = Duration::ZERO;

        let rule_args = RuleArgs {
            conclusion: &step.clause,
            premises: &premises,
            args: &step.args,
            pool: self.pool,
            context: &mut self.context,
            previous_command,
            discharge: &discharge,
            deep_eq_time: &mut deep_eq_time,
        };

        if let Some(reconstructor) = &mut self.reconstructor {
            if let Some(reconstruction_rule) = Self::get_reconstruction_rule(&step.rule) {
                reconstruction_rule(rule_args, step.id.clone(), reconstructor)?;
            } else {
                rule(rule_args)?;
                reconstructor.unchanged(&step.clause);
            }
        } else {
            rule(rule_args)?;
        }

        if let Some(s) = &mut self.config.statistics {
            s.results
                .add_step_measurement(s.file_name, &step.id, &step.rule, time.elapsed());
            *s.deep_eq_time += deep_eq_time;
        }
        Ok(())
    }

    pub fn get_rule(rule_name: &str) -> Option<Rule> {
        use rules::*;

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
            "lia_generic" => linear_arithmetic::lia_generic,
            "la_disequality" => linear_arithmetic::la_disequality,
            "la_tautology" => linear_arithmetic::la_tautology,
            "forall_inst" => quantifier::forall_inst,
            "qnt_join" => quantifier::qnt_join,
            "qnt_rm_unused" => quantifier::qnt_rm_unused,
            "resolution" => resolution::resolution,
            "th_resolution" => resolution::th_resolution,
            "refl" => reflexivity::refl,
            "trans" => transitivity::trans,
            "cong" => congruence::cong,
            "ho_cong" => congruence::ho_cong,
            "and" => clausification::and,
            "tautology" => resolution::tautology,
            "not_or" => clausification::not_or,
            "or" => clausification::or,
            "not_and" => clausification::not_and,
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
            "minus_simplify" => simplification::minus_simplify,
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

            // Special rule that always checks as valid. It is mostly used in tests
            "trust" => |_| Ok(()),

            // The Alethe specification does not yet describe how this more strict version of the
            // resolution rule will be called. Until that is decided and added to the specification,
            // we define a new specialized rule that calls it
            "strict_resolution" => resolution::strict_resolution,

            _ => return None,
        })
    }

    fn get_reconstruction_rule(rule_name: &str) -> Option<ReconstructionRule> {
        use rules::*;

        Some(match rule_name {
            "eq_transitive" => transitivity::reconstruct_eq_transitive,
            "trans" => transitivity::reconstruct_trans,
            _ => return None,
        })
    }
}
