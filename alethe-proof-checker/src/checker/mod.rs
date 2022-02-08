pub mod error;
pub mod reconstruction;
mod rules;

use crate::{
    ast::*,
    benchmarking::{Metrics, StepId},
    AletheResult, Error,
};
use ahash::{AHashMap, AHashSet};
use error::CheckerError;
use reconstruction::Reconstructor;
use rules::{Premise, ReconstructionRule, Rule, RuleArgs, RuleResult};
use std::time::{Duration, Instant};

struct Context {
    substitution: Substitution,
    substitution_until_fixed_point: Substitution,
    cumulative_substitution: Substitution,
    bindings: AHashSet<SortedVar>,
}

#[derive(Debug)]
pub struct CheckerStatistics<'s> {
    pub file_name: &'s str,
    pub checking_time: &'s mut Duration,
    pub reconstructing_time: &'s mut Duration,
    pub step_time: &'s mut Metrics<StepId>,
    pub step_time_by_file: &'s mut AHashMap<String, Metrics<StepId>>,
    pub step_time_by_rule: &'s mut AHashMap<String, Metrics<StepId>>,
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
    context: Vec<Context>,
    reconstructor: Option<Reconstructor>,
}

impl<'c> ProofChecker<'c> {
    pub fn new(pool: &'c mut TermPool, config: Config<'c>) -> Self {
        ProofChecker {
            pool,
            config,
            context: Vec::new(),
            reconstructor: None,
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
                    // other commands in the subproof
                    let subproof_commands =
                        is_end_of_subproof.then(|| iter.current_subproof().unwrap());
                    self.check_step(step, subproof_commands, &iter)
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
                }
                ProofCommand::Subproof(s) => {
                    let time = Instant::now();
                    let step_id = command.id();

                    let new_context = self
                        .build_context(&s.assignment_args, &s.variable_args)
                        .map_err(|e| Error::Checker {
                            inner: e.into(),
                            rule: "anchor".into(),
                            step: step_id.to_owned(),
                        })?;
                    self.context.push(new_context);

                    if let Some(reconstructor) = &mut self.reconstructor {
                        reconstructor.open_subproof(s.commands.len());
                    }

                    self.add_statistics_measurement(step_id, "anchor*", time);
                }
                ProofCommand::Assume { id, term } => {
                    let time = Instant::now();

                    // Some subproofs contain `assume` commands inside them. These don't refer
                    // to the original problem premises, so we ignore the `assume` command if
                    // it is inside a subproof. Since the unit tests for the rules don't define the
                    // original problem, but sometimes use `assume` commands, we also skip the
                    // command if we are in a testing context.
                    if !self.config.is_running_test && !iter.is_in_subproof() {
                        let is_valid = proof.premises.contains(term)
                            || proof
                                .premises
                                .iter()
                                .any(|u| deep_eq_modulo_reordering(term, u));
                        if !is_valid {
                            return Err(Error::Checker {
                                inner: CheckerError::Assume(term.clone()),
                                rule: "assume".into(),
                                step: id.clone(),
                            });
                        }
                    };

                    if let Some(reconstructor) = &mut self.reconstructor {
                        reconstructor.assume(term);
                    }
                    self.add_statistics_measurement(id, "assume*", time);
                }
            }
        }
        Ok(())
    }

    pub fn check_and_reconstruct(&mut self, mut proof: Proof) -> AletheResult<Proof> {
        self.reconstructor = Some(Reconstructor::new());
        let result = self.check(&proof);

        // We reset `self.reconstructor` before returning any errors encountered while checking so
        // we don't leave the checker in an invalid state
        let mut reconstructor = self.reconstructor.take().unwrap();
        result?;

        let reconstructing_time = Instant::now();
        proof.commands = reconstructor.end(proof.commands);
        if let Some(stats) = &mut self.config.statistics {
            *stats.reconstructing_time += reconstructing_time.elapsed();
        }
        Ok(proof)
    }

    fn check_step<'a>(
        &mut self,
        step: &'a ProofStep,
        subproof_commands: Option<&'a [ProofCommand]>,
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

        let rule_args = RuleArgs {
            conclusion: &step.clause,
            premises: &premises,
            args: &step.args,
            pool: self.pool,
            context: &mut self.context,
            subproof_commands,
            discharge: &discharge,
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
        self.add_statistics_measurement(&step.id, &step.rule, time);
        Ok(())
    }

    fn build_context(
        &mut self,
        assignment_args: &[(String, Rc<Term>)],
        variable_args: &[SortedVar],
    ) -> Result<Context, SubstitutionError> {
        // Since some rules (like `refl`) need to apply substitutions until a fixed point, we
        // precompute these substitutions into a separate hash map. This assumes that the assignment
        // arguments are in the correct order.
        let mut substitution = Substitution::empty();
        let mut substitution_until_fixed_point = Substitution::empty();

        // We build the `substitution_until_fixed_point` hash map from the bottom up, by using the
        // substitutions already introduced to transform the result of a new substitution before
        // inserting it into the hash map. So for instance, if the substitutions are `(:= y z)` and
        // `(:= x (f y))`, we insert the first substitution, and then, when introducing the second,
        // we use the current state of the hash map to transform `(f y)` into `(f z)`. The
        // resulting hash map will then contain `(:= y z)` and `(:= x (f z))`
        for (var, value) in assignment_args.iter() {
            let sort = Term::Sort(self.pool.sort(value).clone());
            let var_term = terminal!(var var; self.pool.add_term(sort));
            let var_term = self.pool.add_term(var_term);
            substitution.insert(self.pool, var_term.clone(), value.clone())?;
            let new_value = substitution_until_fixed_point.apply(&mut self.pool, value)?;
            substitution_until_fixed_point.insert(self.pool, var_term, new_value)?;
        }

        // Some rules (notably `refl`) need to apply the substitutions introduced by all the
        // previous contexts instead of just the current one. Instead of doing this iteratively
        // everytime the rule is used, we precompute the cumulative substitutions of this context
        // and all the previous ones and store that in a hash map. This improves the performance of
        // these rules considerably
        let mut cumulative_substitution = substitution_until_fixed_point.map.clone();
        if let Some(previous_context) = self.context.last() {
            for (k, v) in previous_context.cumulative_substitution.map.iter() {
                let value = match substitution_until_fixed_point.map.get(v) {
                    Some(new_value) => new_value,
                    None => v,
                };
                cumulative_substitution.insert(k.clone(), value.clone());
            }
        }
        let cumulative_substitution = Substitution::new(self.pool, cumulative_substitution)?;

        let bindings = variable_args.iter().cloned().collect();
        Ok(Context {
            substitution,
            substitution_until_fixed_point,
            cumulative_substitution,
            bindings,
        })
    }

    fn add_statistics_measurement(&mut self, step_id: &str, rule: &str, start_time: Instant) {
        if let Some(stats) = &mut self.config.statistics {
            let measurement = start_time.elapsed();
            let file_name = stats.file_name.to_owned();
            let rule = rule.to_owned();
            let id = StepId {
                file: file_name.clone().into_boxed_str(),
                step_id: step_id.into(),
                rule: rule.clone().into_boxed_str(),
            };
            stats.step_time.add(&id, measurement);
            stats
                .step_time_by_file
                .entry(file_name)
                .or_default()
                .add(&id, measurement);
            stats
                .step_time_by_rule
                .entry(rule)
                .or_default()
                .add(&id, measurement);
            *stats.checking_time += measurement;
        }
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
            "th_resolution" | "resolution" => resolution::resolution,
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
