mod rules;

use crate::ast::*;
use rules::{Rule, RuleArgs};
use std::collections::HashMap;

#[derive(Debug)]
pub enum CheckerError<'a> {
    UnknownRule(&'a str),
    FailedOnRule(&'a str),
}

pub struct ProofChecker {
    pool: TermPool,
    skip_unknown_rules: bool,
    allow_test_rule: bool,
    context: Vec<HashMap<ByRefRc<Term>, ByRefRc<Term>>>,
}

impl ProofChecker {
    pub fn new(pool: TermPool, skip_unknown_rules: bool, allow_test_rule: bool) -> Self {
        ProofChecker {
            pool,
            skip_unknown_rules,
            allow_test_rule,
            context: Vec::new(),
        }
    }

    pub fn check<'a>(&mut self, proof: &'a Proof) -> Result<(), CheckerError<'a>> {
        self.check_subproof(&proof.0)
    }

    fn check_subproof<'a>(&mut self, commands: &'a [ProofCommand]) -> Result<(), CheckerError<'a>> {
        for step in commands {
            match step {
                ProofCommand::Step(step) => self.check_step(step, commands)?,
                ProofCommand::Subproof(commands, subproof_args) => {
                    let new_context = subproof_args
                        .iter()
                        .map(|(k, v)| {
                            let ident_term = terminal!(var k; self.pool.add_term(v.sort().clone()));
                            (self.pool.add_term(ident_term), v.clone())
                        })
                        .collect();
                    self.context.push(new_context);
                    self.check_subproof(&commands)?;
                    self.context.pop();
                }
                ProofCommand::Assume(_) => (),
            }
        }
        Ok(())
    }

    fn check_step<'a>(
        &mut self,
        ProofStep {
            clause,
            rule: rule_name,
            premises,
            args,
        }: &'a ProofStep,
        all_commands: &'a [ProofCommand],
    ) -> Result<(), CheckerError<'a>> {
        let rule = match Self::get_rule(rule_name, self.allow_test_rule) {
            Some(r) => r,
            None if self.skip_unknown_rules => return Ok(()),
            None => return Err(CheckerError::UnknownRule(rule_name)),
        };
        let premises = premises.iter().map(|&i| &all_commands[i]).collect();
        let rule_args = RuleArgs {
            conclusion: &clause,
            premises,
            args: &args,
            pool: &mut self.pool,
            context: &mut self.context,
            subproof_commands: all_commands,
        };
        if rule(rule_args).is_none() {
            return Err(CheckerError::FailedOnRule(rule_name));
        }
        Ok(())
    }

    pub fn get_rule(rule_name: &str, allow_test_rule: bool) -> Option<Rule> {
        use rules::*;
        Some(match rule_name {
            "true" => tautology::r#true,
            "false" => tautology::r#false,
            "not_not" => tautology::not_not,
            "and_pos" => tautology::and_pos,
            "and_neg" => tautology::and_neg,
            "or_pos" => tautology::or_pos,
            "or_neg" => tautology::or_neg,
            "equiv_pos1" => tautology::equiv_pos1,
            "equiv_pos2" => tautology::equiv_pos2,
            "eq_reflexive" => reflexivity::eq_reflexive,
            "eq_transitive" => transitivity::eq_transitive,
            "eq_congruent" => congruence::eq_congruent,
            "eq_congruent_pred" => congruence::eq_congruent_pred,
            "distinct_elim" => clausification::distinct_elim,
            "la_rw_eq" => linear_arithmetic::la_rw_eq,
            "la_generic" => linear_arithmetic::la_generic,
            "la_disequality" => linear_arithmetic::la_disequality,
            "forall_inst" => quantifier::forall_inst,
            "th_resolution" | "resolution" => resolution::resolution,
            "refl" => reflexivity::refl,
            "trans" => transitivity::trans,
            "cong" => congruence::cong,
            "and" => clausification::and,
            "tautology" => resolution::tautology,
            "or" => clausification::or,
            "implies" => clausification::implies,
            "ite1" => tautology::ite1,
            "ite2" => tautology::ite2,
            "ite_intro" => tautology::ite_intro,
            "contraction" => resolution::contraction,
            "connective_def" => tautology::connective_def,
            "eq_simplify" => simplification::eq_simplify,
            "or_simplify" => simplification::or_simplify,
            "not_simplify" => simplification::not_simplify,
            "equiv_simplify" => simplification::equiv_simplify,
            "bool_simplify" => simplification::bool_simplify,
            "prod_simplify" => simplification::prod_simplify,
            "nary_elim" => clausification::nary_elim,
            "ac_simp" => simplification::ac_simp,
            "bind" => subproof::bind,
            "let" => subproof::r#let,
            "trust_me" if allow_test_rule => |_| Some(()),
            _ => return None,
        })
    }
}
