mod general_rules;
mod la_rules;
mod simplification_rules;
mod tests;

use std::collections::HashMap;

use crate::ast::*;

/// Converts a `bool` into an `Option<()>`.
fn to_option(b: bool) -> Option<()> {
    match b {
        true => Some(()),
        false => None,
    }
}

fn get_single_term_from_command(command: &ProofCommand) -> Option<&ByRefRc<Term>> {
    match get_clause_from_command(command) {
        [t] => Some(t),
        _ => None,
    }
}

fn get_clause_from_command(command: &ProofCommand) -> &[ByRefRc<Term>] {
    match command {
        // "assume" premises are interpreted as a clause with a single term
        ProofCommand::Assume(term) => std::slice::from_ref(term),
        ProofCommand::Step { clause, .. } => &clause,
        ProofCommand::Subproof(commands, _) => get_clause_from_command(commands.last().unwrap()),
    }
}

pub type Rule = fn(RuleArgs) -> Option<()>;

pub struct RuleArgs<'a> {
    conclusion: &'a [ByRefRc<Term>],
    premises: Vec<&'a ProofCommand>,
    args: &'a [ProofArg],
    pool: &'a mut TermPool,
    #[allow(dead_code)] // WIP
    context: &'a mut [HashMap<ByRefRc<Term>, ByRefRc<Term>>],
}

#[derive(Debug)]
pub enum CheckerError<'a> {
    UnknownRule(&'a str),
    FailedOnRule(&'a str),
}

pub struct ProofChecker {
    pool: TermPool,
    skip_unknown_rules: bool,
    context: Vec<HashMap<ByRefRc<Term>, ByRefRc<Term>>>,
}

impl ProofChecker {
    pub fn new(pool: TermPool, skip_unknown_rules: bool) -> Self {
        ProofChecker {
            pool,
            skip_unknown_rules,
            context: Vec::new(),
        }
    }

    pub fn check<'a>(&mut self, proof: &'a Proof) -> Result<(), CheckerError<'a>> {
        self.check_subproof(&proof.0)
    }

    fn check_subproof<'a>(&mut self, commands: &'a [ProofCommand]) -> Result<(), CheckerError<'a>> {
        for step in commands {
            match step {
                ProofCommand::Step {
                    clause,
                    rule: rule_name,
                    premises,
                    args,
                } => {
                    let rule = match Self::get_rule(rule_name) {
                        Some(r) => r,
                        None if self.skip_unknown_rules => continue,
                        None => return Err(CheckerError::UnknownRule(rule_name)),
                    };
                    let premises = premises.iter().map(|&i| &commands[i]).collect();
                    let rule_args = RuleArgs {
                        conclusion: &clause,
                        premises,
                        args: &args,
                        pool: &mut self.pool,
                        context: &mut self.context,
                    };
                    if rule(rule_args).is_none() {
                        return Err(CheckerError::FailedOnRule(rule_name));
                    }
                }
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

    pub fn get_rule(rule_name: &str) -> Option<Rule> {
        Some(match rule_name {
            "not_not" => general_rules::not_not,
            "and_pos" => general_rules::and_pos,
            "and_neg" => general_rules::and_neg,
            "or_pos" => general_rules::or_pos,
            "or_neg" => general_rules::or_neg,
            "equiv_pos1" => general_rules::equiv_pos1,
            "equiv_pos2" => general_rules::equiv_pos2,
            "eq_reflexive" => general_rules::eq_reflexive,
            "eq_transitive" => general_rules::eq_transitive,
            "eq_congruent" => general_rules::eq_congruent,
            "eq_congruent_pred" => general_rules::eq_congruent_pred,
            "distinct_elim" => general_rules::distinct_elim,
            "la_rw_eq" => la_rules::la_rw_eq,
            "la_generic" => la_rules::la_generic,
            "la_disequality" => la_rules::la_disequality,
            "forall_inst" => general_rules::forall_inst,
            "th_resolution" | "resolution" => general_rules::resolution,
            "cong" => general_rules::cong,
            "and" => general_rules::and,
            "or" => general_rules::or,
            "implies" => general_rules::implies,
            "ite1" => general_rules::ite1,
            "ite2" => general_rules::ite2,
            "ite_intro" => general_rules::ite_intro,
            "contraction" => general_rules::contraction,
            "bool_simplify" => simplification_rules::bool_simplify,
            "prod_simplify" => simplification_rules::prod_simplify,
            "nary_elim" => general_rules::nary_elim,
            _ => return None,
        })
    }
}
