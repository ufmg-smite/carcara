mod general_rules;
mod simplification_rules;
mod tests;

use crate::ast::*;

/// Converts a `bool` into an `Option<()>`.
fn to_option(b: bool) -> Option<()> {
    match b {
        true => Some(()),
        false => None,
    }
}

fn get_single_term_from_command(command: &ProofCommand) -> Option<&ByRefRc<Term>> {
    match command {
        ProofCommand::Assume(term) => Some(term),
        ProofCommand::Step { clause, .. } if clause.len() == 1 => Some(&clause[0]),
        _ => None,
    }
}

pub type Rule = fn(&[ByRefRc<Term>], Vec<&ProofCommand>, &[ProofArg]) -> Option<()>;

#[derive(Debug)]
pub enum CheckerError<'a> {
    UnknownRule(&'a str),
    FailedOnRule(&'a str),
}

pub struct ProofChecker {
    proof: Proof,
}

impl ProofChecker {
    pub fn new(proof: Proof) -> Self {
        ProofChecker { proof }
    }

    pub fn check(&self) -> Result<(), CheckerError> {
        for step in &self.proof.0 {
            if let ProofCommand::Step {
                clause,
                rule: rule_name,
                premises,
                args,
            } = step
            {
                let rule = Self::get_rule(rule_name).ok_or(CheckerError::UnknownRule(rule_name))?;
                let premises = premises.iter().map(|&i| &self.proof.0[i]).collect();
                if rule(&clause, premises, &args).is_none() {
                    return Err(CheckerError::FailedOnRule(rule_name));
                }
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
            "nary_elim" => general_rules::nary_elim,
            _ => return None,
        })
    }
}
