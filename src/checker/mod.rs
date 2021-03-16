use std::rc::Rc;

use crate::parser::ast::*;

pub type Rule = fn(&[Rc<Term>], Vec<&ProofCommand>, &[ProofArg]) -> bool;

pub struct ProofChecker {
    proof: Proof,
}

impl ProofChecker {
    pub fn new(proof: Proof) -> Self {
        ProofChecker { proof }
    }

    pub fn check(self) -> bool {
        for step in &self.proof.0 {
            if let ProofCommand::Step {
                clause,
                rule,
                premises,
                args,
            } = step
            {
                let rule = Self::get_rule(rule);
                let premises = premises.iter().map(|&i| &self.proof.0[i]).collect();
                if !rule(&clause, premises, &args) {
                    return false;
                }
            }
        }
        true
    }

    fn get_rule(rule_name: &str) -> Rule {
        match rule_name {
            "or" => or_rule,
            _ => todo!(),
        }
    }
}

fn or_rule(clause: &[Rc<Term>], premises: Vec<&ProofCommand>, _: &[ProofArg]) -> bool {
    if premises.len() != 1 {
        return false;
    }
    let or_term = match premises[0] {
        ProofCommand::Assume(cl) => cl,
        ProofCommand::Step { clause, .. } => {
            if clause.len() == 1 {
                &clause[0]
            } else {
                return false;
            }
        }
    };
    let or_contents = if let Term::Op(Operator::Or, args) = or_term.as_ref() {
        args
    } else {
        return false;
    };

    or_contents == clause
}
