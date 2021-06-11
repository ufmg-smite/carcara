pub(super) mod clausification;
pub(super) mod congruence;
pub(super) mod linear_arithmetic;
pub(super) mod quantifier;
pub(super) mod reflexivity;
pub(super) mod resolution;
pub(super) mod simplification;
pub(super) mod subproof;
pub(super) mod tautology;
pub(super) mod transitivity;

use crate::ast::*;
use std::collections::HashMap;

pub type Rule = fn(RuleArgs) -> Option<()>;

pub struct RuleArgs<'a> {
    pub(super) conclusion: &'a [ByRefRc<Term>],
    pub(super) premises: Vec<&'a ProofCommand>,
    pub(super) args: &'a [ProofArg],
    pub(super) pool: &'a mut TermPool,
    pub(super) context: &'a mut [HashMap<ByRefRc<Term>, ByRefRc<Term>>],

    // For rules like "bind", that end a subproof, we need to pass all the commands of the subproof
    // that it is closing, because they may need to refer to some of them, and they are not given
    // as premises
    pub(super) subproof_commands: &'a [ProofCommand],
}

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
        ProofCommand::Step(ProofStep { clause, .. }) => &clause,
        ProofCommand::Subproof(commands, _) => get_clause_from_command(commands.last().unwrap()),
    }
}
