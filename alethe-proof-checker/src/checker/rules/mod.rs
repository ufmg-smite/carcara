use super::Context;
use crate::ast::*;

#[derive(Debug)]
pub enum RuleError {
    Unspecified,
    UnknownRule,
}

pub type RuleResult = Result<(), RuleError>;

pub type Rule = fn(RuleArgs) -> RuleResult;

pub struct RuleArgs<'a> {
    pub(super) conclusion: &'a [Rc<Term>],
    pub(super) premises: Vec<&'a ProofCommand>,
    pub(super) args: &'a [ProofArg],
    pub(super) pool: &'a mut TermPool,
    pub(super) context: &'a [Context],

    // For rules that end a subproof, we need to pass all the commands of the subproof that it is
    // closing, because they may need to refer to some of them, and they are not given as premises.
    // If a rule is not ending a subproof, this should be `None`
    pub(super) subproof_commands: Option<&'a [ProofCommand]>,
}

/// Converts a `bool` into an `Option<()>`.
#[must_use]
fn to_option(b: bool) -> Option<()> {
    match b {
        true => Some(()),
        false => None,
    }
}

/// Converts a `bool` into an `RuleResult`.
fn to_result(b: bool, e: RuleError) -> RuleResult {
    match b {
        true => Ok(()),
        false => Err(e),
    }
}

fn get_single_term_from_command(command: &ProofCommand) -> Option<&Rc<Term>> {
    match get_clause_from_command(command) {
        [t] => Some(t),
        _ => None,
    }
}

fn get_clause_from_command(command: &ProofCommand) -> &[Rc<Term>] {
    match command {
        // "assume" premises are interpreted as a clause with a single term
        ProofCommand::Assume { index: _, term } => std::slice::from_ref(term),
        ProofCommand::Step(ProofStep { clause, .. }) => clause,
        ProofCommand::Subproof { commands, .. } => {
            get_clause_from_command(commands.last().unwrap())
        }
    }
}

/// Asserts that the argument is true, and returns `None` otherwise. `rassert!(arg)` is identical
/// to `to_option(arg)?`, but much more readable.
macro_rules! rassert {
    ($arg:expr) => {
        to_option($arg)?
    };
}

#[cfg(test)]
fn run_tests(test_name: &str, definitions: &str, cases: &[(&str, bool)]) {
    use crate::{
        checker::{Config, ProofChecker},
        parser::parse_instance,
    };
    use std::io::Cursor;

    for (i, (proof, expected)) in cases.iter().enumerate() {
        // This parses the definitions again for every case, which is not ideal
        let (parsed, pool) = parse_instance(Cursor::new(definitions), Cursor::new(proof))
            .unwrap_or_else(|e| panic!("parser error during test \"{}\": {}", test_name, e));
        let mut checker = ProofChecker::new(
            pool,
            Config {
                skip_unknown_rules: false,
                is_running_test: true,
                statistics: None,
            },
        );
        let got = matches!(checker.check(&parsed), Ok(()));
        assert_eq!(
            *expected, got,
            "test case \"{}\" index {} failed",
            test_name, i
        );
    }
}

#[cfg(test)]
macro_rules! test_cases {
    (
        definitions = $defs:expr,
        $($name:literal { $($proof:literal: $exp:literal,)* } )*
    ) => {{
        let definitions: &str = $defs;
        $({
            let name: &str = $name;
            let cases = [ $(($proof, $exp),)* ];
            crate::checker::rules::run_tests(name, definitions, &cases);
        })*
    }};
}

// Since the rule submodules use the `test_cases` macro, we have to declare them here, after the
// macro is declared
pub(super) mod clausification;
pub(super) mod congruence;
pub(super) mod extras;
pub(super) mod linear_arithmetic;
pub(super) mod quantifier;
pub(super) mod reflexivity;
pub(super) mod resolution;
pub(super) mod simplification;
pub(super) mod subproof;
pub(super) mod tautology;
pub(super) mod transitivity;
