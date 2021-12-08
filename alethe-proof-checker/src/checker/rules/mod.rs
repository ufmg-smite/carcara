use super::{
    error::{CheckerError, EqualityError},
    Context,
};
use crate::{
    ast::*,
    utils::{Range, TypeName},
};

pub type RuleResult = Result<(), CheckerError>;

pub type Rule = fn(RuleArgs) -> RuleResult;

pub type ReconstructionRule = fn(RuleArgs, String, usize) -> Result<ProofCommand, CheckerError>;

pub struct RuleArgs<'a> {
    pub(super) conclusion: &'a [Rc<Term>],
    pub(super) premises: Vec<Premise<'a>>,
    pub(super) args: &'a [ProofArg],
    pub(super) pool: &'a mut TermPool,
    pub(super) context: &'a mut [Context],

    // For rules that end a subproof, we need to pass all the commands of the subproof that it is
    // closing, because they may need to refer to some of them, and they are not given as premises.
    // If a rule is not ending a subproof, this should be `None`
    pub(super) subproof_commands: Option<&'a [ProofCommand]>,
}

#[derive(Clone, Copy)]
pub struct Premise<'a> {
    pub command: &'a ProofCommand,
    pub premise_index: (usize, usize),
}

fn get_single_term_from_command(command: &ProofCommand) -> Option<&Rc<Term>> {
    match get_clause_from_command(command) {
        [t] => Some(t),
        _ => None,
    }
}

fn get_clause_from_command(command: &ProofCommand) -> &[Rc<Term>] {
    match command {
        // `assume` premises are interpreted as a clause with a single term
        ProofCommand::Assume { index: _, term } => std::slice::from_ref(term),
        ProofCommand::Step(ProofStep { clause, .. }) => clause,
        ProofCommand::Subproof { commands, .. } => {
            get_clause_from_command(commands.last().unwrap())
        }
    }
}

/// Helper function to get a single term from a premise, or return a `CheckerError::BadPremise`
/// error if it doesn't succeed.
fn get_premise_term(premise: Premise) -> Result<&Rc<Term>, CheckerError> {
    get_single_term_from_command(&premise.command)
        .ok_or_else(|| CheckerError::BadPremise(premise.command.index().to_string()))
}

/// Asserts that the argument is true, and returns `None` otherwise. `rassert!(arg)` is identical
/// to `to_option(arg)?`, but much more readable.
macro_rules! rassert {
    ($arg:expr) => {
        $crate::checker::rules::to_option($arg)?
    };
    ($arg:expr, $err:expr $(,)?) => {
        match $arg {
            true => Ok(()),
            false => Err($err),
        }?
    };
}

fn assert_num_premises<T: Into<Range>>(premises: &[Premise], range: T) -> RuleResult {
    let range = range.into();
    if !range.contains(premises.len()) {
        return Err(CheckerError::WrongNumberOfPremises(range, premises.len()));
    }
    Ok(())
}

fn assert_clause_len<T: Into<Range>>(clause: &[Rc<Term>], range: T) -> RuleResult {
    let range = range.into();
    if !range.contains(clause.len()) {
        return Err(CheckerError::WrongLengthOfClause(range, clause.len()));
    }
    Ok(())
}

fn assert_num_args<T: Into<Range>>(args: &[ProofArg], range: T) -> RuleResult {
    let range = range.into();
    if !range.contains(args.len()) {
        return Err(CheckerError::WrongNumberOfArgs(range, args.len()));
    }
    Ok(())
}

fn assert_num_steps_in_subproof<T: Into<Range>>(subproof: &[ProofCommand], range: T) -> RuleResult {
    let range = range.into();
    if !range.contains(subproof.len()) {
        return Err(CheckerError::WrongNumberOfStepsInSubproof(
            range,
            subproof.len(),
        ));
    }
    Ok(())
}

fn assert_operation_len<T: Into<Range>>(op: Operator, args: &[Rc<Term>], range: T) -> RuleResult {
    let range = range.into();
    if !range.contains(args.len()) {
        return Err(CheckerError::WrongNumberOfTermsInOp(op, range, args.len()));
    }
    Ok(())
}

fn assert_eq<T>(a: &T, b: &T) -> RuleResult
where
    T: Eq + Clone + TypeName,
    EqualityError<T>: Into<CheckerError>,
{
    if a != b {
        return Err(EqualityError::ExpectedEqual(a.clone(), b.clone()).into());
    }
    Ok(())
}

fn assert_is_expected<T>(got: &T, expected: T) -> RuleResult
where
    T: Eq + Clone + TypeName,
    EqualityError<T>: Into<CheckerError>,
{
    if *got != expected {
        return Err(EqualityError::ExpectedToBe { expected, got: got.clone() }.into());
    }
    Ok(())
}

fn assert_eq_modulo_reordering<T>(a: &T, b: &T) -> Result<(), CheckerError>
where
    T: Eq + Clone + TypeName + DeepEq,
    EqualityError<T>: Into<CheckerError>,
{
    if !deep_eq_modulo_reordering(a, b) {
        return Err(EqualityError::ExpectedEqual(a.clone(), b.clone()).into());
    }
    Ok(())
}

fn assert_is_expected_modulo_reordering<T>(got: &T, expected: T) -> RuleResult
where
    T: Eq + Clone + TypeName + DeepEq,
    EqualityError<T>: Into<CheckerError>,
{
    if !deep_eq_modulo_reordering(got, &expected) {
        return Err(EqualityError::ExpectedToBe { expected, got: got.clone() }.into());
    }
    Ok(())
}

fn assert_is_bool_constant(got: &Rc<Term>, expected: bool) -> RuleResult {
    if !got.is_bool_constant(expected) {
        return Err(CheckerError::ExpectedBoolConstant(expected, got.clone()));
    }
    Ok(())
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
        let (parsed, mut pool) = parse_instance(Cursor::new(definitions), Cursor::new(proof))
            .unwrap_or_else(|e| panic!("parser error during test \"{}\": {}", test_name, e));
        let mut checker = ProofChecker::new(
            &mut pool,
            Config {
                skip_unknown_rules: false,
                is_running_test: true,
                statistics: None,
                builder: None,
            },
        );
        let got = checker.check(&parsed).is_ok();
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
            $crate::checker::rules::run_tests(name, definitions, &cases);
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
