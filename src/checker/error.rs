//! Errors produced while checking a proof.
use crate::{
    ast::*,
    automata::Trigger,
    external::ExternalError,
    utils::{Range, TypeName},
};
use rug::{Integer, Rational};
use std::{fmt, path::Path};
use thiserror::Error;

/// Constructs an ad-hoc checker error given a format string and arguments.
macro_rules! err {
    ($($arg:tt)*) => {
        Err(crate::checker::error::CheckerError::Explanation(format!($($arg)*)))
    };
}

/// Asserts that the first argument is true, and returns the error specified by the second argument
/// otherwise. If the second argument is a format string, the error is `err!` with the formatted
/// message.
macro_rules! rassert {
    ($arg:expr, $fmt:literal $(, $args:expr)* $(,)?) => {
        match $arg {
            true => Ok(()),
            false => crate::checker::error::err!($fmt $(, $args)*),
        }?
    };
    ($arg:expr, $err:expr $(,)?) => {
        match $arg {
            true => Ok(()),
            false => Err($err),
        }?
    };
}

pub(crate) use err;
pub(crate) use rassert;

/// An error that occurred while checking a proof.
#[derive(Debug, Error)]
pub enum CheckerError {
    /// An unspecified error.
    #[error("unspecified error")]
    Unspecified,

    /// An unspecified error, with an explanation message.
    #[error("{0}")]
    Explanation(String),

    /// An error when applying a [`Substitution`].
    #[error(transparent)]
    Substitution(#[from] SubstitutionError),

    /// An assumption did not correspond to any of the original problem's premises.
    #[error("could not match term to any of the original problem premises: {0}")]
    Assume(Rc<Term>),

    /// A binding was not introduced in the context.
    #[error("binding '{0}' was not introduced in context")]
    BindingIsNotInContext(String),

    // Rule specific errors
    /// An error in the `resolution` and related rules.
    #[error(transparent)]
    Resolution(#[from] crate::resolution::ResolutionError),

    /// An error in the `drup` rule.
    #[error(transparent)]
    DrupFormatError(#[from] crate::drup::DrupFormatError),

    /// An error in the congruence rules.
    #[error(transparent)]
    Cong(#[from] CongruenceError),

    /// An error in a rule dealing with quantifiers.
    #[error(transparent)]
    Quant(#[from] QuantifierError),

    /// An error when using an external tool.
    #[error(transparent)]
    External(#[from] ExternalError),

    #[error(transparent)]
    String(#[from] Box<StringError>),

    /// A reflexivity rule failed for the given terms.
    #[error("reflexivity failed with terms '{0}' and '{1}'")]
    ReflexivityFailed(Rc<Term>, Rc<Term>),

    /// Simplifying a term resulted in a term different from the target.
    #[error("simplifying '{original}' resulted in '{result}', expected result to be '{target}'")]
    SimplificationFailed {
        /// The original term being simplified.
        original: Rc<Term>,

        /// The actual result of the simplification.
        result: Rc<Term>,

        /// The expected result of the simplification.
        target: Rc<Term>,
    },

    /// A cycle was encountered while simplifying a term.
    #[error("encountered cycle when simplifying term: '{0}'")]
    CycleInSimplification(Rc<Term>),

    /// The premises of a transitivity rule do not connect the two terms of the conclusion.
    #[error("broken transitivity chain: can't prove '(= {0} {1})'")]
    BrokenTransitivityChain(Rc<Term>, Rc<Term>),

    /// A term present in the premise of a `contraction` step is missing from the conclusion clause.
    #[error("term '{0}' is missing in conclusion clause")]
    ContractionMissingTerm(Rc<Term>),

    /// A term present in the conclusion of a `contraction` step is missing from the premise clause.
    #[error("term '{0}' was not expected in conclusion clause")]
    ContractionExtraTerm(Rc<Term>),

    /// A term is not a valid n-ary operation.
    #[error("term '{0}' is not a valid n-ary operation")]
    NotValidNaryTerm(Rc<Term>),

    /// The length of a term could not be statically determined.
    #[error("cannot evaluate the fixed length of the term '{0}'")]
    LengthCannotBeEvaluated(Rc<Term>),

    /// A term does not have the given i-th child.
    #[error("No {0}-th child in term {1}")]
    NoIthChildInTerm(usize, Rc<Term>),

    /// The argument multisets of a `shuffle` step are not equal.
    #[error("argument multisets are not equal")]
    ShuffleArgsNotEqual,

    /// A term was expected to be a comparison operation (such as `<`, `<=`, `>`, or `>=`), but was
    /// not.
    #[error("expected comparison operation, got: '{0}'")]
    ExpectedComparisonOp(Rc<Term>),

    /// The operator in a `la_mult_pos` or `la_mult_neg` step is not a comparison operator.
    #[error("'{0}' is not a comparison operator")]
    InvalidComparisonOperator(Operator),

    // General errors
    /// A rule received the wrong number of premises.
    #[error("expected {0} premises, got {1}")]
    WrongNumberOfPremises(Range, usize),

    /// The conclusion clause had the wrong length.
    #[error("expected {0} terms in clause, got {1}")]
    WrongLengthOfClause(Range, usize),

    /// A rule received the wrong number of arguments.
    #[error("expected {0} arguments, got {1}")]
    WrongNumberOfArgs(Range, usize),

    /// An operation term contained the wrong number of terms.
    #[error("expected {1} terms in '{0}' term, got {2}")]
    WrongNumberOfTermsInOp(Operator, Range, usize),

    /// The conclusion clause of a premise had the wrong length.
    #[error("expected {1} terms in clause of step '{0}', got {2}")]
    WrongLengthOfPremiseClause(String, Range, usize),

    /// A term is not of the expected form.
    #[error("term '{1}' is of the wrong form, expected '{0}'")]
    TermOfWrongForm(&'static str, Rc<Term>),

    /// A term was expected to be a specific boolean constant.
    #[error("expected term '{0}' to be boolean constant '{1}'")]
    ExpectedBoolConstant(bool, Rc<Term>),

    /// A term was expected to be a boolean constant.
    #[error("expected term '{0}' to be a boolean constant")]
    ExpectedAnyBoolConstant(Rc<Term>),

    /// A term was expected to be a string constant of length one.
    #[error("expected term '{0}' to be a string constant of length one")]
    ExpectedStringConstantOfLengthOne(Rc<Term>),

    /// A term was expected to be a specific numeric constant.
    #[error("expected term '{}' to be numerical constant {:?}", .1, .0.to_f64())]
    ExpectedNumber(Rational, Rc<Term>),

    /// A term was expected to be a specific integer constant.
    #[error("expected term '{}' to be integer constant {:?}", .1, .0.to_i32())]
    ExpectedInteger(Integer, Rc<Term>),

    /// A term was expected to be a numeric constant.
    #[error("expected term '{0}' to be a numerical constant")]
    ExpectedAnyNumber(Rc<Term>),

    /// A term was expected to be an integer constant.
    #[error("expected term '{0}' to be an integer constant")]
    ExpectedAnyInteger(Rc<Term>),

    /// A term was expected to be a non-negative integer constant.
    #[error("expected term '{0}' to be an non-negative integer constant")]
    ExpectedNonnegInteger(Rc<Term>),

    /// A term was expected to be a bitvector constant.
    #[error("expected term '{0}' to be a bitvector constant")]
    ExpectedBitvector(Rc<Term>),

    /// A term was expected to be an operation term.
    #[error("expected operation term, got '{0}'")]
    ExpectedOperationTerm(Rc<Term>),

    /// A term was expected to be a quantifier term (a `forall` or `exists` term).
    #[error("expected quantifier term, got '{0}'")]
    ExpectedQuantifierTerm(Rc<Term>),

    /// A term was expected to be a binder term (a `forall`, `exists`, `choice`, or `lambda` term).
    #[error("expected binder term, got '{0}'")]
    ExpectedBinderTerm(Rc<Term>),

    /// A term was expected to be a `let` term.
    #[error("expected 'let' term, got '{0}'")]
    ExpectedLetTerm(Rc<Term>),

    /// The first term was expected to be a prefix of the second.
    #[error("expected term {0} to be a prefix of {1}")]
    ExpectedToBePrefix(Rc<Term>, Rc<Term>),

    /// The first term was expected to be a suffix of the second.
    #[error("expected term {0} to be a suffix of {1}")]
    ExpectedToBeSuffix(Rc<Term>, Rc<Term>),

    /// A string term was expected to not be empty.
    #[error("expected term {0} to not be empty")]
    ExpectedToNotBeEmpty(Rc<Term>),

    /// A subproof closing rule was used in a step that is not the last step of a subproof.
    #[error("this rule can only be used in the last step of a subproof")]
    MustBeLastStepInSubproof,

    /// A division or modulo operation was performed with a zero divisor.
    #[error("division or modulo by zero")]
    DivOrModByZero,

    // Equality errors
    /// Two terms were expected to be equal.
    #[error(transparent)]
    TermEquality(#[from] EqualityError<Rc<Term>>),

    /// Two sorts were expected to be equal.
    #[error(transparent)]
    SortEquality(#[from] EqualityError<Rc<Sort>>),

    /// Two quantifiers were expected to be equal.
    #[error(transparent)]
    QuantifierEquality(#[from] EqualityError<Binder>),

    /// Two binding lists were expected to be equal.
    #[error(transparent)]
    BindingListEquality(#[from] EqualityError<BindingList>),

    /// Two value binding lists were expected to be equal.
    #[error(transparent)]
    BindingValueListEquality(#[from] EqualityError<BindingList<Rc<Term>>>),

    /// Two integers were expected to be equal.
    #[error(transparent)]
    IntegerEquality(#[from] EqualityError<Integer>),

    // Rare Rules Error
    /// A `rare` rule was not specified in the step's arguments.
    #[error("expected a rare rule specified in the arguments")]
    RareNotSpecifiedRule,

    /// The argument given as a `rare` rule was not a string constant.
    #[error("expected a rare rule specified in the arguments, but found {0}")]
    RareRuleExpectedLiteral(Rc<Term>),

    /// A `rare` rule with the given name was not found.
    #[error("the rule {0} was not found")]
    RareRuleNotFound(String),

    /// A `rare` rule received an unexpected number of premises.
    #[error("expected {0} number of premises, maybe you applied more arguments than needed")]
    RareNumberOfPremisesWrong(usize),

    /// A premise of a step is not equal to the corresponding premise of the `rare` rule.
    #[error("the premise {0} isn't equal to {1}")]
    RarePremiseAreNotEqual(Rc<Term>, Rc<Term>),

    /// The conclusion of a step is not equal to the conclusion of the `rare` rule.
    #[error("the conclusion {0} isn't equal to {1}")]
    RareConclusionAreNotEqual(Rc<Term>, Rc<Term>),

    /// The conclusion of a `rare` rule should contain exactly one term.
    #[error("the conclusion of a rare rule should be exactly 1")]
    RareConclusionNumberInvalid,

    /// An unknown rule was encountered.
    #[error("unknown rule")]
    UnknownRule,
}

impl CheckerError {
    pub fn at(self, id: &str, rule: &str, file: &Path) -> crate::Error {
        crate::Error::Checker {
            inner: Box::new(self),
            rule: rule.into(),
            step: id.into(),
            file: file.to_path_buf(),
        }
    }
}

/// Errors in which we expected two things to be equal but they weren't.
#[derive(Debug, Error)]
pub enum EqualityError<T: TypeName> {
    /// The two values were expected to be equal.
    ///
    /// This implies no preference to either value.
    #[error("expected {}s to be equal: '{}' and '{}'", T::NAME, .0, .1)]
    ExpectedEqual(T, T),

    /// We expected a specific value, but got another.
    ///
    /// This gives preference to `expected` being the 'correct' value.
    #[error("expected {} '{got}' to be '{expected}'", T::NAME)]
    ExpectedToBe {
        /// The expected value.
        expected: T,
        /// The value that was actually found.
        got: T,
    },
}

struct DisplayIndexedOp<'a>(&'a ParamOperator, &'a Vec<Rc<Term>>);

impl fmt::Display for DisplayIndexedOp<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "(_ {}", self.0)?;
        for a in self.1 {
            write!(f, " {}", a)?;
        }
        write!(f, ")")
    }
}

/// Errors in the congruence rules.
#[derive(Debug, Error)]
pub enum CongruenceError {
    /// The rule was given more premises than argument pairs to justify.
    #[error("too many premises")]
    TooManyPremises,

    /// There is no premise justifying the equality of the two arguments.
    #[error("no premise to justify equality of arguments '{0}' and '{1}'")]
    MissingPremise(Rc<Term>, Rc<Term>),

    /// The given premise does not justify the equality of the given arguments.
    #[error(
        "premise '(= {} {})' doesn't justify conclusion arguments '{}' and '{}'",
        .premise.0, .premise.1, .args.0, .args.1
    )]
    PremiseDoesntJustifyArgs {
        /// The arguments of the conclusion.
        args: (Rc<Term>, Rc<Term>),

        /// The premise that should justify their equality.
        premise: (Rc<Term>, Rc<Term>),
    },

    /// The functions of the two terms do not match.
    #[error("functions don't match: '{0}' and '{1}'")]
    DifferentFunctions(Rc<Term>, Rc<Term>),

    /// The operators of the two terms do not match.
    #[error("operators don't match: '{0}' and '{1}'")]
    DifferentOperators(Operator, Operator),

    /// The two terms have different numbers of arguments.
    #[error("different numbers of arguments: {0} and {1}")]
    DifferentNumberOfArguments(usize, usize),

    /// A term is not an application or operation, so congruence cannot be applied to it.
    #[error("term is not an application or operation: '{0}'")]
    NotApplicationOrOperation(Rc<Term>),

    /// The indexed operators of the two terms do not match.
    #[error(
        "indexed operators don't match: '{}' and '{}'",
        DisplayIndexedOp(&(.0).0, &(.0).1), DisplayIndexedOp(&(.1).0, &(.1).1)
    )]
    DifferentIndexedOperators(
        (ParamOperator, Vec<Rc<Term>>),
        (ParamOperator, Vec<Rc<Term>>),
    ),

    /// The qualified operators of the two terms do not match.
    #[error(
        "qualified operators don't match: '(as {} {})' and '(as {} {})'",
        (.0).0, (.0).1, (.1).0, (.1).1)
    ]
    DifferentQualifiedOperators((QualifiedOperator, Rc<Sort>), (QualifiedOperator, Rc<Sort>)),
}

/// Errors relevant to the rules dealing with quantifiers.
#[derive(Debug, Error)]
pub enum QuantifierError {
    /// A binding introduced on the right-hand side was not present on the left-hand side.
    #[error("unknown binding introduced in right-hand side: '{0}'")]
    NewBindingIntroduced(String),

    /// A binding from the left-hand side that is still used is missing from the right-hand side.
    #[error("binding is missing in right-hand side: '{0}'")]
    BindingIsMissing(String),

    /// A bound variable appears as a free variable in the term.
    #[error("binding '{0}' appears as free variable in term '{1}'")]
    MiniscopeFreeVar(String, Rc<Term>),
}

/// Errors relevant to all String rules (CPC and RCP calculus).
#[derive(Debug, Error)]
pub enum StringError {
    #[error("expected two ranges to calculate the intersection between then, got '{0}' and '{1}'")]
    ExpectedRangesToCalculateTheIntersection(Trigger, Trigger),

    #[error("expected a string constant inside the str.to_re operator, got '{0}'")]
    ExpectedStringConstantInsideStrToRe(Rc<Term>),

    #[error("unexpected term when converting '{0}' to his automaton form")]
    UnexpectedTermOnAutomatonConversion(Rc<Term>),

    #[error("regular expression match failed: expected '{s}' in '{regex}' to be {expected}")]
    RegexMatchFailed {
        s: String,
        regex: Rc<Term>,
        expected: bool,
    },

    #[error(
        "regular expression replace failed: replacing in '{s}' with regex '{regex}' and replacement '{replacement}' expected to result in '{expected}', got '{got}'"
    )]
    RegexReplaceFailed {
        s: String,
        regex: Rc<Term>,
        replacement: String,
        expected: String,
        got: String,
    },
}

impl From<StringError> for CheckerError {
    fn from(e: StringError) -> Self {
        CheckerError::String(Box::new(e))
    }
}
