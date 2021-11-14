use crate::{ast::*, utils::Range};
use std::fmt;

#[derive(Debug)]
pub enum CheckerError {
    Unspecified,

    // Rule specific errors
    Cong(CongruenceError),
    ReflexivityFailed(Rc<Term>, Rc<Term>),
    SimplificationFailed {
        original: Rc<Term>,
        result: Rc<Term>,
        target: Rc<Term>,
    },
    CycleInSimplification(Rc<Term>),
    TermIsNotConnective(Rc<Term>),
    IsNotIteSubterm(Rc<Term>),
    BrokenTransitivityChain(Rc<Term>, Rc<Term>),

    // General errors
    WrongNumberOfPremises(Range, usize),
    WrongLengthOfClause(Range, usize),
    WrongNumberOfTermsInOp(Operator, Range, usize),
    TermDoesntApperInOp(Operator, Rc<Term>),
    BadPremise(String), // TODO: This error is too general
    TermOfWrongForm(&'static str, Rc<Term>),
    TermsNotEqual(Rc<Term>, Rc<Term>),
    ExpectedTermToBe {
        // This error is very similar to `TermsNotEqual`, but the error message implies that a
        // specific term was expected
        expected: Rc<Term>,
        got: Rc<Term>,
    },
    BindingsNotEqual,
    ExpectedBoolConstant(bool, Rc<Term>),

    UnknownRule,
}

impl fmt::Display for CheckerError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            CheckerError::Unspecified => write!(f, "unspecified error"),
            CheckerError::Cong(e) => write!(f, "{}", e),
            CheckerError::ReflexivityFailed(a, b) => {
                write!(f, "reflexivity failed with terms '{}' and '{}'", a, b)
            }
            CheckerError::SimplificationFailed { original, result, target } => {
                write!(
                    f,
                    "simplifying '{}' resulted in '{}', expected result to be '{}'",
                    original, result, target
                )
            }
            CheckerError::CycleInSimplification(t) => {
                write!(f, "encountered cycle when simplifying term: '{}'", t)
            }
            CheckerError::TermIsNotConnective(t) => write!(f, "term '{}' is not a connective", t),
            CheckerError::IsNotIteSubterm(t) => {
                write!(
                    f,
                    "term '{}' does not appear as a subterm of the root term",
                    t
                )
            }
            CheckerError::BrokenTransitivityChain(stopped, target) => {
                write!(
                    f,
                    "broken transitivity chain: can't prove '(= {} {})'",
                    stopped, target
                )
            }
            CheckerError::WrongNumberOfPremises(expected, got) => {
                write!(f, "expected {} premises, got {}", expected.to_text(), got)
            }
            CheckerError::WrongLengthOfClause(expected, got) => {
                write!(
                    f,
                    "expected {} terms in clause, got {}",
                    expected.to_text(),
                    got
                )
            }
            CheckerError::WrongNumberOfTermsInOp(op, expected, got) => {
                write!(
                    f,
                    "expected {} terms in '{}' term, got {}",
                    expected.to_text(),
                    op,
                    got
                )
            }
            CheckerError::TermDoesntApperInOp(op, t) => {
                write!(f, "expected term '{}' to appear in '{}' term", t, op)
            }
            CheckerError::BadPremise(p) => write!(f, "bad premise: '{}'", p),
            CheckerError::TermOfWrongForm(pat, term) => {
                write!(
                    f,
                    "term '{}' is of the wrong form, expected '{}'",
                    term, pat
                )
            }
            CheckerError::TermsNotEqual(a, b) => {
                write!(f, "expected terms to be equal: '{}' and '{}'", a, b)
            }
            CheckerError::ExpectedTermToBe { expected, got } => {
                write!(f, "expected term '{}' to be '{}'", got, expected)
            }
            CheckerError::BindingsNotEqual => write!(f, "quantifier bindings are not equal"),
            CheckerError::ExpectedBoolConstant(b, t) => {
                write!(f, "expected term '{}' to be boolean constant '{}'", t, b)
            }
            CheckerError::UnknownRule => write!(f, "unknown rule"),
        }
    }
}

impl From<CongruenceError> for CheckerError {
    fn from(e: CongruenceError) -> Self {
        Self::Cong(e)
    }
}

#[derive(Debug)]
pub enum CongruenceError {
    TooManyPremises,
    MissingPremise(Rc<Term>, Rc<Term>),
    PremiseDoesntJustifyArgs {
        args: (Rc<Term>, Rc<Term>),
        premise: (Rc<Term>, Rc<Term>),
    },
    DifferentFunctions(Rc<Term>, Rc<Term>),
    DifferentOperators(Operator, Operator),
    DifferentNumberOfArguments(usize, usize),
    NotApplicationOrOperation(Rc<Term>),
}

impl fmt::Display for CongruenceError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            CongruenceError::TooManyPremises => write!(f, "too many premises"),
            CongruenceError::MissingPremise(a, b) => write!(
                f,
                "no premise to justify equality of arguments '{}' and '{}'",
                a, b
            ),
            CongruenceError::PremiseDoesntJustifyArgs { args, premise } => write!(
                f,
                "premise '(= {} {})' doesn't justify conclusion arguments '{}' and '{}'",
                premise.0, premise.1, args.0, args.1
            ),
            CongruenceError::DifferentFunctions(a, b) => {
                write!(f, "functions don't match: '{}' and '{}'", a, b)
            }
            CongruenceError::DifferentOperators(a, b) => {
                write!(f, "operators don't match: '{}' and '{}'", a, b)
            }
            CongruenceError::DifferentNumberOfArguments(a, b) => {
                write!(f, "different numbers of arguments: {} and {}", a, b)
            }
            CongruenceError::NotApplicationOrOperation(t) => {
                write!(f, "term is not an application or operation: '{}'", t)
            }
        }
    }
}
