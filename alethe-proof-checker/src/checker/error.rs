use crate::{ast::*, utils::Range};
use std::fmt;

#[derive(Debug)]
pub enum CheckerError {
    Unspecified,
    Cong(CongruenceError),
    ReflexivityFailed(Rc<Term>, Rc<Term>),
    SimplificationFailed {
        original: Rc<Term>,
        result: Rc<Term>,
        target: Rc<Term>,
    },
    CycleInSimplification(Rc<Term>),
    WrongNumberOfPremises(Range, usize),
    WrongLengthOfClause(Range, usize),
    BadPremise(String), // TODO: This error is too general
    TermOfWrongForm(Rc<Term>),
    TermsNotEqual(Rc<Term>, Rc<Term>),
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
            CheckerError::BadPremise(p) => write!(f, "bad premise: '{}'", p),
            CheckerError::TermOfWrongForm(t) => write!(f, "term is of the wrong form: '{}'", t),
            CheckerError::TermsNotEqual(a, b) => {
                write!(f, "expected terms to be equal: '{}' and '{}'", a, b)
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
                "premise '(= {} {})' doesn't justify arguments '{}' and '{}'",
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
