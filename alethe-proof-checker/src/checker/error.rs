use crate::{ast::*, utils::Range};
use std::fmt;

#[derive(Debug)]
pub enum CheckerError {
    Unspecified,

    // Rule specific errors
    Cong(CongruenceError),
    Quant(QuantifierError),
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
    WrongNumberOfArgs(Range, usize),
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
    ExpectedAssignStyleArg(Rc<Term>),

    UnknownRule,
}

impl fmt::Display for CheckerError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            CheckerError::Unspecified => write!(f, "unspecified error"),
            CheckerError::Cong(e) => write!(f, "{}", e),
            CheckerError::Quant(e) => write!(f, "{}", e),
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
            CheckerError::WrongNumberOfArgs(expected, got) => {
                write!(f, "expected {} arguments, got {}", expected.to_text(), got)
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
            CheckerError::ExpectedAssignStyleArg(t) => {
                write!(
                    f,
                    "expected assign style '(:= ...)' argument, got term style argument: '{}'",
                    t
                )
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

impl From<QuantifierError> for CheckerError {
    fn from(e: QuantifierError) -> Self {
        Self::Quant(e)
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

/// Errors relevant to the rules dealing with quantifiers.
#[derive(Debug)]
pub enum QuantifierError {
    NoBindingMatchesArg(String),
    NoArgGivenForBinding(String),
    ExpectedQuantifierTerm(Rc<Term>),
    ExpectedSameQuantifiers,
    ExpectedQuantifierToBe {
        expected: Quantifier,
        got: Quantifier,
    },
    JoinFailed, // TODO: Store bindings in this error
    ExpectedBindingsToBe {
        expected: BindingList,
        got: BindingList,
    },
    CnfNewBindingIntroduced(String),
    CnfBindingIsMissing(String),
    ClauseDoesntAppearInCnf(Rc<Term>),
}

impl fmt::Display for QuantifierError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            QuantifierError::NoBindingMatchesArg(arg) => {
                write!(f, "argument doesn't match any binding: '{}'", arg)
            }
            QuantifierError::NoArgGivenForBinding(b) => {
                write!(f, "no argument was given for binding '{}'", b)
            }
            QuantifierError::ExpectedQuantifierTerm(t) => {
                write!(f, "expected quantifier term, got '{}'", t)
            }
            QuantifierError::ExpectedSameQuantifiers => {
                write!(f, "expected terms to have the same quantifier")
            }
            QuantifierError::ExpectedQuantifierToBe { expected, got } => {
                write!(f, "expected quantifier '{}' to be '{}'", got, expected)
            }
            QuantifierError::JoinFailed => {
                write!(
                    f,
                    "union of bindings in the left does not equal bindings in the right"
                )
            }
            QuantifierError::ExpectedBindingsToBe { expected, got } => {
                write!(f, "expected bindings '{}' to be '{}'", got, expected,)
            }
            QuantifierError::CnfNewBindingIntroduced(b) => {
                write!(f, "unknown binding introduced in right-hand side: '{}'", b)
            }
            QuantifierError::CnfBindingIsMissing(b) => {
                write!(f, "binding is missing in right-hand side: '{}'", b)
            }
            QuantifierError::ClauseDoesntAppearInCnf(t) => {
                write!(
                    f,
                    "result clause doensn't appear in CNF of original term: '{}'",
                    t
                )
            }
        }
    }
}