use crate::{
    ast::*,
    checker::rules::linear_arithmetic::LinearComb,
    utils::{Range, TypeName},
};
use num_rational::BigRational;
use num_traits::One;
use std::fmt;

#[derive(Debug)]
pub enum CheckerError {
    Unspecified,

    // Rule specific errors
    Resolution(ResolutionError),
    Cong(CongruenceError),
    Quant(QuantifierError),
    LinearArithmetic(LinearArithmeticError),
    Subproof(SubproofError),
    ReflexivityFailed(Rc<Term>, Rc<Term>),
    SimplificationFailed {
        original: Rc<Term>,
        result: Rc<Term>,
        target: Rc<Term>,
    },
    CycleInSimplification(Rc<Term>),
    SumProdSimplifyInvalidConclusion(Rc<Term>),
    TermIsNotConnective(Rc<Term>),
    IsNotIteSubterm(Rc<Term>),
    BrokenTransitivityChain(Rc<Term>, Rc<Term>),

    // TODO: This error is not detailed enough. This is because the current implementation of the
    // "ac_simp" rule does not compute the expected term explicitly. Instead, it expands the
    // original term applying the simplification rules gradually, comparing it with the result term
    // encountered in the conclusion. This is because there is a bug in veriT that causes the
    // simplification to not be complete in some cases. Once this bug is solved, we can revert back
    // to a simpler implementation of this rule, that would allow a more detailed error message
    AcSimpFailed(Rc<Term>, Rc<Term>),
    ReorderingMissingTerm(Rc<Term>),
    ReorderingExtraTerm(Rc<Term>),
    NotValidNaryTerm(Rc<Term>),

    // General errors
    WrongNumberOfPremises(Range, usize),
    WrongLengthOfClause(Range, usize),
    WrongNumberOfArgs(Range, usize),
    WrongNumberOfStepsInSubproof(Range, usize),
    WrongNumberOfTermsInOp(Operator, Range, usize),
    TermDoesntApperInOp(Operator, Rc<Term>),
    BadPremise(String), // TODO: This error is too general
    WrongLengthOfPremiseClause(String, Range, usize),
    TermOfWrongForm(&'static str, Rc<Term>),
    ExpectedBoolConstant(bool, Rc<Term>),
    ExpectedAnyBoolConstant(Rc<Term>),
    ExpectedNumber(BigRational, Rc<Term>),
    ExpectedAnyNumber(Rc<Term>),
    ExpectedTermStyleArg(String, Rc<Term>),
    ExpectedAssignStyleArg(Rc<Term>),
    MustBeLastStepInSubproof,

    // Equality errors
    TermEquality(EqualityError<Rc<Term>>),
    QuantifierEquality(EqualityError<Quantifier>),
    BindingListEquality(EqualityError<BindingList>),

    UnknownRule,
}

impl fmt::Display for CheckerError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            CheckerError::Unspecified => write!(f, "unspecified error"),
            CheckerError::Resolution(e) => write!(f, "{}", e),
            CheckerError::Cong(e) => write!(f, "{}", e),
            CheckerError::Quant(e) => write!(f, "{}", e),
            CheckerError::LinearArithmetic(e) => write!(f, "{}", e),
            CheckerError::Subproof(e) => write!(f, "{}", e),
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
            CheckerError::SumProdSimplifyInvalidConclusion(t) => {
                write!(
                    f,
                    "'{}' is not a valid simplification result for this rule",
                    t
                )
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
            CheckerError::AcSimpFailed(original, target) => {
                write!(
                    f,
                    "couldn't reach '{}' by simplifying '{}'",
                    target, original
                )
            }
            CheckerError::ReorderingMissingTerm(t) => {
                write!(f, "term '{}' is missing in conclusion clause", t)
            }
            CheckerError::ReorderingExtraTerm(t) => {
                write!(f, "term '{}' was not expected in conclusion clause", t)
            }
            CheckerError::NotValidNaryTerm(t) => {
                write!(f, "term '{}' is not a valid n-ary operation", t)
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
            CheckerError::WrongNumberOfStepsInSubproof(expected, got) => {
                write!(
                    f,
                    "expected {} commands in subproof, got {}",
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
            CheckerError::WrongLengthOfPremiseClause(index, expected, got) => {
                write!(
                    f,
                    "expected {} terms in clause of step '{}', got {}",
                    expected.to_text(),
                    index,
                    got
                )
            }
            CheckerError::TermOfWrongForm(pat, term) => {
                write!(
                    f,
                    "term '{}' is of the wrong form, expected '{}'",
                    term, pat
                )
            }
            CheckerError::ExpectedBoolConstant(b, t) => {
                write!(f, "expected term '{}' to be boolean constant '{}'", t, b)
            }
            CheckerError::ExpectedAnyBoolConstant(t) => {
                write!(f, "expected term '{}' to be a boolean constant", t)
            }
            CheckerError::ExpectedNumber(r, t) => {
                write!(
                    f,
                    "expected term '{}' to be numerical constant {}",
                    t,
                    DisplayRatio(r)
                )
            }
            CheckerError::ExpectedAnyNumber(t) => {
                write!(f, "expected term '{}' to be a numerical constant", t)
            }
            CheckerError::ExpectedTermStyleArg(name, value) => {
                write!(
                    f,
                    "expected term style argument, got assign style argument: '(:= {} {})'",
                    name, value
                )
            }
            CheckerError::ExpectedAssignStyleArg(t) => {
                write!(
                    f,
                    "expected assign style '(:= ...)' argument, got term style argument: '{}'",
                    t
                )
            }
            CheckerError::MustBeLastStepInSubproof => {
                write!(
                    f,
                    "this rule can only be used in the last step of a subproof"
                )
            }
            CheckerError::TermEquality(e) => write!(f, "{}", e),
            CheckerError::QuantifierEquality(e) => write!(f, "{}", e),
            CheckerError::BindingListEquality(e) => write!(f, "{}", e),

            CheckerError::UnknownRule => write!(f, "unknown rule"),
        }
    }
}

macro_rules! impl_from_for_checker_error {
    ($($type:ty => $variant:ident,)*) => {$(
        impl From<$type> for CheckerError {
            fn from(e: $type) -> Self {
                Self::$variant(e)
            }
        }
    )*}

}

impl_from_for_checker_error! {
    EqualityError<Rc<Term>> => TermEquality,
    EqualityError<Quantifier> => QuantifierEquality,
    EqualityError<BindingList> => BindingListEquality,
    ResolutionError => Resolution,
    CongruenceError => Cong,
    QuantifierError => Quant,
    LinearArithmeticError => LinearArithmetic,
    SubproofError => Subproof,
}

/// Errors in which we expected two things to be equal but they weren't.
#[derive(Debug)]
pub enum EqualityError<T> {
    ExpectedEqual(T, T),
    ExpectedToBe { expected: T, got: T },
}

impl<T: fmt::Display + TypeName> fmt::Display for EqualityError<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            EqualityError::ExpectedEqual(a, b) => {
                write!(f, "expected {}s to be equal: '{}' and '{}'", T::NAME, a, b)
            }
            EqualityError::ExpectedToBe { expected, got } => {
                write!(f, "expected {} '{}' to be '{}'", T::NAME, got, expected)
            }
        }
    }
}

#[derive(Debug)]
pub enum ResolutionError {
    TautologyFailed,
    RemainingPivot(Rc<Term>),
    ResolutionMissingTerm(Rc<Term>),
}

impl fmt::Display for ResolutionError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ResolutionError::TautologyFailed => write!(f, "couldn't find tautology in clause"),
            ResolutionError::RemainingPivot(p) => write!(f, "pivot was not eliminated: '{}'", p),
            ResolutionError::ResolutionMissingTerm(t) => {
                write!(
                    f,
                    "term in conclusion was not produced by resolution: '{}'",
                    t
                )
            }
        }
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
    JoinFailed, // TODO: Store bindings in this error
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
            QuantifierError::JoinFailed => {
                write!(
                    f,
                    "union of bindings in the left does not equal bindings in the right"
                )
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

/// Errors relevant to the linear arithmetic rules.
#[derive(Debug)]
pub enum LinearArithmeticError {
    NotValidTautologyCase(Rc<Term>),
    InvalidDisequalityOp(Rc<Term>),
    TooManyArgsInDisequality(Rc<Term>),
    DisequalityIsNotContradiction(Operator, LinearComb),
    DisequalityIsNotTautology(Operator, LinearComb),
    ExpectedLessThan(Rc<Term>, Rc<Term>),
    ExpectedLessEq(Rc<Term>, Rc<Term>),
}

impl fmt::Display for LinearArithmeticError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            LinearArithmeticError::NotValidTautologyCase(t) => {
                write!(f, "term '{}' doesn't match any tautology case", t)
            }
            LinearArithmeticError::InvalidDisequalityOp(t) => {
                write!(f, "term '{}' is not a valid disequality operation", t)
            }
            LinearArithmeticError::TooManyArgsInDisequality(t) => {
                write!(f, "too many arguments in disequality '{}'", t)
            }
            LinearArithmeticError::DisequalityIsNotContradiction(op, comb) => {
                write!(
                    f,
                    "final disequality is not contradictory: '{}'",
                    DisplayLinearComb(op, comb)
                )
            }
            LinearArithmeticError::DisequalityIsNotTautology(op, comb) => {
                write!(
                    f,
                    "final disequality is not tautological: '{}'",
                    DisplayLinearComb(op, comb)
                )
            }
            LinearArithmeticError::ExpectedLessThan(a, b) => {
                write!(f, "expected term '{}' to be less than term '{}'", a, b)
            }
            LinearArithmeticError::ExpectedLessEq(a, b) => {
                write!(
                    f,
                    "expected term '{}' to be less than or equal to term '{}'",
                    a, b
                )
            }
        }
    }
}

/// Errors relevant to all rules that end subproofs (not just the "subproof" rule).
#[derive(Debug)]
pub enum SubproofError {
    DischargeMustBeAssume(String),
    BindBindingIsFreeVarInPhi(String),
    BindDifferentNumberOfBindings(usize, usize),
    BindingIsNotInContext(String),
    WrongNumberOfLetBindings(usize, usize),
    PremiseDoesntJustifyLet {
        substitution: (Rc<Term>, Rc<Term>),
        premise: (Rc<Term>, Rc<Term>),
    },
    NoPointForSubstitution(Rc<Term>, Rc<Term>),
    OnePointWrongBindings(BindingList),
}

impl fmt::Display for SubproofError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            SubproofError::DischargeMustBeAssume(index) => {
                write!(f, "discharge must be 'assume' command: '{}'", index)
            }
            SubproofError::BindBindingIsFreeVarInPhi(var) => {
                write!(f, "binding '{}' appears as free variable in phi", var)
            }
            SubproofError::BindDifferentNumberOfBindings(left, right) => {
                write!(
                    f,
                    "right and left quantifiers have different number of bindings: {} and {}",
                    left, right
                )
            }
            SubproofError::BindingIsNotInContext(var) => {
                write!(f, "binding '{}' was not introduced in context", var)
            }
            SubproofError::WrongNumberOfLetBindings(expected, got) => {
                write!(
                    f,
                    "expected {} bindings in 'let' term, got {}",
                    expected, got
                )
            }
            SubproofError::PremiseDoesntJustifyLet { substitution, premise } => {
                write!(
                    f,
                    "premise '(= {} {})' doesn't justify substitution of '{}' for '{}'",
                    premise.0, premise.1, substitution.0, substitution.1
                )
            }
            SubproofError::NoPointForSubstitution(k, v) => {
                write!(
                    f,
                    "substitution '(:= {} {})' doesn't appear as a point in phi",
                    k, v
                )
            }
            SubproofError::OnePointWrongBindings(expected) => {
                write!(
                    f,
                    "expected binding list in right-hand side to be '{}'",
                    expected
                )
            }
        }
    }
}

/// A wrapper struct that implements `fmt::Display` for `BigRational`s.
struct DisplayRatio<'a>(&'a BigRational);

impl<'a> fmt::Display for DisplayRatio<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use num_traits::ToPrimitive;
        let float_value = self.0.numer().to_f64().unwrap() / self.0.denom().to_f64().unwrap();
        write!(f, "{:?}", float_value)
    }
}

/// A wrapper struct that implements `fmt::Display` for linear combinations.
struct DisplayLinearComb<'a>(&'a Operator, &'a LinearComb);

impl<'a> fmt::Display for DisplayLinearComb<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fn write_var(
            f: &mut fmt::Formatter,
            (var, coeff): (&Rc<Term>, &BigRational),
        ) -> fmt::Result {
            if coeff.is_one() {
                write!(f, "{}", var)
            } else {
                write!(f, "(* {} {})", DisplayRatio(coeff), var)
            }
        }

        let DisplayLinearComb(op, LinearComb(vars, constant)) = self;
        write!(f, "({} ", op)?;
        match vars.len() {
            0 => write!(f, "0.0"),
            1 => write_var(f, vars.iter().next().unwrap()),
            _ => {
                write!(f, "(+")?;
                for var in vars.iter() {
                    write!(f, " ")?;
                    write_var(f, var)?;
                }
                write!(f, ")")
            }
        }?;
        write!(f, " {})", DisplayRatio(constant))
    }
}
