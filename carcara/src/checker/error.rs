use crate::{
    ast::*,
    checker::rules::linear_arithmetic::LinearComb,
    utils::{Range, TypeName},
};
use rug::Rational;
use std::{fmt, io};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum CheckerError {
    #[error("unspecified error")]
    Unspecified,

    #[error(transparent)]
    Substitution(#[from] SubstitutionError),

    #[error("term '{0}' was not in original problem's assumptions")]
    Assume(Rc<Term>),

    // Rule specific errors
    #[error(transparent)]
    Resolution(#[from] ResolutionError),

    #[error(transparent)]
    Cong(#[from] CongruenceError),

    #[error(transparent)]
    Quant(#[from] QuantifierError),

    #[error(transparent)]
    LinearArithmetic(#[from] LinearArithmeticError),

    #[error(transparent)]
    LiaGeneric(#[from] LiaGenericError),

    #[error(transparent)]
    Subproof(#[from] SubproofError),

    #[error("reflexivity failed with terms '{0}' and '{1}'")]
    ReflexivityFailed(Rc<Term>, Rc<Term>),

    #[error("simplifying '{original}' resulted in '{result}', expected result to be '{target}'")]
    SimplificationFailed {
        original: Rc<Term>,
        result: Rc<Term>,
        target: Rc<Term>,
    },

    #[error("encountered cycle when simplifying term: '{0}'")]
    CycleInSimplification(Rc<Term>),

    #[error("'{0}' is not a valid simplification result for this rule")]
    SumProdSimplifyInvalidConclusion(Rc<Term>),

    #[error("term '{0}' is not a connective")]
    TermIsNotConnective(Rc<Term>),

    #[error("term '{0}' does not have the correct form for `ite_intro`")]
    IsNotValidIteIntro(Rc<Term>),

    #[error("broken transitivity chain: can't prove '(= {0} {1})'")]
    BrokenTransitivityChain(Rc<Term>, Rc<Term>),

    #[error("term '{0}' is missing in conclusion clause")]
    ContractionMissingTerm(Rc<Term>),

    #[error("term '{0}' was not expected in conclusion clause")]
    ContractionExtraTerm(Rc<Term>),

    #[error("term '{0}' is not a valid n-ary operation")]
    NotValidNaryTerm(Rc<Term>),

    // General errors
    #[error("expected {0} premises, got {1}")]
    WrongNumberOfPremises(Range, usize),

    #[error("expected {0} terms in clause, got {1}")]
    WrongLengthOfClause(Range, usize),

    #[error("expected {0} arguments, got {1}")]
    WrongNumberOfArgs(Range, usize),

    #[error("expected {1} terms in '{0}' term, got {2}")]
    WrongNumberOfTermsInOp(Operator, Range, usize),

    #[error("expected term '{1}' to appear in '{0}' term")]
    TermDoesntApperInOp(Operator, Rc<Term>),

    #[error("expected {1} terms in clause of step '{0}', got {2}")]
    WrongLengthOfPremiseClause(String, Range, usize),

    #[error("term '{1}' is of the wrong form, expected '{0}'")]
    TermOfWrongForm(&'static str, Rc<Term>),

    #[error("expected term '{0}' to be boolean constant '{1}'")]
    ExpectedBoolConstant(bool, Rc<Term>),

    #[error("expected term '{0}' to be a boolean constant")]
    ExpectedAnyBoolConstant(Rc<Term>),

    #[error("expected term '{1}' to be numerical constant {:?}", .0.to_f64())]
    ExpectedNumber(Rational, Rc<Term>),

    #[error("expected term '{0}' to be a numerical constant")]
    ExpectedAnyNumber(Rc<Term>),

    #[error("expected operation term, got '{0}'")]
    ExpectedOperationTerm(Rc<Term>),

    #[error("expected quantifier term, got '{0}'")]
    ExpectedQuantifierTerm(Rc<Term>),

    #[error("expected 'let' term, got '{0}'")]
    ExpectedLetTerm(Rc<Term>),

    #[error("expected term style argument, got assign style argument: '(:= {0} {1})'")]
    ExpectedTermStyleArg(String, Rc<Term>),

    #[error("expected assign style '(:= ...)' argument, got term style argument: '{0}'")]
    ExpectedAssignStyleArg(Rc<Term>),

    #[error("this rule can only be used in the last step of a subproof")]
    MustBeLastStepInSubproof,

    // Equality errors
    #[error(transparent)]
    TermEquality(#[from] EqualityError<Rc<Term>>),

    #[error(transparent)]
    QuantifierEquality(#[from] EqualityError<Quantifier>),

    #[error(transparent)]
    BindingListEquality(#[from] EqualityError<BindingList>),

    #[error("unknown rule")]
    UnknownRule,
}

/// Errors in which we expected two things to be equal but they weren't.
#[derive(Debug, Error)]
pub enum EqualityError<T: TypeName> {
    #[error("expected {}s to be equal: '{0}' and '{1}'", T::NAME)]
    ExpectedEqual(T, T),

    #[error("expected {} '{got}' to be '{expected}'", T::NAME)]
    ExpectedToBe { expected: T, got: T },
}

#[derive(Debug, Error)]
pub enum ResolutionError {
    #[error("couldn't find tautology in clause")]
    TautologyFailed,

    #[error("pivot was not eliminated: '{0}'")]
    RemainingPivot(Rc<Term>),

    #[error("term in conclusion was not produced by resolution: '{0}'")]
    ExtraTermInConclusion(Rc<Term>),

    #[error("term produced by resolution is missing in conclusion: '{0}'")]
    MissingTermInConclusion(Rc<Term>),

    #[error("pivot was not found in clause: '{0}'")]
    PivotNotFound(Rc<Term>),
}

#[derive(Debug, Error)]
pub enum CongruenceError {
    #[error("too many premises")]
    TooManyPremises,

    #[error("no premise to justify equality of arguments '{0}' and '{1}'")]
    MissingPremise(Rc<Term>, Rc<Term>),

    #[error(
        "premise '(= {} {})' doesn't justify conclusion arguments '{}' and '{}'",
        .premise.0, .premise.1, .args.0, .args.1
    )]
    PremiseDoesntJustifyArgs {
        args: (Rc<Term>, Rc<Term>),
        premise: (Rc<Term>, Rc<Term>),
    },

    #[error("functions don't match: '{0}' and '{1}'")]
    DifferentFunctions(Rc<Term>, Rc<Term>),

    #[error("operators don't match: '{0}' and '{1}'")]
    DifferentOperators(Operator, Operator),

    #[error("different numbers of arguments: {0} and {1}")]
    DifferentNumberOfArguments(usize, usize),

    #[error("term is not an application or operation: '{0}'")]
    NotApplicationOrOperation(Rc<Term>),
}

/// Errors relevant to the rules dealing with quantifiers.
#[derive(Debug, Error)]
pub enum QuantifierError {
    #[error("argument doesn't match any binding: '{0}'")]
    NoBindingMatchesArg(String),

    #[error("no argument was given for binding '{0}'")]
    NoArgGivenForBinding(String),

    #[error("union of bindings '{left_outer}' and '{left_inner}' does not equal '{right}'")]
    JoinFailed {
        left_outer: BindingList,
        left_inner: BindingList,
        right: BindingList,
    },

    #[error("unknown binding introduced in right-hand side: '{0}'")]
    CnfNewBindingIntroduced(String),

    #[error("binding is missing in right-hand side: '{0}'")]
    CnfBindingIsMissing(String),

    #[error("result clause doensn't appear in CNF of original term: '{0}'")]
    ClauseDoesntAppearInCnf(Rc<Term>),
}

/// Errors relevant to the linear arithmetic rules.
#[derive(Debug, Error)]
pub enum LinearArithmeticError {
    #[error("term '{0}' doesn't match any tautology case")]
    NotValidTautologyCase(Rc<Term>),

    #[error("term '{0}' is not a valid disequality operation")]
    InvalidDisequalityOp(Rc<Term>),

    #[error("too many arguments in disequality '{0}'")]
    TooManyArgsInDisequality(Rc<Term>),

    #[error("final disequality is not contradictory: '{}'", DisplayLinearComb(.0, .1))]
    DisequalityIsNotContradiction(Operator, LinearComb),

    #[error("final disequality is not tautological: '{}'", DisplayLinearComb(.0, .1))]
    DisequalityIsNotTautology(Operator, LinearComb),

    #[error("expected term '{0}' to be less than term '{1}'")]
    ExpectedLessThan(Rc<Term>, Rc<Term>),

    #[error("expected term '{0}' to be less than or equal to term '{1}'")]
    ExpectedLessEq(Rc<Term>, Rc<Term>),
}

#[derive(Debug, Error)]
pub enum LiaGenericError {
    #[error("failed to spawn cvc5 process")]
    FailedSpawnCvc5(io::Error),

    #[error("failed to write to cvc5 stdin")]
    FailedWriteToCvc5Stdin(io::Error),

    #[error("error while waiting for cvc5 to exit")]
    FailedWaitForCvc5(io::Error),

    #[error("cvc5 gave invalid output")]
    Cvc5GaveInvalidOutput,

    #[error("cvc5 output not unsat")]
    Cvc5OutputNotUnsat,

    #[error("cvc5 timed out when solving problem")]
    Cvc5Timeout,

    #[error(
        "cvc5 returned non-zero exit code: {}",
        if let Some(i) = .0 { format!("{}", i) } else { "none".to_owned() }
    )]
    Cvc5NonZeroExitCode(Option<i32>),

    #[error("error in inner proof: {0}")]
    InnerProofError(Box<crate::Error>),
}

/// Errors relevant to all rules that end subproofs (not just the `subproof` rule).
#[derive(Debug, Error)]
pub enum SubproofError {
    #[error("discharge must be 'assume' command: '{0}'")]
    DischargeMustBeAssume(String),

    #[error("binding '{0}' appears as free variable in phi")]
    BindBindingIsFreeVarInPhi(String),

    #[error("right and left quantifiers have different number of bindings: {0} and {1}")]
    BindDifferentNumberOfBindings(usize, usize),

    #[error("binding '{0}' was not introduced in context")]
    BindingIsNotInContext(String),

    #[error("expected {0} bindings in 'let' term, got {1}")]
    WrongNumberOfLetBindings(usize, usize),

    #[error(
        "premise '(= {} {})' doesn't justify substitution of '{}' for '{}'",
        .premise.0, .premise.1, .substitution.0, .substitution.1
    )]
    PremiseDoesntJustifyLet {
        substitution: (Rc<Term>, Rc<Term>),
        premise: (Rc<Term>, Rc<Term>),
    },

    #[error("substitution '(:= {0} {1})' doesn't appear as a point in phi")]
    NoPointForSubstitution(Rc<Term>, Rc<Term>),

    #[error("expected binding list in right-hand side to be '{0}'")]
    OnePointWrongBindings(BindingList),
}

/// A wrapper struct that implements `fmt::Display` for linear combinations.
struct DisplayLinearComb<'a>(&'a Operator, &'a LinearComb);

impl<'a> fmt::Display for DisplayLinearComb<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fn write_var(f: &mut fmt::Formatter, (var, coeff): (&Rc<Term>, &Rational)) -> fmt::Result {
            if *coeff == 1i32 {
                write!(f, "{}", var)
            } else {
                write!(f, "(* {:?} {})", coeff.to_f64(), var)
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
        write!(f, " {:?})", constant.to_f64())
    }
}
