//! Errors produced while checking a proof.

use crate::automata::{Automaton, Trigger};
use crate::external::ExternalError;
use crate::{
    ast::*,
    checker::rules::linear_arithmetic::LinearComb,
    utils::{Range, TypeName},
};
use rug::{Integer, Rational};
use std::fmt;
use thiserror::Error;

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

    /// An error in a linear arithmetic rule.
    #[error(transparent)]
    LinearArithmetic(#[from] LinearArithmeticError),

    /// An error in a polynomial simplification rule.
    #[error(transparent)]
    Polynomial(#[from] PolynomialError),

    /// An error when using an external tool.
    #[error(transparent)]
    External(#[from] ExternalError),

    /// An error in a subproof closing rule.
    #[error(transparent)]
    Subproof(#[from] SubproofError),

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

    /// A term in the conclusion of a `sum_simplify` or `prod_simplify` rule is not a valid
    /// simplification result.
    #[error("'{0}' is not a valid simplification result for this rule")]
    SumProdSimplifyInvalidConclusion(Rc<Term>),

    /// Expected this term to be a boolean connective (such as `xor`, `=>`, `ite`).
    #[error("term '{0}' is not a connective")]
    TermIsNotConnective(Rc<Term>),

    /// A term does not have the correct form for the `ite_intro` rule.
    #[error("term '{0}' does not have the correct form for `ite_intro`")]
    IsNotValidIteIntro(Rc<Term>),

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

    /// The `re_unfold_pos` rule cannot be applied to the given regular expression term.
    #[error("cannot apply the re_unfold_pos rule to the regular expression term '{0}'")]
    CannotApplyReUnfoldPos(Rc<Term>),

    /// The `shuffle` rule cannot be applied because the operator is not commutative.
    #[error("operator '{0}' is not commutative")]
    OperatorNotCommutative(Operator),

    /// The argument multisets of a `shuffle` step are not equal.
    #[error("argument multisets are not equal")]
    ShuffleArgsNotEqual,

    /// A term was expected to be a comparison operation (such as `<`, `<=`, `>`, or `>=`), but was
    /// not.
    #[error("expected comparison operation, got: '{0}'")]
    ExpectedComparisonOp(Rc<Term>),

    /// The monomial relation in the `la_mult_sign` rule does not match the expected relation.
    #[error("monomial relation does not match expected, got: '{0}'")]
    LaMultSignWrongRelation(Rc<Term>),

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

    /// A term was expected to appear in an operation term, but did not.
    #[error("expected term '{1}' to appear in '{0}' term")]
    TermDoesntAppearInOp(Operator, Rc<Term>),

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

    /// Two string terms were expected to have different constant prefixes.
    #[error("expected terms '{0}' and '{1}' to have different constant prefixes")]
    ExpectedDifferentConstantPrefixes(Rc<Term>, Rc<Term>),

    /// A term was expected to be a specific numeric constant.
    #[error("expected term '{}' to be numerical constant {:?}", .1, .0.to_f64())]
    ExpectedNumber(Rational, Rc<Term>),

    /// A term was expected to be a specific integer constant.
    #[error("expected term '{}' to be integer constant {:?}", .1, .0.to_i32())]
    ExpectedInteger(Integer, Rc<Term>),

    /// A term was expected to be a numeric constant.
    #[error("expected term '{0}' to be a numerical constant")]
    ExpectedAnyNumber(Rc<Term>),

    #[error("expected term '{0}' to be a string constant")]
    ExpectedAnyString(Rc<Term>),

    #[error("expected an 'automaton' term, got '{0}'")]
    ExpectedAutomaton(Rc<Term>),

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
    #[error("the rule {0} wasn`t found")]
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
    /// The union of the bindings on the left-hand side of a `qnt_join` rule does not equal the
    /// bindings on the right-hand side.
    #[error("union of bindings '{left_outer}' and '{left_inner}' does not equal '{right}'")]
    JoinFailed {
        /// The bindings of the outer quantifier on the left-hand side.
        left_outer: BindingList,
        /// The bindings of the inner quantifier on the left-hand side.
        left_inner: BindingList,
        /// The bindings on the right-hand side.
        right: BindingList,
    },

    /// A binding introduced on the right-hand side was not present on the left-hand side.
    #[error("unknown binding introduced in right-hand side: '{0}'")]
    NewBindingIntroduced(String),

    /// A binding from the left-hand side that is still used is missing from the right-hand side.
    #[error("binding is missing in right-hand side: '{0}'")]
    BindingIsMissing(String),

    /// A clause does not appear in the CNF of the original term.
    #[error("result clause doesn't appear in CNF of original term: '{0}'")]
    ClauseDoesntAppearInCnf(Rc<Term>),

    /// A bound variable appears as a free variable in the term.
    #[error("binding '{0}' appears as free variable in term '{1}'")]
    MiniscopeFreeVar(String, Rc<Term>),
}

/// Errors relevant to the linear arithmetic rules.
#[derive(Debug, Error)]
pub enum LinearArithmeticError {
    /// A term does not match any tautology case.
    #[error("term '{0}' doesn't match any tautology case")]
    NotValidTautologyCase(Rc<Term>),

    /// A term is not a valid disequality operation.
    #[error("term '{0}' is not a valid disequality operation")]
    InvalidDisequalityOp(Rc<Term>),

    /// A disequality operation has too many arguments.
    #[error("too many arguments in disequality '{0}'")]
    TooManyArgsInDisequality(Rc<Term>),

    /// The final disequality is not contradictory.
    #[error("final disequality is not contradictory: '{}'", DisplayLinearComb(.0, .1))]
    DisequalityIsNotContradiction(Operator, Box<LinearComb>),

    /// The final disequality is not tautological.
    #[error("final disequality is not tautological: '{}'", DisplayLinearComb(.0, .1))]
    DisequalityIsNotTautology(Operator, Box<LinearComb>),

    /// A term was expected to be less than another term.
    #[error("expected term '{0}' to be less than term '{1}'")]
    ExpectedLessThan(Rc<Term>, Rc<Term>),

    /// A term was expected to be less than or equal to another term.
    #[error("expected term '{0}' to be less than or equal to term '{1}'")]
    ExpectedLessEq(Rc<Term>, Rc<Term>),
}

/// Errors relevant to the polynomial simplification rules.
#[derive(Debug, Error)]
pub enum PolynomialError {
    /// Two terms are not equal after polynomial normalization.
    #[error("terms are not equal after polynomial normalization: '{0}' and '{1}'")]
    PolynomialsNotEqual(Rc<Term>, Rc<Term>),

    /// A bitvector sort was expected, but a different sort was found.
    #[error("expected bitvector sort, got '{0}'")]
    ExpectedBvSort(Sort),

    /// A `poly_simp_rel` coefficient cannot be zero.
    #[error("coefficient can't be zero: '{0}'")]
    CoeffIsZero(Rational),

    /// The two coefficients should have the same signum, but did not.
    #[error("coefficients should have the same signum: '{0}' and '{1}'")]
    CoeffDifferentSignums(Rational, Rational),

    /// A coefficient should be odd, but was not.
    #[error("coefficient should be odd: '{0}'")]
    CoeffEven(Integer),

    /// The relation operators of the two terms are invalid.
    #[error("invalid relation operators: '{0}' and '{1}'")]
    InvalidOperators(Operator, Operator),
}

/// Errors relevant to all rules that end subproofs (not just the `subproof` rule).
#[derive(Debug, Error)]
pub enum SubproofError {
    /// A discharge was not an `assume` command.
    #[error("discharge must be 'assume' command: '{0}'")]
    DischargeMustBeAssume(String),

    /// A local assumption was not discharged by the end of the subproof.
    #[error("local assumption '{0}' was not discharged")]
    LocalAssumeNotDischarged(String),

    /// Only the `subproof` rule may discharge local assumptions.
    #[error("only the `subproof` rule may discharge local assumptions")]
    DischargeInWrongRule,

    /// A bound variable appears as a free variable in `phi`.
    #[error("binding '{0}' appears as free variable in phi")]
    BindBindingIsFreeVarInPhi(String),

    /// An unexpected anchor argument was given to the `bind` rule.
    #[error("unexpected anchor argument: '{0}'")]
    BindUnexpectedVarArgument(String),

    /// The right and left quantifiers of a `bind` rule have different numbers of bindings.
    #[error("right and left quantifiers have different number of bindings: {0} and {1}")]
    BindDifferentNumberOfBindings(usize, usize),

    /// A binding was not introduced in the context.
    #[error("binding '{0}' was not introduced in context")]
    BindingIsNotInContext(String),

    /// A `let` term had an unexpected number of bindings.
    #[error("expected {0} bindings in 'let' term, got {1}")]
    WrongNumberOfLetBindings(usize, usize),

    /// The given premise does not justify a substitution in a `let` term.
    #[error(
        "premise '(= {} {})' doesn't justify substitution of '{}' for '{}'",
        .premise.0, .premise.1, .substitution.0, .substitution.1
    )]
    PremiseDoesntJustifyLet {
        /// The substitution that was expected to be justified.
        substitution: (Rc<Term>, Rc<Term>),
        /// The premise that was expected to justify it.
        premise: (Rc<Term>, Rc<Term>),
    },

    /// A substitution does not appear as a point in `phi`.
    #[error("substitution '(:= {0} {1})' doesn't appear as a point in phi")]
    NoPointForSubstitution(String, Rc<Term>),

    /// The binding list in the left-hand side of an `onepoint` rule is wrong.
    #[error("expected binding list in left-hand side to be '{0}'")]
    OnepointWrongLeftBindings(BindingList),

    /// The binding list in the right-hand side of an `onepoint` rule is wrong.
    #[error("expected binding list in right-hand side to be '{0}'")]
    OnepointWrongRightBindings(BindingList),
}

/// Errors relevant to all String rules (CPC and RCP calculi).
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

    #[error(
        "regular expression index of failed: index of '{regex}' in '{s}' starting at '{index}' expected to be '{expected}', got '{got}'"
    )]
    RegexIndexOfFailed {
        s: String,
        regex: Rc<Term>,
        index: Integer,
        expected: Integer,
        got: Integer,
    },

    #[error("expected automata '{0}' and '{1}' to be equivalent")]
    ExpectedEquivalentAutomata(Automaton, Automaton),

    #[error("expected automaton '{0}' to be the empty intersection of '{1}' and '{2}'")]
    ExpectedAutomataEmptyIntersection(Automaton, Automaton, Automaton),

    #[error("expected non empty intersection between '{0}' and '{1}'")]
    ExpectedAutomataIntersection(Automaton, Automaton),

    #[error("expected '{0}' to be a subautomaton of '{1}'")]
    ExpectedSubautomaton(Automaton, Automaton),

    #[error("mismatched number of terms: concatenation has {0} terms, but premises have {1}")]
    ConcatTermsNumberDiffersFromPremiseTermsNumber(usize, usize),

    #[error("expected a backwardable operator, got '{0}'")]
    NotBackwardableOperator(Rc<Term>),
}

impl From<StringError> for CheckerError {
    fn from(e: StringError) -> Self {
        CheckerError::String(Box::new(e))
    }
}

/// A wrapper struct that implements `fmt::Display` for linear combinations.
struct DisplayLinearComb<'a>(&'a Operator, &'a LinearComb);

impl fmt::Display for DisplayLinearComb<'_> {
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
                for var in vars {
                    write!(f, " ")?;
                    write_var(f, var)?;
                }
                write!(f, ")")
            }
        }?;
        write!(f, " {:?})", constant.to_f64())
    }
}
