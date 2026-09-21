//! The types for parser errors.

use crate::{
    ast::{Constant, Rc, Sort, Term},
    parser::Token,
    utils::Range,
};
use rug::Integer;
use std::fmt;
use thiserror::Error;

/// The error type for the parser.
#[derive(Debug, Error)]
pub enum ParserError {
    /// The lexer encountered an unexpected character.
    #[error("unexpected character: '{0}'")]
    UnexpectedChar(char),

    /// The lexer encountered a numeral with a leading zero, e.g. `0123`.
    #[error("leading zero in numeral '{0}'")]
    LeadingZero(String),

    /// The lexer encountered a numerical literal that contained a division by zero, e.g. '1/0'.
    #[error("division by zero in numerical literal: '{0}'")]
    DivisionByZeroInLiteral(String),

    /// The lexer encountered a `\` character while reading a quoted symbol.
    #[error("quoted symbol contains backslash")]
    BackslashInQuotedSymbol,

    /// The lexer encountered the end of the input while reading a quoted symbol.
    #[error("unexpected EOF in quoted symbol")]
    EofInQuotedSymbol,

    /// The lexer encountered the end of the input while reading a string literal.
    #[error("unexpected EOF in string literal")]
    EofInString,

    /// The lexer encountered an invalid Unicode value in an escape sequence.
    #[error("invalid Unicode value: 0x'{0}'")]
    InvalidUnicode(String),

    /// The lexer encountered a bitvector literal with no actual digits. This happens when the
    /// bitvector literal is just `#`, `#b` or `#x`.
    #[error("empty bitvector literal")]
    EmptyBitvector,

    /// A bitvector literal was too large.
    #[error("bitvector literal is too large")]
    TooLargeBitvector,

    /// The parser encountered an unexpected token.
    #[error("unexpected token: '{0}'")]
    UnexpectedToken(Token),

    /// The parser encountered an empty sequence where only non-empty sequences are allowed.
    #[error("expected non-empty sequence")]
    EmptySequence,

    /// An error in sort checking.
    #[error("sort error: {0}")]
    SortError(#[from] SortError),

    /// Expected any bitvector sort.
    #[error("expected bitvector sort, got '{0}'")]
    ExpectedBvSort(Rc<Sort>),

    /// Expected any datatype sort.
    #[error("expected datatype sort, got '{0}'")]
    ExpectedDatatypeSort(Rc<Sort>),

    /// Expected any set sort.
    #[error("expected set sort, got '{0}'")]
    ExpectedSetSort(Rc<Sort>),

    /// Expected any tuple sort.
    #[error("expected tuple sort, got '{0}'")]
    ExpectedTupleSort(Rc<Sort>),

    /// Expected an integer constant term.
    #[error("expected integer constant, got '{0}'")]
    ExpectedIntegerConstant(Rc<Term>),

    /// Pattern in `match` term is not valid.
    #[error("invalid pattern '{0}'")]
    InvalidPattern(Rc<Term>),

    /// Results in `match` term do not have the same type.
    #[error("invalid match results (different types) '{0} and {1}'")]
    InvalidMatchResults(Rc<Term>, Rc<Term>),

    /// Patterns in `match` term do not cover all constructors.
    #[error("Patterns in match statement do not cover all constructors")]
    NonExhaustivePatterns,

    /// A term that is not a function was used as a function.
    #[error("'{0}' is not a function sort")]
    NotAFunction(Rc<Sort>), // TODO: This should also carry the actual function term

    /// Tried to match two incompatible sorts.
    #[error("'{0}' cannot be matched to '{1}'")]
    IncompatibleSorts(Rc<Sort>, Rc<Sort>),

    /// The parser encountered an identifier that was not defined.
    #[error("identifier '{0}' is not defined")]
    UndefinedIden(String),

    /// The parser encountered a sort that was not defined.
    #[error("sort '{0}' is not defined")]
    UndefinedSort(String),

    /// The parser encountered a step id that was not defined.
    #[error("step id '{0}' is not defined")]
    UndefinedStepId(String),

    /// The wrong number of arguments was given to a function, operator or sort.
    #[error("expected {0} arguments, got {1}")]
    WrongNumberOfArgs(Range, usize),

    /// The argument values are not in the expected range.
    #[error("expected argument value to be greater than {0}, got {1}")]
    WrongValueOfArgs(Range, Integer),

    /// Constant arguments given to `extract` do not follow required restrictions.
    #[error(
        "extract arguments do not follow restrictions. Expected: {2} > {0} and {0} >= {1} and {1} >= 0"
    )]
    InvalidExtractArgs(usize, usize, usize),

    /// A step id was used in more than one step.
    #[error("step id '{0}' was repeated")]
    RepeatedStepId(String),

    /// The number given as the arity in a `declare-sort` command is too large. This only happens
    /// if the number is too big to fit in a `usize`, so it almost never happens.
    #[error("{0} is not a valid sort arity")]
    InvalidSortArity(Integer),

    /// The number of datatype declarations given in a `declare-datatypes` command didn't match the
    /// number of sorts declared beforehand.
    #[error("expected {0} datatype declarations, got {1}")]
    WrongNumberOfDatatypeDeclarations(usize, usize),

    /// The number of parameters of a datatype in a `declare-datatypes` command didn't match the
    /// arity declared beforehand.
    #[error("expected {0} parameters for datatype based on declared arity, got {1}")]
    WrongNumberOfDatatypeParams(usize, usize),

    /// A `match` pattern contained an unknown constructor
    #[error("unknown datatype constructor: {0}")]
    UnknownConstructor(String),

    /// The parser encountered an empty subproof
    #[error("subproof '{0}' is empty")]
    EmptySubproof(String),

    /// The last command in a subproof is not a `step` command.
    #[error("last command in subproof '{0}' is not a step")]
    LastSubproofStepIsNotStep(String),

    /// The parser encountered the end of the input while it was still inside a subproof.
    #[error("subproof '{0}' was not closed")]
    UnclosedSubproof(String),

    /// The parser encountered an `assume` after a `step` inside of a subproof.
    #[error("`assume` command '{0}' appears after step inside subproof")]
    AssumeAfterStepInSubproof(String),

    /// The parser encountered an unknown indexed operator.
    #[error("not a valid indexed operator: '{0}'")]
    InvalidIndexedOp(String),

    /// The parser encountered an unknown qualified operator.
    #[error("not a valid qualified operator: '{0}'")]
    InvalidQualifiedOp(String),

    // RCP errors
    #[error("not a valid automaton declaration: '{0}'")]
    InvalidAutomatonDeclaration(String),

    #[error("expected an automaton declaration, got: '{0}'")]
    ExpectedAnAutomatonDeclaration(Rc<Term>),

    /// The parser encountered an invalid argument.
    #[error("not a valid format for the argument: '{0}'")]
    InvalidRareArgFormat(String),

    /// The parser encountered an invalid Rare argument attribute.
    #[error("not a valid argument attribute: '{0}'")]
    InvalidRareArgAttribute(String),

    /// The parser encountered an invalid Rare rule attribute.
    #[error("not a valid rule attribute: '{0}'")]
    InvalidRareRuleAttribute(String),

    /// The parser encountered a Rare ruel with no conclusion.
    #[error("the rule '{0}' has no conclusion")]
    UndefinedRareConclusion(String),

    /// A RARE rule conclusion must be a binary equality.
    #[error("the conclusion of RARE rule '{0}' must be a binary equality")]
    InvalidRareConclusion(String),

    /// A RARE rule premise must be a binary equality or disequality.
    #[error("a premise of RARE rule '{0}' must be a binary equality or disequality")]
    InvalidRarePremise(String),

    /// Every RARE rule argument must name a declared parameter.
    #[error("RARE rule '{0}' uses undeclared argument '{1}'")]
    UndeclaredRareArgument(String, String),
}

/// Returns an error if the length of `sequence` is not in the `expected` range.
pub fn assert_num_args<T, R>(sequence: &[T], range: R) -> Result<(), ParserError>
where
    R: Into<Range>,
{
    let range = range.into();
    if range.contains(sequence.len()) {
        Ok(())
    } else {
        Err(ParserError::WrongNumberOfArgs(range, sequence.len()))
    }
}

/// Returns an error if the value of `sequence` is not in the `expected` range.
pub fn assert_indexed_op_args_value<R>(sequence: &[Rc<Term>], range: R) -> Result<(), ParserError>
where
    R: Into<Range>,
{
    let range = range.into();
    for x in sequence {
        if let Term::Const(Constant::Integer(i)) = x.as_ref() {
            let contained = i.to_usize().is_some_and(|i| range.contains(i));
            if !contained {
                return Err(ParserError::WrongValueOfArgs(range, i.clone()));
            }
        }
    }
    Ok(())
}

/// Makes sure `got` is a valid `Set` sort.
pub fn check_set_sort(got: &Rc<Sort>) -> Result<(), ParserError> {
    if !matches!(got.as_ref(), Sort::Set(_)) {
        return Err(ParserError::ExpectedSetSort(got.clone()));
    }
    Ok(())
}

/// Makes sure `got` is a valid `Tuple` sort.
pub fn check_tuple_sort(got: &Rc<Sort>) -> Result<(), ParserError> {
    if !matches!(got.as_ref(), Sort::Tuple(_)) {
        return Err(ParserError::ExpectedTupleSort(got.clone()));
    }
    Ok(())
}

/// Makes sure `got` is a valid `(Set (Tuple ...))` sort.
pub fn check_relation_sort(got: &Rc<Sort>) -> Result<(), ParserError> {
    let Sort::Set(tuple) = got.as_ref() else {
        return Err(ParserError::ExpectedSetSort(got.clone()));
    };
    check_tuple_sort(tuple)
}

/// An error in sort checking.
#[derive(Debug, Error)]
pub struct SortError {
    /// The possible sorts that were expected.
    pub expected: Box<[Rc<Sort>]>,

    /// The sort we got.
    pub got: Rc<Sort>,
}

impl fmt::Display for SortError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &*self.expected {
            [] => unreachable!(),
            [p] => write!(f, "expected '{}', got '{}'", p, self.got),
            [first, middle @ .., last] => {
                write!(f, "expected '{}'", first)?;
                for p in middle {
                    write!(f, ", '{}'", p)?;
                }
                write!(f, " or '{}', got '{}'", last, self.got)
            }
        }
    }
}
