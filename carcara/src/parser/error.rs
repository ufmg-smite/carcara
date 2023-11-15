//! The types for parser errors.

use crate::{
    ast::{Constant, Sort},
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

    /// The lexer encountered a `\` character while reading a quoted symbol.
    #[error("quoted symbol contains backslash")]
    BackslashInQuotedSymbol,

    /// The lexer encountered the end of the input while reading a quoted symbol.
    #[error("unexpected EOF in quoted symbol")]
    EofInQuotedSymbol,

    /// The lexer encountered the end of the input while reading a string literal.
    #[error("unexpected EOF in string literal")]
    EofInString,

    /// The lexer encountered a bitvector literal with no actual digits. This
    /// happens when the bitvector literal is just `#`, `#b` or `#x`.
    #[error("empty bitvector literal")]
    EmptyBitvector,

    /// Bitvector literal is too large.
    #[error("bitvector literal is too large")]
    TooLargeBitvector,

    /// The parser encountered an unexpected token.
    #[error("unexpected token: '{0}'")]
    UnexpectedToken(Token),

    /// The parser parsed an empty sequence where only non-empty sequences are allowed.
    #[error("expected non-empty sequence")]
    EmptySequence,

    /// An error in sort checking.
    #[error("sort error: {0}")]
    SortError(#[from] SortError),

    /// Expected BvSort
    #[error("expected bitvector sort, got '{0}'")]
    ExpectedBvSort(Sort),

    // Expected Constant::Integer, got other Constant
    #[error("expected Constant of type Integer, got '{0}'")]
    ExpectedIntegerConstant(Constant),

    /// A term that is not a function was used as a function.
    #[error("'{0}' is not a function sort")]
    NotAFunction(Sort), // TODO: This should also carry the actual function term

    /// The parser encountered an identifier that was not defined.
    #[error("identifier '{0}' is not defined")]
    UndefinedIden(String),

    /// The parser encountered a sort that was not defined.
    #[error("sort '{0}' is not defined")]
    UndefinedSort(String),

    /// The parser encountered a step id that was not defined.
    #[error("step id '{0}' is not defined")]
    UndefinedStepIndex(String),

    /// The wrong number of arguments was given to a function, operator or sort.
    #[error("expected {0} arguments, got {1}")]
    WrongNumberOfArgs(Range, usize),

    #[error("expected argument value to be greater than {0}, got {1}")]
    ExpectedGreaterThanArgs(usize, usize),

    /// A step id was used in more than one step.
    #[error("step id '{0}' was repeated")]
    RepeatedStepIndex(String),

    /// The number given as the arity in a `declare-sort` command is too large. This only happens
    /// if the number is too big to fit in a `usize`, so it almost never happens.
    #[error("{0} is not a valid sort arity")]
    InvalidSortArity(Integer),

    /// The parser encountered an empty subproof
    #[error("subproof '{0}' is empty")]
    EmptySubproof(String),

    /// The last command in a subproof is not a `step` command.
    #[error("last command in subproof '{0}' is not a step")]
    LastSubproofStepIsNotStep(String),

    /// The parser encountered the end of the input while it was still inside a subproof.
    #[error("subproof '{0}' was not closed")]
    UnclosedSubproof(String),

    /// The parser could not get bitvector width from Sort
    #[error("could not get bitvector width from sort '{0}'")]
    UnreachableBitVecWidth(Sort),
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

/// Returns an error if the value of of `sequence` is not in the `expected` range.
pub fn assert_args_value<T, R>(sequence: &[T], range: R) -> Result<(), ParserError>
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

/// An error in sort checking.
#[derive(Debug, Error)]
pub struct SortError {
    /// The possible sorts that were expected.
    pub expected: Vec<Sort>,

    /// The sort we got.
    pub got: Sort,
}

impl fmt::Display for SortError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.expected.as_slice() {
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

impl SortError {
    /// Returns a sort error if `got` does not equal `expected`.
    pub(crate) fn assert_eq(expected: &Sort, got: &Sort) -> Result<(), Self> {
        if expected == got {
            Ok(())
        } else {
            Err(Self {
                expected: vec![expected.clone()],
                got: got.clone(),
            })
        }
    }

    /// Makes sure all terms in `sequence` are equal to each other, otherwise returns an error.
    pub(crate) fn assert_all_eq(sequence: &[&Sort]) -> Result<(), Self> {
        for i in 1..sequence.len() {
            Self::assert_eq(sequence[i - 1], sequence[i])?;
        }
        Ok(())
    }

    /// Returns a sort error if `got` is not one of `possibilities`.
    pub(crate) fn assert_one_of(possibilities: &[Sort], got: &Sort) -> Result<(), Self> {
        if possibilities.contains(got) {
            Ok(())
        } else {
            Err(Self {
                expected: possibilities.to_vec(),
                got: got.clone(),
            })
        }
    }
}
