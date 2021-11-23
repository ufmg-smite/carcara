use super::lexer::Token;
use crate::ast::{Identifier, Sort, SubstitutionError};
use num_bigint::BigInt;
use std::{fmt, ops::RangeFrom};
use thiserror::Error;

/// The error type for the parser and lexer.
#[derive(Debug, Error, PartialEq)]
pub enum ParserError {
    #[error("unexpected character: '{0}'")]
    UnexpectedChar(char),

    #[error("leading zero in numeral '{0}'")]
    LeadingZero(String),

    #[error("quoted symbol contains backslash")]
    BackslashInQuotedSymbol,

    #[error("unexpected EOF in quoted symbol")]
    EofInQuotedSymbol,

    #[error("unexpected EOF in string literal")]
    EofInString,

    #[error("unexpected EOF in numeral")]
    EofInNumeral,

    #[error("unexpected token: '{0}'")]
    UnexpectedToken(Token),

    #[error("expected non-empty sequence")]
    EmptySequence,

    #[error("sort error: {0}")]
    SortError(#[from] SortError),

    #[error("'{0}' is not a function sort")]
    NotAFunction(Sort),

    #[error("identifier '{0}' is not defined")]
    UndefinedIden(Identifier),

    #[error("sort '{0}' is not defined")]
    UndefinedSort(String),

    #[error("step index '{0}' is not defined")]
    UndefinedStepIndex(String),

    #[error("expected {0} arguments, got {1}")]
    WrongNumberOfArgs(usize, usize),

    #[error("step index '{0}' was repeated")]
    RepeatedStepIndex(String),

    #[error("{0} is not a valid sort arity")]
    InvalidSortArity(BigInt),

    #[error("last command in subproof '{0}' is not a step")]
    LastSubproofStepIsNotStep(String),

    #[error("subproof '{0}' was not closed")]
    UnclosedSubproof(String),

    #[error("unknown attribute: ':{0}'")]
    UnknownAttribute(String),

    #[error("substitution error when applying function definition '{0}': {1}")]
    BadFunctionDef(String, SubstitutionError),
}

impl ParserError {
    /// Returns an error if the length of `sequence` is not `expected`.
    pub fn assert_num_of_args<T>(sequence: &[T], expected: usize) -> Result<(), Self> {
        let got = sequence.len();
        if got == expected {
            Ok(())
        } else {
            Err(ParserError::WrongNumberOfArgs(expected, got))
        }
    }

    pub fn assert_num_of_args_range<T>(
        sequence: &[T],
        expected: RangeFrom<usize>,
    ) -> Result<(), Self> {
        let got = sequence.len();
        if expected.contains(&got) {
            Ok(())
        } else {
            Err(ParserError::WrongNumberOfArgs(expected.start, got))
        }
    }
}

#[derive(Debug, Error, PartialEq)]
pub struct SortError {
    pub expected: Vec<Sort>,
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
    /// Returns an `Expected` sort error if `got` does not equal `expected`.
    pub fn assert_eq(expected: &Sort, got: &Sort) -> Result<(), Self> {
        if expected == got {
            Ok(())
        } else {
            Err(Self {
                expected: vec![expected.clone()],
                got: got.clone(),
            })
        }
    }

    /// Makes sure all terms in `sequence` are equal to each other, otherwise returns an `Expected`
    /// error.
    pub fn assert_all_eq(sequence: &[&Sort]) -> Result<(), Self> {
        for i in 1..sequence.len() {
            Self::assert_eq(sequence[i - 1], sequence[i])?;
        }
        Ok(())
    }

    /// Returns an `ExpectedOneOf` sort error if `got` is not in `possibilities`.
    pub fn assert_one_of(possibilities: &[Sort], got: &Sort) -> Result<(), Self> {
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
