use std::io;
use std::ops::RangeFrom;

use super::ast::*;
use super::lexer::Token;

/// A `Result` type alias for parser errors.
pub type ParserResult<T> = Result<T, ParserError>;

/// The error type for the parser and lexer.
#[derive(Debug, PartialEq)]
pub enum ParserError {
    Io(ParserIoError),
    UnexpectedChar(Option<char>),
    LeadingZero(String),
    BackslashInQuotedSymbol,
    EofInQuotedSymbol,
    EofInString,
    UnexpectedToken(Token),
    EmptySequence,
    SortError(SortError),
    UndefinedIden(Identifier),
    UndefinedStepIndex(String),
    WrongNumberOfArgs(usize, usize),
    RepeatedStepIndex,
}

impl From<io::Error> for ParserError {
    fn from(e: io::Error) -> Self {
        ParserError::Io(ParserIoError(e))
    }
}

impl From<SortError> for ParserError {
    fn from(e: SortError) -> Self {
        ParserError::SortError(e)
    }
}

impl ParserError {
    /// Returns an error if the length of `sequence` is not `expected`.
    pub fn assert_num_of_args<T>(sequence: &[T], expected: usize) -> ParserResult<()> {
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
    ) -> ParserResult<()> {
        let got = sequence.len();
        if expected.contains(&got) {
            Ok(())
        } else {
            Err(ParserError::WrongNumberOfArgs(expected.start, got))
        }
    }
}

/// A simple wrapper of io::Error so ParserError can derive PartialEq
#[derive(Debug)]
pub struct ParserIoError(io::Error);

impl PartialEq for ParserIoError {
    fn eq(&self, other: &Self) -> bool {
        self.0.kind() == other.0.kind()
    }
}

#[derive(Debug, PartialEq)]
pub enum SortError {
    Expected { expected: Term, got: Term },
    ExpectedOneOf { possibilities: Vec<Term>, got: Term },
}

impl SortError {
    /// Returns an `Expected` sort error if `got` does not equal `expected`.
    pub fn assert_eq(expected: &Term, got: &Term) -> Result<(), Self> {
        if expected == got {
            Ok(())
        } else {
            Err(Self::Expected {
                expected: expected.clone(),
                got: got.clone(),
            })
        }
    }

    /// Makes sure all terms in `sequence` are equal to each other, otherwise returns an `Expected`
    /// error.
    pub fn assert_all_eq(sequence: &[&Term]) -> Result<(), Self> {
        for i in 1..sequence.len() {
            Self::assert_eq(sequence[i - 1], sequence[i])?;
        }
        Ok(())
    }

    /// Returns an `ExpectedOneOf` sort error if `got` is not in `possibilities`.
    pub fn assert_one_of(possibilities: &[&Term], got: &Term) -> Result<(), Self> {
        match possibilities.iter().find(|&&s| s == got) {
            Some(_) => Ok(()),
            None => Err(Self::ExpectedOneOf {
                possibilities: possibilities.iter().map(|t| (*t).clone()).collect(),
                got: got.clone(),
            }),
        }
    }
}
