use super::lexer::{Position, Token};
use crate::ast::{Identifier, Sort};
use num_bigint::BigInt;
use std::{fmt, io, ops::RangeFrom};

/// A `Result` type alias for parser errors.
pub type ParserResult<T> = Result<T, ParserError>;

#[derive(Debug, PartialEq)]
pub struct ParserError(pub ErrorKind, pub Option<Position>);

impl fmt::Display for ParserError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self.0 {
            ErrorKind::Io(e) => write!(f, "{}", e.0),
            ErrorKind::UnexpectedChar(c) => write!(f, "unexpected character: '{}'", c),
            ErrorKind::LeadingZero(s) => write!(f, "leading zero in numeral '{}'", s),
            ErrorKind::BackslashInQuotedSymbol => write!(f, "quoted symbol contains backslash"),
            ErrorKind::EofInQuotedSymbol => write!(f, "unexpected EOF in quoted symbol"),
            ErrorKind::EofInString => write!(f, "unexpected EOF in string literal"),
            ErrorKind::EofInNumeral => write!(f, "unexpected EOF in numeral"),
            ErrorKind::UnexpectedToken(t) => write!(f, "unexpected token: '{}'", t),
            ErrorKind::EmptySequence => write!(f, "expected non-empty sequence"),
            ErrorKind::SortError(e) => write!(f, "sort error: {}", e),
            ErrorKind::UndefinedIden(i) => write!(f, "identifier '{}' is not defined", i),
            ErrorKind::UndefinedSort(s) => write!(f, "sort '{}' is not defined", s),
            ErrorKind::UndefinedStepIndex(i) => write!(f, "step index '{}' is not defined", i),
            ErrorKind::WrongNumberOfArgs(e, g) => write!(f, "expected {} arguments, got {}", e, g),
            ErrorKind::RepeatedStepIndex(i) => write!(f, "step index '{}' was repeated", i),
            ErrorKind::InvalidSortArity(n) => write!(f, "{} is not a valid sort arity", n),
            ErrorKind::LastSubproofStepIsNotStep(i) => {
                write!(f, "last command in subproof '{}' is not a step", i)
            }
            ErrorKind::UnknownAttribute(a) => write!(f, "unknown attribute: ':{}'", a),
        }?;
        if let Some((l, c)) = self.1 {
            write!(f, " (on line {}, column {})", l, c)?;
        }
        Ok(())
    }
}

impl<T: Into<ErrorKind>> From<T> for ParserError {
    fn from(err: T) -> Self {
        ParserError(err.into(), None)
    }
}

impl<T: Into<ErrorKind>> From<(T, Position)> for ParserError {
    fn from((err, pos): (T, Position)) -> Self {
        ParserError(err.into(), Some(pos))
    }
}

/// The error type for the parser and lexer.
#[derive(Debug, PartialEq)]
pub enum ErrorKind {
    Io(ParserIoError),
    UnexpectedChar(char),
    LeadingZero(String),
    BackslashInQuotedSymbol,
    EofInQuotedSymbol,
    EofInString,
    EofInNumeral,
    UnexpectedToken(Token),
    EmptySequence,
    SortError(SortError),
    UndefinedIden(Identifier),
    UndefinedSort(String),
    UndefinedStepIndex(String),
    WrongNumberOfArgs(usize, usize),
    RepeatedStepIndex(String),
    InvalidSortArity(BigInt),
    LastSubproofStepIsNotStep(String),
    UnknownAttribute(String),
}

impl From<io::Error> for ErrorKind {
    fn from(err: io::Error) -> Self {
        ErrorKind::Io(ParserIoError(err))
    }
}

impl From<SortError> for ErrorKind {
    fn from(err: SortError) -> Self {
        ErrorKind::SortError(err)
    }
}

impl ErrorKind {
    /// Returns an error if the length of `sequence` is not `expected`.
    pub fn assert_num_of_args<T>(sequence: &[T], expected: usize) -> Result<(), Self> {
        let got = sequence.len();
        if got == expected {
            Ok(())
        } else {
            Err(ErrorKind::WrongNumberOfArgs(expected, got))
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
            Err(ErrorKind::WrongNumberOfArgs(expected.start, got))
        }
    }
}

/// A simple wrapper of `io::Error` so `ParserError` can derive `PartialEq`
#[derive(Debug)]
pub struct ParserIoError(io::Error);

impl PartialEq for ParserIoError {
    fn eq(&self, other: &Self) -> bool {
        self.0.kind() == other.0.kind()
    }
}

#[derive(Debug, PartialEq)]
pub enum SortError {
    Expected { expected: Sort, got: Sort },
    ExpectedOneOf { possibilities: Vec<Sort>, got: Sort },
}

impl fmt::Display for SortError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            SortError::Expected { expected, got } => {
                write!(f, "expected '{}', got '{}'", expected, got)
            }
            SortError::ExpectedOneOf { possibilities, got } => match possibilities.as_slice() {
                [] => unreachable!(),
                [p] => write!(f, "expected '{}', got '{}'", p, got),
                [first, middle @ .., last] => {
                    write!(f, "expected '{}'", first)?;
                    for p in middle {
                        write!(f, ", '{}'", p)?;
                    }
                    write!(f, "or '{}', got '{}'", last, got)
                }
            },
        }
    }
}

impl SortError {
    /// Returns an `Expected` sort error if `got` does not equal `expected`.
    pub fn assert_eq(expected: &Sort, got: &Sort) -> Result<(), Self> {
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
    pub fn assert_all_eq(sequence: &[&Sort]) -> Result<(), Self> {
        for i in 1..sequence.len() {
            Self::assert_eq(sequence[i - 1], sequence[i])?;
        }
        Ok(())
    }

    /// Returns an `ExpectedOneOf` sort error if `got` is not in `possibilities`.
    pub fn assert_one_of(possibilities: &[Sort], got: &Sort) -> Result<(), Self> {
        match possibilities.iter().find(|&s| s == got) {
            Some(_) => Ok(()),
            None => Err(Self::ExpectedOneOf {
                possibilities: possibilities.to_vec(),
                got: got.clone(),
            }),
        }
    }
}
