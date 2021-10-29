use super::lexer::Token;
use crate::ast::{Identifier, Sort};
use num_bigint::BigInt;
use std::{fmt, ops::RangeFrom};

/// The error type for the parser and lexer.
#[derive(Debug, PartialEq)]
pub enum ParserError {
    UnexpectedChar(char),
    LeadingZero(String),
    BackslashInQuotedSymbol,
    EofInQuotedSymbol,
    EofInString,
    EofInNumeral,
    UnexpectedToken(Token),
    EmptySequence,
    SortError(SortError),
    NotAFunction(Sort),
    UndefinedIden(Identifier),
    UndefinedSort(String),
    UndefinedStepIndex(String),
    WrongNumberOfArgs(usize, usize),
    RepeatedStepIndex(String),
    InvalidSortArity(BigInt),
    LastSubproofStepIsNotStep(String),
    UnclosedSubproof(String),
    UnknownAttribute(String),
}

impl From<SortError> for ParserError {
    fn from(err: SortError) -> Self {
        ParserError::SortError(err)
    }
}

impl fmt::Display for ParserError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use ParserError::*;
        match self {
            UnexpectedChar(c) => write!(f, "unexpected character: '{}'", c),
            LeadingZero(s) => write!(f, "leading zero in numeral '{}'", s),
            BackslashInQuotedSymbol => write!(f, "quoted symbol contains backslash"),
            EofInQuotedSymbol => write!(f, "unexpected EOF in quoted symbol"),
            EofInString => write!(f, "unexpected EOF in string literal"),
            EofInNumeral => write!(f, "unexpected EOF in numeral"),
            UnexpectedToken(t) => write!(f, "unexpected token: '{}'", t),
            EmptySequence => write!(f, "expected non-empty sequence"),
            SortError(e) => write!(f, "sort error: {}", e),
            NotAFunction(s) => write!(f, "'{}' is not a function sort", s),
            UndefinedIden(i) => write!(f, "identifier '{}' is not defined", i),
            UndefinedSort(s) => write!(f, "sort '{}' is not defined", s),
            UndefinedStepIndex(i) => write!(f, "step index '{}' is not defined", i),
            WrongNumberOfArgs(e, g) => {
                write!(f, "expected {} arguments, got {}", e, g)
            }
            RepeatedStepIndex(i) => write!(f, "step index '{}' was repeated", i),
            InvalidSortArity(n) => write!(f, "{} is not a valid sort arity", n),
            LastSubproofStepIsNotStep(i) => {
                write!(f, "last command in subproof '{}' is not a step", i)
            }
            UnclosedSubproof(i) => write!(f, "subproof '{}' was not closed", i),
            UnknownAttribute(a) => write!(f, "unknown attribute: ':{}'", a),
        }
    }
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

#[derive(Debug, PartialEq)]
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
