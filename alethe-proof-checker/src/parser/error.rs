use crate::{
    ast::{Identifier, Sort},
    parser::Token,
    utils::Range,
};
use num_bigint::BigInt;
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

    /// The lexer encountered the end of the input while reading a numeral. This only happens when
    /// the lexer reads a `#` character that is immediately followed by the end of the input.
    #[error("unexpected EOF in numeral")]
    EofInNumeral,

    /// The parser encountered an unexpected token.
    #[error("unexpected token: '{0}'")]
    UnexpectedToken(Token),

    /// The parser parsed an empty sequence where only non-empty sequences are allowed.
    #[error("expected non-empty sequence")]
    EmptySequence,

    /// An error in sort checking.
    #[error("sort error: {0}")]
    SortError(#[from] SortError),

    /// A term that is not a function was used as a function.
    #[error("'{0}' is not a function sort")]
    NotAFunction(Sort), // TODO: This should also carry the actual function term

    /// The parser encountered an identifier that was not defined.
    #[error("identifier '{0}' is not defined")]
    UndefinedIden(Identifier),

    /// The parser encountered a sort that was not defined.
    #[error("sort '{0}' is not defined")]
    UndefinedSort(String),

    /// The parser encountered a step index that was not defined.
    #[error("step index '{0}' is not defined")]
    UndefinedStepIndex(String),

    /// The wrong number of arguments was given to a function, operator or sort.
    #[error("expected {0} arguments, got {1}")]
    WrongNumberOfArgs(Range, usize),

    /// A step index was used in more than one step.
    #[error("step index '{0}' was repeated")]
    RepeatedStepIndex(String),

    /// The number given as the arity in a `declare-sort` command is too large. This only happens
    /// if the number is too big to fit in a `usize`, so it almost never happens.
    #[error("{0} is not a valid sort arity")]
    InvalidSortArity(BigInt),

    /// The last command in a subproof is not a `step` command.
    #[error("last command in subproof '{0}' is not a step")]
    LastSubproofStepIsNotStep(String),

    /// The parser encountered the end of the input while it was still inside a subproof.
    #[error("subproof '{0}' was not closed")]
    UnclosedSubproof(String),

    /// An unknown attribute was given to an annotated term.
    #[error("unknown attribute: ':{0}'")]
    UnknownAttribute(String),
}

/// Returns an error if the length of `sequence` is not in the `expected` range.
pub(crate) fn assert_num_of_args<T, R>(sequence: &[T], expected: R) -> Result<(), ParserError>
where
    R: Into<Range>,
{
    let expected = expected.into();
    let got = sequence.len();
    if expected.contains(got) {
        Ok(())
    } else {
        Err(ParserError::WrongNumberOfArgs(expected, got))
    }
}

/// An error in sort checking.
#[derive(Debug, Error)]
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
