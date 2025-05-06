//! The types for parser errors.

use crate::{
    ast::{Constant, PrimitivePool, Rc, Sort, Term, TermPool},
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

    /// Expected `BvSort`
    #[error("expected bitvector sort, got '{0}'")]
    ExpectedBvSort(Sort),

    // Expected Constant::Integer, got other Term
    #[error("expected integer constant, got '{0}'")]
    ExpectedIntegerConstant(Rc<Term>),

    /// A term that is not a function was used as a function.
    #[error("'{0}' is not a function sort")]
    NotAFunction(Sort), // TODO: This should also carry the actual function term

    /// A term that is not a function was used as a function.
    #[error("'{0}' cannot be matched to '{1}'")]
    IncompatibleSorts(Sort, Sort),

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
    WrongValueOfArgs(Range<Integer>, Integer),

    #[error("extract arguments do not follow restrictions. Expected: {2} > {0} and {0} >= {1} and {1} >= 0")]
    InvalidExtractArgs(usize, usize, usize),

    /// A step id was used in more than one step.
    #[error("step id '{0}' was repeated")]
    RepeatedStepId(String),

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

    /// The parser encountered an unknown indexed operator.
    #[error("not a valid indexed operator: '{0}'")]
    InvalidIndexedOp(String),

    /// The parser encountered an unknown qualified operator.
    #[error("not a valid qualified operator: '{0}'")]
    InvalidQualifiedOp(String),
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
    R: Into<Range<Integer>>,
{
    let range = range.into();
    for x in sequence {
        if let Term::Const(Constant::Integer(i)) = x.as_ref() {
            if !range.contains(i.clone()) {
                return Err(ParserError::WrongValueOfArgs(range, i.clone()));
            }
        }
    }
    Ok(())
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

    pub(crate) fn assert_array_sort(
        pool: &mut PrimitivePool,
        key: Option<&Sort>,
        value: Option<&Sort>,
        got: &Sort,
    ) -> Result<(), Self> {
        let any = Sort::Atom("?".to_owned(), Vec::new());

        let expected = {
            let key = pool.add(Term::Sort(key.cloned().unwrap_or_else(|| any.clone())));
            let value = pool.add(Term::Sort(value.cloned().unwrap_or_else(|| any.clone())));
            vec![Sort::Array(key, value)]
        };
        let Sort::Array(got_key, got_value) = got else {
            return Err(Self { expected, got: got.clone() });
        };
        if key.is_some_and(|k| got_key.as_sort().unwrap() != k)
            || value.is_some_and(|v| got_value.as_sort().unwrap() != v)
        {
            return Err(Self { expected, got: got.clone() });
        }
        Ok(())
    }
}
