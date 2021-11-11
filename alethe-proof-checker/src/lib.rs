#![deny(clippy::disallowed_method)]

#[macro_use]
pub mod ast;
pub mod benchmarking;
pub mod checker;
pub mod parser;
mod utils;

use checker::error::CheckerError;
use parser::error::ParserError;
use parser::lexer::Position;
use std::{
    fmt,
    fs::File,
    io::{self, BufReader},
    path::Path,
};

pub type AletheResult<T> = Result<T, Error>;

#[derive(Debug)]
pub enum Error {
    Io(io::Error),
    Parser(ParserError, Position),
    Checker {
        inner: CheckerError,
        rule: String,
        step: String,
    },
}

impl From<io::Error> for Error {
    fn from(e: io::Error) -> Self {
        Self::Io(e)
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::Io(e) => write!(f, "IO error: {}", e),
            Error::Parser(e, (l, c)) => {
                write!(f, "parser error: {} (on line {}, column {})", e, l, c)
            }
            Error::Checker { inner, rule, step } => write!(
                f,
                "checking failed on step '{}' with rule '{}': {}",
                step, rule, inner
            ),
        }
    }
}

pub fn check<P: AsRef<Path>>(
    problem_path: P,
    proof_path: P,
    skip_unknown_rules: bool,
    is_running_test: bool,
) -> Result<(), Error> {
    let (proof, pool) = parser::parse_instance(
        BufReader::new(File::open(problem_path)?),
        BufReader::new(File::open(proof_path)?),
    )?;

    let config = checker::Config {
        skip_unknown_rules,
        is_running_test,
        statistics: None,
    };
    checker::ProofChecker::new(pool, config).check(&proof)
}
