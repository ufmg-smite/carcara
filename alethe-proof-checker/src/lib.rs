#![deny(clippy::disallowed_method)]

#[macro_use]
pub mod ast;
pub mod benchmarking;
pub mod checker;
pub mod parser;
mod utils;

use checker::CheckerError;
use parser::error::ParserError;
use std::{
    fmt,
    fs::File,
    io::{self, BufReader},
    path::Path,
};

#[derive(Debug)]
pub enum Error {
    Parser(ParserError),
    Checker(CheckerError),
}

impl From<ParserError> for Error {
    fn from(e: ParserError) -> Self {
        Self::Parser(e)
    }
}

impl From<CheckerError> for Error {
    fn from(e: CheckerError) -> Self {
        Self::Checker(e)
    }
}

impl From<io::Error> for Error {
    fn from(e: io::Error) -> Self {
        Self::Parser(e.into())
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::Parser(e) => write!(f, "parser error: {}", e),
            Error::Checker(e) => write!(f, "checker error: {}", e),
        }
    }
}

pub fn check<P: AsRef<Path>>(
    problem_path: P,
    proof_path: P,
    skip_unknown_rules: bool,
    is_running_test: bool,
) -> Result<checker::Correctness, Error> {
    let (proof, pool) = parser::parse_instance(
        BufReader::new(File::open(problem_path).unwrap()),
        BufReader::new(File::open(proof_path).unwrap()),
    )?;

    let config = checker::Config {
        skip_unknown_rules,
        is_running_test,
        statistics: None,
    };
    checker::ProofChecker::new(pool, config)
        .check(&proof)
        .map_err(Error::Checker)
}
