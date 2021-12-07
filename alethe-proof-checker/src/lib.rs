#![deny(clippy::disallowed_method)]

#[macro_use]
pub mod ast;
pub mod benchmarking;
pub mod checker;
pub mod parser;
mod utils;

use ast::ProofCommand;
use checker::error::CheckerError;
use parser::ParserError;
use parser::Position;
use std::{
    fs::File,
    io::{self, BufReader},
    path::Path,
};
use thiserror::Error;

pub type AletheResult<T> = Result<T, Error>;

#[derive(Debug, Error)]
pub enum Error {
    #[error("IO error: {0}")]
    Io(#[from] io::Error),

    #[error("parser error: {0} (on line {}, column {})", (.1).0, (.1).1)]
    Parser(ParserError, Position),

    #[error("checking failed on step '{step}' with rule '{rule}': {inner}")]
    Checker {
        inner: CheckerError,
        rule: String,
        step: String,
    },
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
        builder: None,
    };
    checker::ProofChecker::new(pool, config).check(&proof)
}

pub fn check_and_reconstruct<P: AsRef<Path>>(
    problem_path: P,
    proof_path: P,
    skip_unknown_rules: bool,
) -> Result<Vec<ProofCommand>, Error> {
    let (proof, pool) = parser::parse_instance(
        BufReader::new(File::open(problem_path)?),
        BufReader::new(File::open(proof_path)?),
    )?;

    let config = checker::Config {
        skip_unknown_rules,
        is_running_test: false,
        statistics: None,
        builder: Some(Default::default()),
    };
    let mut checker = checker::ProofChecker::new(pool, config);
    checker.check(&proof)?;
    Ok(checker.get_reconstructed_proof())
}
