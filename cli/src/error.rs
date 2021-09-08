use alethe_proof_checker::parser::error::ParserError;
use std::{io, path::PathBuf};

#[derive(Debug)]
pub enum CliError {
    InvalidArgument(String),
    InvalidProofFile(PathBuf),
    AletheError(alethe_proof_checker::Error),
    Io(io::Error),
}

impl From<io::Error> for CliError {
    fn from(e: io::Error) -> Self {
        Self::Io(e)
    }
}

impl From<alethe_proof_checker::Error> for CliError {
    fn from(e: alethe_proof_checker::Error) -> Self {
        Self::AletheError(e)
    }
}

impl From<ParserError> for CliError {
    fn from(e: ParserError) -> Self {
        Self::AletheError(e.into())
    }
}
