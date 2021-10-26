use alethe_proof_checker::parser::error::ParserError;
use std::{fmt, io, path::PathBuf};

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

impl fmt::Display for CliError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            CliError::InvalidArgument(a) => write!(f, "invalid argument: {}", a),
            CliError::InvalidProofFile(p) => {
                write!(f, "{} is not a valid proof file", p.to_str().unwrap())
            }
            CliError::AletheError(e) => write!(f, "{}", e),
            CliError::Io(e) => write!(f, "io error: {}", e),
        }
    }
}
