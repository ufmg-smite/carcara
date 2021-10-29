use std::{fmt, io, path::PathBuf};

#[derive(Debug)]
pub enum CliError {
    AletheError(alethe_proof_checker::Error),
    InvalidArgument(String),
    InvalidProofFile(PathBuf),
}

impl From<io::Error> for CliError {
    fn from(e: io::Error) -> Self {
        Self::AletheError(alethe_proof_checker::Error::Io(e))
    }
}

impl From<alethe_proof_checker::Error> for CliError {
    fn from(e: alethe_proof_checker::Error) -> Self {
        Self::AletheError(e)
    }
}

impl fmt::Display for CliError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            CliError::AletheError(e) => write!(f, "{}", e),
            CliError::InvalidArgument(a) => write!(f, "invalid argument: {}", a),
            CliError::InvalidProofFile(p) => {
                write!(f, "{} is not a valid proof file", p.to_str().unwrap())
            }
        }
    }
}
