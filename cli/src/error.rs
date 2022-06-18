use std::{fmt, io, path::PathBuf};

#[derive(Debug)]
pub enum CliError {
    AletheError(alethe_proof_checker::Error),
    CantInferProblemFile(PathBuf),
    BothFilesStdin,
}

pub type CliResult<T> = Result<T, CliError>;

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
            CliError::CantInferProblemFile(p) => {
                write!(f, "can't infer problem file: {}", p.display())
            }
            CliError::BothFilesStdin => write!(f, "problem and proof files can't both be `-`"),
        }
    }
}
