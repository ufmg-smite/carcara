use std::{fmt, io, path::PathBuf};

#[derive(Debug)]
pub enum CliError {
    CarcaraError(carcara::Error),
    CantInferProblemFile(PathBuf),
    InvalidSliceId(String),
    BothFilesStdin,
}

pub type CliResult<T> = Result<T, CliError>;

impl From<io::Error> for CliError {
    fn from(e: io::Error) -> Self {
        Self::CarcaraError(carcara::Error::Io(e))
    }
}

impl From<carcara::Error> for CliError {
    fn from(e: carcara::Error) -> Self {
        Self::CarcaraError(e)
    }
}

impl fmt::Display for CliError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            CliError::CarcaraError(e) => write!(f, "{}", e),
            CliError::CantInferProblemFile(p) => {
                write!(f, "can't infer problem file: {}", p.display())
            }
            CliError::BothFilesStdin => write!(f, "problem and proof files can't both be `-`"),
            CliError::InvalidSliceId(id) => write!(f, "invalid id for slice: {}", id),
        }
    }
}
