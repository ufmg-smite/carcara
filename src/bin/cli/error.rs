use ansi_term::{Color, Style};
use carcara::{elaborator::ElaborationPass, parser::Position};
use std::{
    fmt,
    path::{Path, PathBuf},
};

#[derive(Debug)]
pub enum CliError {
    CarcaraError(carcara::Error),
    CantInferProblemFile(PathBuf),
    InvalidSliceId(String),
}

pub type CliResult<T> = Result<T, CliError>;

// TODO: this does not respect `--no-color`
fn pretty_error(
    f: &mut fmt::Formatter,
    error: impl fmt::Display,
    file: &Path,
    pos: Option<Position>,
    more_info: Option<impl fmt::Display>,
) -> fmt::Result {
    writeln!(f, "{}", error)?;
    write!(
        f,
        "  {} in file {}",
        Color::Blue.paint("-->"),
        Color::Blue.underline().paint(file.to_string_lossy()),
    )?;
    if let Some((line, column)) = pos {
        writeln!(f, ":{}:{}", line, column)?;
    } else {
        writeln!(f)?;
    }
    if let Some(info) = more_info {
        writeln!(f, "  {} {}", Style::new().bold().paint("note:"), info)?;
    }
    Ok(())
}

impl From<carcara::Error> for CliError {
    fn from(e: carcara::Error) -> Self {
        Self::CarcaraError(e)
    }
}

impl fmt::Display for CliError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use carcara::Error;
        match self {
            CliError::CarcaraError(Error::Io { inner, file }) => {
                pretty_error(f, "IO error", file, None, Some(inner))
            }
            CliError::CarcaraError(Error::Parser(e, pos, file)) => {
                pretty_error(f, e, file, Some(*pos), None::<String>)
            }
            CliError::CarcaraError(Error::Checker { inner, rule, step, file }) => {
                let info = format!(
                    "checking failed on step {} with rule {}",
                    Color::Yellow.paint(&**step),
                    Color::Yellow.paint(&**rule),
                );
                pretty_error(f, inner, file, None, Some(info))
            }
            CliError::CarcaraError(Error::DoesNotReachEmptyClause { file }) => {
                let e = "proof does not conclude empty clause";
                pretty_error(f, e, file, None, None::<String>)
            }
            CliError::CarcaraError(Error::Elaborator { inner, rule, step, pass, file }) => {
                let pass = match pass {
                    ElaborationPass::Polyeq => "polyeq",
                    ElaborationPass::Hole => "hole",
                    ElaborationPass::Local => "local",
                    ElaborationPass::Uncrowd => "uncrowd",
                    ElaborationPass::Reordering => "reordering",
                    ElaborationPass::SatRefutation => "sat-refutation",
                };
                let info = format!(
                    "elaboration failed during {} elaboration pass, on step {} with rule {}",
                    Color::Yellow.paint(pass),
                    Color::Yellow.paint(&**step),
                    Color::Yellow.paint(&**rule),
                );
                pretty_error(f, inner, file, None, Some(info))
            }
            CliError::CantInferProblemFile(p) => {
                write!(f, "can't infer problem file: {}", p.display())
            }
            CliError::InvalidSliceId(id) => write!(f, "invalid id for slice: {}", id),
        }
    }
}
