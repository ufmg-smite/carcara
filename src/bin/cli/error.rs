use carcara::{elaborator::ElaborationPass, parser::Position};
use owo_colors::{OwoColorize, Style};
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

impl CliError {
    pub fn display(&self, use_color: bool) -> impl fmt::Display {
        DisplayError { error: self, use_color }
    }
}

pub type CliResult<T> = Result<T, CliError>;

fn pretty_error(
    f: &mut fmt::Formatter,
    error: impl fmt::Display,
    file: &Path,
    pos: Option<Position>,
    more_info: Option<impl fmt::Display>,
    use_color: bool,
) -> fmt::Result {
    writeln!(f, "{error}")?;
    let arrow = "-->".style(crate::style_if(use_color, Style::blue));
    write!(
        f,
        "  {arrow} in file {}",
        file.display()
            .style(crate::style_if(use_color, |s| s.blue().underline())),
    )?;
    if let Some((line, column)) = pos {
        writeln!(f, ":{}:{}", line, column)?;
    } else {
        writeln!(f)?;
    }
    if let Some(info) = more_info {
        let note = "note:".style(crate::style_if(use_color, Style::bold));
        writeln!(f, "  {note} {info}")?;
    }
    Ok(())
}

impl From<carcara::Error> for CliError {
    fn from(e: carcara::Error) -> Self {
        Self::CarcaraError(e)
    }
}

struct DisplayError<'a> {
    error: &'a CliError,
    use_color: bool,
}

impl<'a> fmt::Display for DisplayError<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use carcara::Error;

        let yellow = crate::style_if(self.use_color, Style::yellow);

        match self.error {
            CliError::CarcaraError(Error::Io { inner, file }) => {
                pretty_error(f, "IO error", file, None, Some(inner), self.use_color)
            }
            CliError::CarcaraError(Error::Parser(e, pos, file)) => {
                pretty_error(f, e, file, Some(*pos), None::<String>, self.use_color)
            }
            CliError::CarcaraError(Error::Checker { inner, rule, step, file }) => {
                let info = format!(
                    "checking failed on step {} with rule {}",
                    step.style(yellow),
                    rule.style(yellow),
                );
                pretty_error(f, inner, file, None, Some(info), self.use_color)
            }
            CliError::CarcaraError(Error::DoesNotReachEmptyClause { file }) => {
                let e = "proof does not conclude empty clause";
                pretty_error(f, e, file, None, None::<String>, self.use_color)
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
                    pass.style(yellow),
                    step.style(yellow),
                    rule.style(yellow),
                );
                pretty_error(f, inner, file, None, Some(info), self.use_color)
            }
            CliError::CantInferProblemFile(p) => {
                write!(f, "can't infer problem file: {}", p.display())
            }
            CliError::InvalidSliceId(id) => write!(f, "invalid id for slice: {}", id),
        }
    }
}
