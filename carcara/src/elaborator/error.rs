use crate::{resolution::ResolutionError, CheckerError};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum ElaborationError {
    #[error("trying to elaborate invalid step: {0}")]
    Checker(#[from] CheckerError),

    #[error(transparent)]
    LiaGeneric(#[from] crate::elaborator::lia_generic::LiaGenericError),

    #[error(transparent)]
    Hole(#[from] crate::elaborator::hole::HoleError),

    #[error("could not infer pivots for resolution step")]
    CouldNotInferPivots,

    #[error("cannot uncrowd resolution without pivots being provided")]
    UncrowdMissingPivots,
}

impl ElaborationError {
    /// Converts the [`ElaborationError`] into an [`Error`] by locating it to a specific step node.
    pub fn at(self, step: &crate::ast::StepNode) -> crate::Error {
        crate::Error::Elaborator {
            inner: self,
            rule: step.rule.as_str().into(),
            step: step.id.as_str().into(),
        }
    }
}

impl From<ResolutionError> for ElaborationError {
    fn from(value: ResolutionError) -> Self {
        Self::Checker(value.into())
    }
}
