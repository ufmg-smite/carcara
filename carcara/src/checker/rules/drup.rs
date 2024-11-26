use super::{CheckerError, RuleArgs, RuleResult};
use crate::ast::*;
use crate::drup::*;

pub fn drup(
    RuleArgs { pool, conclusion, premises, args, .. }: RuleArgs,
) -> RuleResult {
    let premises: Vec<&[Rc<Term>]> = premises
        .iter()
        .map(|p| p.clause)
        .map(|p| p)
        .collect();


    match check_drup(pool, conclusion, premises.as_slice(), args) {
        Ok(_) => Ok(()),
        Err(err) => Err(CheckerError::DratFormatError(err))
    }
}
