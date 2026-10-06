use super::{CheckerError, RuleArgs, RuleResult, assert_clause_len};
use crate::ast::*;
use crate::drup::*;

pub fn drup(
    check_drat: bool,
    RuleArgs {
        pool, conclusion, premises, args, ..
    }: RuleArgs,
) -> RuleResult {
    if check_drat {
        // RAT additions only preserve satisfiability, not implication, so the only clause that
        // `drat` can soundly conclude is the empty clause
        assert_clause_len(conclusion, 0)?;
    }

    let premises: Vec<Rc<Term>> = premises
        .iter()
        .map(|p| p.clause)
        .map(|p| build_term!(pool, (cl[p.to_vec()])))
        .collect();

    let conclusion = build_term!(pool, (cl[conclusion.to_vec()]));

    match check_drup(pool, conclusion, premises.as_slice(), args, check_drat) {
        Ok(_) => Ok(()),
        Err(err) => Err(CheckerError::DrupFormatError(err)),
    }
}
