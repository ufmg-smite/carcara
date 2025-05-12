use super::{assert_clause_len, assert_eq, CheckerError, RuleArgs, RuleResult};
use crate::ast::*;

pub fn eq_reflexive(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let (a, b) = match_term_err!((= a b) = &conclusion[0])?;
    assert_eq(a, b)
}

pub fn refl(
    RuleArgs {
        conclusion,
        pool,
        context,
        polyeq_time,
        ..
    }: RuleArgs,
) -> RuleResult {
    assert_clause_len(conclusion, 1)?;

    let (left, right) = match_term_err!((= l r) = &conclusion[0])?;

    // If the two terms are directly identical, we don't need to do any more work. We make sure to
    // do this check before we try to get the context substitution, because `refl` can be used
    // outside of any subproof
    if alpha_equiv(left, right, polyeq_time) {
        return Ok(());
    }

    if context.is_empty() {
        return Err(CheckerError::ReflexivityFailed(left.clone(), right.clone()));
    }

    // In some cases, the substitution is only applied to the left or the right term, and in some
    // cases it is applied to both. To cover all cases, we must check all three possibilities. We
    // don't compute the new left and right terms until they are needed, to avoid doing unnecessary
    // work
    let new_left = context.apply(pool, left);
    let result = alpha_equiv(&new_left, right, polyeq_time) || {
        let new_right = context.apply(pool, right);
        alpha_equiv(left, &new_right, polyeq_time)
            || alpha_equiv(&new_left, &new_right, polyeq_time)
    };
    rassert!(
        result,
        CheckerError::ReflexivityFailed(left.clone(), right.clone()),
    );
    Ok(())
}

pub fn strict_refl(RuleArgs { conclusion, pool, context, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;

    let (left, right) = match_term_err!((= l r) = &conclusion[0])?;

    if left == right {
        return Ok(());
    }
    if context.is_empty() {
        return Err(CheckerError::ReflexivityFailed(left.clone(), right.clone()));
    }

    // This follows the same logic as the `refl` function, but without using alpha equivalence
    let new_left = context.apply(pool, left);
    let result = new_left == *right || {
        let new_right = context.apply(pool, right);
        *left == new_right || new_left == new_right
    };
    rassert!(
        result,
        CheckerError::ReflexivityFailed(left.clone(), right.clone()),
    );
    Ok(())
}
