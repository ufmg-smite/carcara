use super::{CheckerError, RuleArgs, RuleResult, assert_clause_len, assert_eq};
use crate::{ast::*, checker::error::rassert};

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

    if context.is_empty() {
        rassert!(
            alpha_equiv(left, right, polyeq_time),
            CheckerError::ReflexivityFailed(left.clone(), right.clone()),
        );
        return Ok(());
    }

    // Inside a subproof, the context substitution σ should applied to the left term, but some solvers
    // (e.g. veriT) apply it to the right term instead, so we accept both `σ(left) = right` and
    // `left = σ(right)`.
    let new_left = context.apply(pool, left);
    let result = alpha_equiv(&new_left, right, polyeq_time) || {
        context.is_idempotent(pool) && {
            let new_right = context.apply(pool, right);
            alpha_equiv(left, &new_right, polyeq_time)
        }
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

    // Unlike the traditional `refl` function, we do not use alpha equivalence, and we only try to
    // apply the context on the left-hand side.
    let new_left = context.apply(pool, left);
    rassert!(
        new_left == *right,
        CheckerError::ReflexivityFailed(left.clone(), right.clone()),
    );
    Ok(())
}
