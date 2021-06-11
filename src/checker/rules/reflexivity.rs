use super::{to_option, RuleArgs};
use crate::ast::*;

pub fn eq_reflexive(RuleArgs { conclusion, .. }: RuleArgs) -> Option<()> {
    if conclusion.len() == 1 {
        let (a, b) = match_term!((= a b) = conclusion[0])?;
        to_option(a == b)
    } else {
        None
    }
}

pub fn refl(
    RuleArgs {
        conclusion,
        pool,
        context,
        ..
    }: RuleArgs,
) -> Option<()> {
    if conclusion.len() != 1 {
        return None;
    }

    let (left, right) = match_term!((= l r) = conclusion[0], RETURN_RCS)?;

    let new_left = pool.apply_context_substitutions(&left, context);
    let new_right = pool.apply_context_substitutions(&right, context);

    to_option(new_left == new_right)
}
