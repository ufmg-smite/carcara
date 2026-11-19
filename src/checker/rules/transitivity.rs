use super::{CheckerError, RuleArgs, RuleResult, assert_clause_len, get_premise_term};
use crate::{ast::*, checker::error::rassert};

/// Function to find a transitive chain given a conclusion equality and a series of premise
/// equalities.
///
/// Inside a subproof, the context substitution σ only applies to the left-hand side of each
/// equality, so the premises `(= s t)` and `(= t u)` actually mean `σ(s) = t` and `σ(t) = u`. They
/// only chain into `σ(s) = u` if `t` is fixed by σ, that is, if `σ(t) = t`. For the same reason, a
/// premise can only be used in reverse if both of its terms are fixed, and a conclusion `(= a a)`
/// is only trivially valid if `a` is fixed. The `side_condition` function checks if a term is fixed
/// by σ.
fn find_chain(
    conclusion: (&Rc<Term>, &Rc<Term>),
    premises: &mut [(&Rc<Term>, &Rc<Term>)],
    mut side_condition: impl FnMut(&Rc<Term>) -> bool,
) -> RuleResult {
    let (mut current, target) = conclusion;

    // When the conclusion is of the form (= a a), it is trivially valid
    if current == target && side_condition(current) {
        return Ok(());
    }

    let mut used = 0;
    loop {
        // Find in the remaining premises, if it exists, an equality such that one of its terms is
        // equal to the current term in the chain. The other term of this equality is the next term
        // in the chain
        let (index, next) = premises[used..]
            .iter()
            .enumerate()
            .find_map(|(i, &(t, u))| {
                if t == current {
                    Some((i, u))
                // for flipped equalities, we also require that both terms fulfill the side
                // condition, since the trans step would encode an implicity symm
                } else if u == current && side_condition(t) && side_condition(u) {
                    Some((i, t))
                } else {
                    None
                }
            })
            .ok_or_else(|| {
                let (a, b) = conclusion;
                CheckerError::BrokenTransitivityChain(a.clone(), b.clone())
            })?;

        // We remove the found equality from the remaining premises by swapping it with the first
        // of them
        premises.swap(used, used + index);
        used += 1;

        if next == target {
            return Ok(());
        }
        // `next` is now in the middle of the chain
        rassert!(
            side_condition(next),
            CheckerError::TransitivityTermNotFixed(next.clone())
        );
        current = next;
    }
}

pub fn eq_transitive(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 2..)?;

    // The last term in the conclusion clause should be an equality, and it will be the conclusion
    // of the transitive chain
    let chain_conclusion = match_term_err!((= t u) = conclusion.last().unwrap())?;

    // The first `conclusion.len()` - 1 terms in the conclusion clause must be a sequence of
    // inequalities, and they will be the premises of the transitive chain
    let mut premises: Vec<_> = conclusion[..conclusion.len() - 1]
        .iter()
        .map(|term| match_term_err!((not (= t u)) = term))
        .collect::<Result<_, _>>()?;

    find_chain(chain_conclusion, &mut premises, |_| true)
}

pub fn trans(
    RuleArgs {
        conclusion, premises, pool, context, ..
    }: RuleArgs,
) -> RuleResult {
    assert_clause_len(conclusion, 1)?;

    let conclusion = match_term_err!((= t u) = &conclusion[0])?;
    let mut premises: Vec<_> = premises
        .iter()
        .map(|premise| match_term_err!((= t u) = get_premise_term(premise)?))
        .collect::<Result<_, _>>()?;

    find_chain(conclusion, &mut premises, |t| context.apply(pool, t) == *t)
}
