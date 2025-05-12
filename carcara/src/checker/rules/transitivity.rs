use super::{assert_clause_len, get_premise_term, CheckerError, RuleArgs, RuleResult};
use crate::ast::*;

/// Function to find a transitive chain given a conclusion equality and a series of premise
/// equalities.
fn find_chain(
    conclusion: (&Rc<Term>, &Rc<Term>),
    premises: &mut [(&Rc<Term>, &Rc<Term>)],
) -> RuleResult {
    // When the conclusion is of the form (= a a), it is trivially valid
    if conclusion.0 == conclusion.1 {
        return Ok(());
    }

    // Find in the premises, if it exists, an equality such that one of its terms is equal to the
    // first term in the conclusion. Possibly reorder this equality so the matching term is the
    // first one
    let (index, eq) = premises
        .iter()
        .enumerate()
        .find_map(|(i, &(t, u))| {
            if t == conclusion.0 {
                Some((i, (t, u)))
            } else if u == conclusion.0 {
                Some((i, (u, t)))
            } else {
                None
            }
        })
        .ok_or_else(|| {
            let (a, b) = conclusion;
            CheckerError::BrokenTransitivityChain(a.clone(), b.clone())
        })?;

    // We remove the found equality by swapping it with the first element in `premises`.  The new
    // premises will then be all elements after the first
    premises.swap(0, index);

    // The new conclusion will be the terms in the conclusion and the found equality that didn't
    // match. For example, if the conclusion was (= a d) and we found in the premises (= a b), the
    // new conclusion will be (= b d)
    find_chain((eq.1, conclusion.1), &mut premises[1..])
}

pub fn eq_transitive(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 3..)?;

    // The last term in the conclusion clause should be an equality, and it will be the conclusion
    // of the transitive chain
    let chain_conclusion = match_term_err!((= t u) = conclusion.last().unwrap())?;

    // The first `conclusion.len()` - 1 terms in the conclusion clause must be a sequence of
    // inequalities, and they will be the premises of the transitive chain
    let mut premises: Vec<_> = conclusion[..conclusion.len() - 1]
        .iter()
        .map(|term| match_term_err!((not (= t u)) = term))
        .collect::<Result<_, _>>()?;

    find_chain(chain_conclusion, &mut premises)
}

pub fn trans(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;

    let conclusion = match_term_err!((= t u) = &conclusion[0])?;
    let mut premises: Vec<_> = premises
        .iter()
        .map(|premise| match_term_err!((= t u) = get_premise_term(premise)?))
        .collect::<Result<_, _>>()?;

    find_chain(conclusion, &mut premises)
}
