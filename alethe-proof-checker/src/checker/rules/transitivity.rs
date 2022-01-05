use super::{
    assert_clause_len, get_premise_term, CheckerError, ProofBuilder, RuleArgs, RuleResult,
};
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
    // inequalites, and they will be the premises of the transitive chain
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

/// Similar to `find_chain`, but reorders the step premises vector to match the found chain
fn reconstruct_chain(
    conclusion: (&Rc<Term>, &Rc<Term>),
    premise_equalities: &mut [(&Rc<Term>, &Rc<Term>)],
    premises: &mut [(usize, usize)],
    should_flip: &mut Vec<bool>,
) -> RuleResult {
    if conclusion.0 == conclusion.1 {
        return Ok(());
    }

    let (index, next_link) = premise_equalities
        .iter()
        .enumerate()
        .find_map(|(i, &(t, u))| {
            if t == conclusion.0 {
                should_flip.push(false);
                Some((i, u))
            } else if u == conclusion.0 {
                should_flip.push(true);
                Some((i, t))
            } else {
                None
            }
        })
        .ok_or_else(|| {
            let (a, b) = conclusion;
            CheckerError::BrokenTransitivityChain(a.clone(), b.clone())
        })?;

    premise_equalities.swap(0, index);
    premises.swap(0, index);

    reconstruct_chain(
        (next_link, conclusion.1),
        &mut premise_equalities[1..],
        &mut premises[1..],
        should_flip,
    )
}

pub fn reconstruct_trans(
    RuleArgs { conclusion, premises, pool, .. }: RuleArgs,
    command_index: String,
    builder: &mut ProofBuilder,
) -> RuleResult {
    assert_clause_len(conclusion, 1)?;

    let conclusion_equality = match_term_err!((= t u) = &conclusion[0])?;
    let mut premise_equalities: Vec<_> = premises
        .iter()
        .map(|premise| match_term_err!((= t u) = get_premise_term(premise)?))
        .collect::<Result<_, _>>()?;

    let mut new_premises: Vec<_> = premises.iter().map(|p| p.premise_index).collect();
    let mut should_flip = Vec::with_capacity(new_premises.len());
    reconstruct_chain(
        conclusion_equality,
        &mut premise_equalities,
        &mut new_premises,
        &mut should_flip,
    )?;

    // If there are any premises that need flipping, we need to introduce `symm` steps to flip the
    // needed equalities
    let mut index_in_subproof = 0;
    for i in 0..new_premises.len() {
        // The lenght of `should_flip` may be smaller than that of `new_premises`. This can happen
        // if there are premises in the step which are not needed to complete the transitivity
        // chain. In that case, we consider that theses premises don't need flipping. Ideally, we
        // should remove them in the reconstructed step.
        let should_flip = should_flip.get(i) == Some(&true);
        new_premises[i] = if should_flip {
            let (a, b) = premise_equalities[i];
            index_in_subproof += 1;
            builder.add_symm_step(
                pool,
                new_premises[i],
                (a.clone(), b.clone()),
                // TODO: Avoid collisions when creating this index
                format!("{}.t{}", command_index, index_in_subproof),
            )
        } else {
            // If the premise didn't need flipping, we just need to map its index to the new
            // index in the reconstructed proof
            builder.map_index(new_premises[i])
        };
    }

    let reconstructed = ProofStep {
        index: command_index,
        clause: conclusion.into(),
        rule: "trans".into(),
        premises: new_premises,
        args: Vec::new(),
        discharge: Vec::new(),
    };
    builder.add_step(reconstructed, false);
    Ok(())
}

#[cfg(test)]
mod tests {
    #[test]
    fn eq_transitive() {
        test_cases! {
            definitions = "
                (declare-sort T 0)
                (declare-fun a () T)
                (declare-fun b () T)
                (declare-fun c () T)
                (declare-fun d () T)
                (declare-fun e () T)
            ",
            "Simple working examples" {
                "(step t1 (cl (not (= a b)) (not (= b c)) (= a c)) :rule eq_transitive)": true,

                "(step t1 (cl (not (= a b)) (not (= b c)) (not (= c d)) (= a d))
                    :rule eq_transitive)": true,

                "(step t1 (cl (not (= a a)) (not (= a a)) (= a a)) :rule eq_transitive)": true,
            }
            "Inequality terms in different orders" {
                "(step t1 (cl (not (= a b)) (not (= c b)) (not (= c d)) (= d a))
                    :rule eq_transitive)": true,

                "(step t1 (cl (not (= b a)) (not (= c b)) (not (= d c)) (= a d))
                    :rule eq_transitive)": true,
            }
            "Clause term is not an inequality" {
                "(step t1 (cl (= a b) (not (= b c)) (= a c)) :rule eq_transitive)": false,

                "(step t1 (cl (not (= a b)) (= b c) (= a c)) :rule eq_transitive)": false,
            }
            "Final term is not an equality" {
                "(step t1 (cl (not (= a b)) (not (= b c)) (not (= a c)))
                    :rule eq_transitive)": false,
            }
            "Clause is too small" {
                "(step t1 (cl (not (= a b)) (= a b)) :rule eq_transitive)": false,
            }
            "Clause terms in different orders" {
                "(step t1 (cl (not (= a b)) (not (= c d)) (not (= b c)) (= a d))
                    :rule eq_transitive)": true,

                "(step t1 (cl (not (= c d)) (not (= b c)) (not (= a b)) (= a d))
                    :rule eq_transitive)": true,
            }
            "Clause doesn't form transitive chain" {
                "(step t1 (cl (not (= a b)) (not (= c d)) (= a d)) :rule eq_transitive)": false,

                "(step t1 (cl (not (= a b)) (not (= b b)) (not (= c d)) (= a d))
                    :rule eq_transitive)": false,

                "(step t1 (cl (not (= a b)) (not (= b c)) (not (= c d)) (= a e))
                    :rule eq_transitive)": false,

                "(step t1 (cl (not (= a b)) (not (= b e)) (not (= b c)) (= a c))
                    :rule eq_transitive)": false,
            }
        }
    }

    #[test]
    fn trans() {
        test_cases! {
            definitions = "
                (declare-sort T 0)
                (declare-fun a () T)
                (declare-fun b () T)
                (declare-fun c () T)
                (declare-fun d () T)
                (declare-fun e () T)
            ",
            "Simple working examples" {
                "(assume h1 (= a b)) (assume h2 (= b c))
                (step t3 (cl (= a c)) :rule trans :premises (h1 h2))": true,

                "(assume h1 (= a b)) (assume h2 (= b c)) (assume h3 (= c d))
                (step t4 (cl (= a d)) :rule trans :premises (h1 h2 h3))": true,

                "(assume h1 (= a a))
                (step t2 (cl (= a a)) :rule trans :premises (h1))": true,
            }
            "Premises in different orders" {
                "(assume h1 (= a b)) (assume h2 (= c d)) (assume h3 (= b c))
                (step t4 (cl (= a d)) :rule trans :premises (h1 h2 h3))": true,

                "(assume h1 (= c d)) (assume h2 (= b c)) (assume h3 (= a b))
                (step t4 (cl (= a d)) :rule trans :premises (h1 h2 h3))": true,
            }
            "Prmise term is not an equality" {
                "(assume h1 (= a b)) (assume h2 (not (= b c))) (assume h3 (= c d))
                (step t4 (cl (= a d)) :rule trans :premises (h1 h2 h3))": false,
            }
            "Conclusion clause is of the wrong form" {
                "(assume h1 (= a b)) (assume h2 (= b c))
                (step t3 (cl (not (= a c))) :rule trans :premises (h1 h2))": false,

                "(assume h1 (= a b)) (assume h2 (= b c))
                (step t3 (cl (= a c) (= c a)) :rule trans :premises (h1 h2))": false,
            }
        }
    }
}
