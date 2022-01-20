use super::{
    assert_clause_len, get_premise_term, CheckerError, Reconstructor, RuleArgs, RuleResult,
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

/// Similar to `find_chain`, but reorders the a premises vector to match the found chain. In
/// `trans`, this is used to reorder the step premises vector; in `eq_transitive`, it is used to
/// reorder the clause. This returns a boolean indicating whether any reordering was needed, a
/// `usize` indicating how many premises are needed to prove the conclusion, and a vector of indices
/// of the premise equalities that need to be flipped.
fn reconstruct_chain<'a, T>(
    mut conclusion: (&'a Rc<Term>, &'a Rc<Term>),
    premise_equalities: &mut [(&'a Rc<Term>, &'a Rc<Term>)],
    premises: &mut [T],
) -> Result<(bool, usize, Vec<usize>), CheckerError> {
    let mut reordered = false;
    let mut should_flip = Vec::with_capacity(premise_equalities.len());
    let mut i = 0;
    loop {
        if conclusion.0 == conclusion.1 {
            return Ok((reordered, i, should_flip));
        }

        let (found_index, next_link) = premise_equalities[i..]
            .iter()
            .enumerate()
            .find_map(|(j, &(t, u))| {
                if t == conclusion.0 {
                    Some((j + i, u))
                } else if u == conclusion.0 {
                    should_flip.push(i);
                    Some((j + i, t))
                } else {
                    None
                }
            })
            .ok_or_else(|| {
                let (a, b) = conclusion;
                CheckerError::BrokenTransitivityChain(a.clone(), b.clone())
            })?;

        if found_index != i {
            premise_equalities.swap(i, found_index);
            premises.swap(i, found_index);
            reordered = true;
        }
        conclusion = (next_link, conclusion.1);
        i += 1;
    }
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

pub fn reconstruct_eq_transitive(
    RuleArgs { conclusion, pool, .. }: RuleArgs,
    command_id: String,
    reconstructor: &mut Reconstructor,
) -> RuleResult {
    assert_clause_len(conclusion, 3..)?;
    let n = conclusion.len();

    // The last term in the conclusion clause should be an equality, and it will be the conclusion
    // of the transitive chain
    let conclusion_equality = match_term_err!((= t u) = conclusion.last().unwrap())?;

    // The first `conclusion.len()` - 1 terms in the conclusion clause must be a sequence of
    // inequalites, and they will be the premises of the transitive chain
    let mut premise_equalities: Vec<_> = conclusion[..n - 1]
        .iter()
        .map(|term| match_term_err!((not (= t u)) = term))
        .collect::<Result<_, _>>()?;

    let mut new_clause: Vec<_> = conclusion.to_vec();
    let (needs_reordering, num_needed, should_flip) = reconstruct_chain(
        conclusion_equality,
        &mut premise_equalities,
        &mut new_clause[..n - 1],
    )?;

    if !needs_reordering && num_needed == n - 1 && should_flip.is_empty() {
        reconstructor.signal_unchanged();
        return Ok(());
    }

    for &i in &should_flip {
        new_clause[i] = if let Some((a, b)) = match_term!((not (= a b)) = &new_clause[i]) {
            build_term!(pool, (not (= {b.clone()} {a.clone()})))
        } else {
            panic!()
        };
    }

    let not_needed = if num_needed == n - 1 {
        Vec::new()
    } else {
        let conclusion = new_clause.pop().unwrap();
        let not_needed = new_clause.split_off(num_needed);
        new_clause.push(conclusion);
        not_needed
    };

    let new_eq_transitive_step = ProofStep {
        id: reconstructor.get_new_id(&command_id),
        clause: new_clause.clone(),
        rule: "eq_transitive".to_owned(),
        premises: Vec::new(),
        args: Vec::new(),
        discharge: Vec::new(),
    };
    let new_eq_transitive_step = reconstructor.add_new_step(new_eq_transitive_step);
    let mut latest_step_index = new_eq_transitive_step;
    let mut latest_clause = new_clause;

    if !should_flip.is_empty() {
        let (clause, step) = flip_eq_transitive_premises(
            pool,
            reconstructor,
            new_eq_transitive_step,
            &latest_clause,
            &command_id,
            &should_flip,
        );
        latest_step_index = step;
        latest_clause = clause;
    }

    if !not_needed.is_empty() {
        let mut clause = latest_clause;
        clause.extend(not_needed.into_iter());
        let or_intro_step = ProofStep {
            id: reconstructor.get_new_id(&command_id),
            clause,
            rule: "or_intro".to_owned(),
            premises: vec![latest_step_index],
            args: Vec::new(),
            discharge: Vec::new(),
        };
        latest_step_index = reconstructor.add_new_step(or_intro_step);
    }

    reconstructor.push_reconstructed_step(ProofStep {
        id: command_id,
        clause: conclusion.to_vec(),
        rule: "reordering".to_owned(),
        premises: vec![latest_step_index],
        args: Vec::new(),
        discharge: Vec::new(),
    });
    Ok(())
}

fn flip_eq_transitive_premises(
    pool: &mut TermPool,
    reconstructor: &mut Reconstructor,
    new_eq_transitive_step: (usize, usize),
    new_clause: &[Rc<Term>],
    original_id: &str,
    should_flip: &[usize],
) -> (Vec<Rc<Term>>, (usize, usize)) {
    let resolution_pivots: Vec<_> = should_flip
        .iter()
        .map(|&i| {
            let (a, b) = match_term!((not (= a b)) = new_clause[i]).unwrap();
            let pivot = build_term!(pool, (= {a.clone()} {b.clone()}));
            let to_introduce = build_term!(pool, (not (= {b.clone()} {a.clone()})));
            let clause = vec![to_introduce.clone(), pivot.clone()];
            let new_step = ProofStep {
                id: reconstructor.get_new_id(original_id),
                clause,
                rule: "eq_symmetric".to_owned(),
                premises: Vec::new(),
                args: Vec::new(),
                discharge: Vec::new(),
            };
            (reconstructor.add_new_step(new_step), pivot, to_introduce)
        })
        .collect();

    let clause = {
        let should_flip = {
            let mut new = vec![false; new_clause.len()];
            for &i in should_flip {
                new[i] = true;
            }
            new
        };
        let mut original: Vec<_> = new_clause
            .iter()
            .enumerate()
            .filter(|&(i, _)| !should_flip[i])
            .map(|(_, t)| t.clone())
            .collect();
        original.extend(
            resolution_pivots
                .iter()
                .map(|(_, _, to_introduce)| to_introduce.clone()),
        );
        original
    };
    let mut premises = vec![new_eq_transitive_step];
    premises.extend(resolution_pivots.iter().map(|&(index, _, _)| index));
    let args: Vec<_> = resolution_pivots
        .into_iter()
        .flat_map(|(_, pivot, _)| [pivot, pool.bool_false()])
        .map(ProofArg::Term)
        .collect();

    let final_step = ProofStep {
        id: reconstructor.get_new_id(original_id),
        clause: clause.clone(),
        rule: "strict_resolution".to_owned(),
        premises,
        args,
        discharge: Vec::new(),
    };
    (clause, reconstructor.add_new_step(final_step))
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

pub fn reconstruct_trans(
    RuleArgs { conclusion, premises, pool, .. }: RuleArgs,
    command_id: String,
    reconstructor: &mut Reconstructor,
) -> RuleResult {
    assert_clause_len(conclusion, 1)?;

    let conclusion_equality = match_term_err!((= t u) = &conclusion[0])?;
    let mut premise_equalities: Vec<_> = premises
        .iter()
        .map(|premise| match_term_err!((= t u) = get_premise_term(premise)?))
        .collect::<Result<_, _>>()?;

    let mut new_premises: Vec<_> = premises.iter().map(|p| p.index).collect();
    let (_, num_needed, should_flip) = reconstruct_chain(
        conclusion_equality,
        &mut premise_equalities,
        &mut new_premises,
    )?;

    // If there are any premises in the step which are not needed to complete the transitivity
    // chain, we simply remove them in the reconstructed step.
    new_premises.truncate(num_needed);

    // To make things easier later, we change `should_flip` to be a vector of booleans instead of a
    // vector of indices. Now, `should_flip[i]` indicates whether the i-th premise needs to be
    // flipped.
    let should_flip = {
        let mut new = vec![false; num_needed];
        for i in should_flip {
            new[i] = true;
        }
        new
    };

    // If there are any premises that need flipping, we need to introduce `symm` steps to flip the
    // needed equalities
    for i in 0..new_premises.len() {
        new_premises[i] = if should_flip[i] {
            let (a, b) = premise_equalities[i];
            let id = reconstructor.get_new_id(&command_id);
            reconstructor.add_symm_step(pool, new_premises[i], (a.clone(), b.clone()), id)
        } else {
            // If the premise didn't need flipping, we just need to map its index to the new
            // index in the reconstructed proof
            reconstructor.map_index(new_premises[i])
        };
    }

    reconstructor.push_reconstructed_step(ProofStep {
        id: command_id,
        clause: conclusion.into(),
        rule: "trans".into(),
        premises: new_premises,
        args: Vec::new(),
        discharge: Vec::new(),
    });
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
