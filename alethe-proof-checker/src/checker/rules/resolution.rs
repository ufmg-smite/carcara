use super::{
    assert_clause_len, assert_is_bool_constant, assert_is_expected, assert_num_premises, RuleArgs,
    RuleResult,
};
use crate::{ast::*, checker::error::ResolutionError, utils::DedupIterator};
use ahash::{AHashMap, AHashSet};
use std::collections::hash_map::Entry;

/// Undoes the transformation done by `Rc<Term>::remove_all_negations`.
fn unremove_all_negations(pool: &mut TermPool, (n, term): (i32, &Rc<Term>)) -> Rc<Term> {
    let mut term = term.clone();
    for _ in 0..n {
        term = build_term!(pool, (not { term }));
    }
    term
}

pub fn resolution(RuleArgs { conclusion, premises, pool, .. }: RuleArgs) -> RuleResult {
    // In some cases, this rule is used with a single premise `(not true)` to justify an empty
    // conclusion clause
    if conclusion.is_empty() && premises.len() == 1 {
        if let [t] = premises[0].clause {
            if match_term!((not true) = t).is_some() {
                return Ok(());
            }
        }
    }

    // When checking this rule, we must look at what the conclusion clause looks like in order to
    // determine the pivots. The reason for that is because there is no other way to know which
    // terms should be removed in a given binary resolution step. Consider the following example,
    // adapted from an actual generated proof:
    //
    //     (step t1 (cl (not q) (not (not p)) (not p)) :rule irrelevant)
    //     (step t2 (cl (not (not (not p))) p) :rule irrelevant)
    //     (step t3 (cl (not q) p (not p)) :rule resolution :premises (t1 t2))
    //
    // Without looking at the conclusion, it is unclear if the (not p) term should be removed by
    // the p term, if the (not (not p)) should be removed by the (not (not (not p))), or both. We
    // can only determine this by looking at the conlcusion and using it to derive the pivots.
    let conclusion: AHashSet<_> = conclusion
        .iter()
        .map(|t| t.remove_all_negations())
        .map(|(n, t)| (n as i32, t))
        .collect();

    // The working clause contains the terms from the conclusion clause that we already encountered
    let mut working_clause = AHashSet::new();

    // The pivots are the encountered terms that are not present in the conclusion clause, and so
    // should be removed. After being used to eliminate a term, a pivot can still be used to
    // eliminate other terms. Because of that, we represent the pivots as a hash map to a boolean,
    // which represents if the pivot was already eliminated or not. At the end, this boolean should
    // be true for all pivots
    let mut pivots = AHashMap::new();

    for premise in premises {
        for term in premise.clause {
            let (n, inner) = term.remove_all_negations();
            let n = n as i32;

            // There are two possible negations of a term, with one leading negation added, or with
            // one leading negation removed (if the term had any in the first place)
            let below = (n - 1, inner);
            let above = (n + 1, inner);

            // First, if the encountered term should be in the conclusion, but is not yet in the
            // working clause, we insert it and don't try to remove it with a pivot
            if conclusion.contains(&(n, inner)) && !working_clause.contains(&(n, inner)) {
                working_clause.insert((n, inner));
                continue;
            }

            // If the negation of the encountered term is present in the pivots set, we simply
            // eliminate it. Otherwise, we insert the encountered term in the working clause or the
            // pivots set, depending on wether it is present in the conclusion clause or not
            let mut try_eliminate = |pivot| match pivots.entry(pivot) {
                Entry::Occupied(mut e) => {
                    e.insert(true);
                    true
                }
                Entry::Vacant(_) => false,
            };
            let eliminated = try_eliminate(below) || try_eliminate(above);
            if !eliminated {
                if conclusion.contains(&(n, inner)) {
                    working_clause.insert((n, inner));
                } else {
                    // If the term is not in the conclusion clause, it must be a pivot. If it was
                    // not already in the pivots set, we insert `false`, to indicate that it was
                    // not yet eliminated
                    pivots.entry((n, inner)).or_insert(false);
                }
            }
        }
    }

    // There are some special cases in the resolution rules that are valid, but leave a pivot
    // remaining
    let mut remaining_pivots = pivots.iter().filter(|&(_, eliminated)| !eliminated);

    if let Some(((i, pivot), _)) = remaining_pivots.next() {
        // There is a special case in the resolution rules that is valid, but leaves a pivot
        // remaining: when the result of the resolution is just the boolean constant `false`, it
        // may be implicitly eliminated. For example:
        //     (step t1 (cl p q false) :rule trust)
        //     (step t2 (cl (not p)) :rule trust)
        //     (step t3 (cl (not q)) :rule trust)
        //     (step t4 (cl) :rule resolution :premises (t1 t2 t3))
        if conclusion.is_empty() && *i == 0 && pivot.is_bool_false() {
            return Ok(());
        }

        // There is another, similar, special case: when the result of the resolution is just one
        // term, it may appear in the conclusion clause with an even number of leading negations
        // added to it. The following is an example of this, adapted from a generated proof:
        //     (step t1 (cl (not e)) :rule trust)
        //     (step t2 (cl (= (not e) (not (not f)))) :rule trust)
        //     (step t3 (cl (not (= (not e) (not (not f)))) e f) :rule trust)
        //     (step t4 (cl (not (not f))) :rule resolution :premises (t1 t2 t3))
        // Usually, we would expect the clause in the t4 step to be (cl f). This behaviour may be a
        // bug in veriT, but it is still logically sound and happens often enough that it is useful
        // to support it here
        if conclusion.len() == 1 {
            let (j, conclusion) = conclusion.into_iter().next().unwrap();
            if conclusion == *pivot && (i % 2) == (j % 2) {
                return Ok(());
            }
        }

        let pivot = unremove_all_negations(pool, (*i, pivot));
        Err(ResolutionError::RemainingPivot(pivot).into())
    } else {
        // This is the general case, where all pivots have been eliminated. In this case, the
        // working clause should be equal to the conclusion clause
        for t in conclusion {
            // By construction, the working clause is a subset of the conclusion. Therefore, we
            // only need to check that all terms in the conclusion are also in the working clause
            if !working_clause.contains(&t) {
                let t = unremove_all_negations(pool, t);
                return Err(ResolutionError::ResolutionMissingTerm(t).into());
            }
        }
        Ok(())
    }
}

pub fn tautology(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 1)?;
    assert_is_bool_constant(&conclusion[0], true)?;

    let premise = premises[0].clause;
    let mut seen = AHashSet::with_capacity(premise.len());
    let with_negations_removed = premise
        .iter()
        .map(|t| t.remove_all_negations_with_polarity());
    for (polarity, term) in with_negations_removed {
        if seen.contains(&(!polarity, term)) {
            return Ok(());
        }
        seen.insert((polarity, term));
    }
    Err(ResolutionError::TautologyFailed.into())
}

pub fn contraction(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;

    let expected: Vec<_> = premises[0].clause.iter().dedup().collect();
    assert_clause_len(conclusion, expected.len())?;

    for (t, u) in conclusion.iter().zip(expected) {
        assert_is_expected(t, u.clone())?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    #[test]
    fn resolution() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
                (declare-fun r () Bool)
                (declare-fun s () Bool)
            ",
            "Simple working examples" {
                "(assume h1 (not p))
                (step t2 (cl p q) :rule trust)
                (step t3 (cl q) :rule resolution :premises (h1 t2))": true,

                "(assume h1 (not p))
                (assume h2 (not q))
                (assume h3 (not r))
                (step t4 (cl p q r) :rule trust)
                (step t5 (cl) :rule resolution :premises (h1 h2 h3 t4))": true,

                "(assume h1 (not p))
                (assume h2 q)
                (step t3 (cl p (not q)) :rule trust)
                (step t4 (cl) :rule resolution :premises (h1 h2 t3))": true,
            }
            "Missing term in final clause" {
                "(assume h1 (not p))
                (step t2 (cl p q r) :rule trust)
                (step t3 (cl q) :rule resolution :premises (h1 t2))": false,
            }
            "Extra term in final clause" {
                "(assume h1 (not p))
                (step t2 (cl p q r) :rule trust)
                (step t3 (cl p q r) :rule resolution :premises (h1 t2))": false,
            }
            "Term appears in final clause with wrong polarity" {
                "(assume h1 (not p))
                (step t2 (cl p q r) :rule trust)
                (step t3 (cl (not q) r) :rule resolution :premises (h1 t2))": false,
            }
            "Duplicate term in final clause" {
                "(step t1 (cl q (not p)) :rule trust)
                (step t2 (cl p q r) :rule trust)
                (step t3 (cl q q r) :rule resolution :premises (t1 t2))": true,
            }
            "Terms with leading negations" {
                "(assume h1 (not p))
                (assume h2 (not (not p)))
                (assume h3 (not (not (not p))))
                (assume h4 (not (not (not (not p)))))
                (step t5 (cl) :rule resolution :premises (h1 h2))
                (step t6 (cl) :rule resolution :premises (h2 h3))
                (step t7 (cl (not p) (not (not (not p)))) :rule resolution :premises (h1 h3))
                (step t8 (cl (not p) (not (not (not (not p)))))
                    :rule resolution :premises (h1 h4))": true,
            }
            "Must use correct pivots" {
                "(step t1 (cl (not q) (not (not p)) (not p)) :rule trust)
                (step t2 (cl (not (not (not p))) p) :rule trust)
                (step t3 (cl (not q) p (not p)) :rule resolution :premises (t1 t2))": true,

                "(step t1 (cl (not q) (not (not p)) (not p)) :rule trust)
                (step t2 (cl (not (not (not p))) p) :rule trust)
                (step t3 (cl (not q) (not (not (not p))) (not (not p)))
                    :rule resolution :premises (t1 t2))": true,

                "(step t1 (cl (not q) (not (not p)) (not p)) :rule trust)
                (step t2 (cl (not (not (not p))) p) :rule trust)
                (step t3 (cl (not q) p (not p) (not (not (not p))) (not (not p)))
                    :rule resolution :premises (t1 t2))": true,
            }
            "Weird behaviour where leading negations sometimes are added to conclusion" {
                "(assume h1 (not p))
                (assume h2 (= (not p) (not (not q))))
                (step t3 (cl (not (= (not p) (not (not q)))) p q) :rule trust)
                (step t4 (cl (not (not q))) :rule resolution :premises (h1 h2 t3))": true,
            }
            "Premise is \"(not true)\" and leads to empty conclusion clause" {
                "(step t1 (cl (not true)) :rule trust)
                (step t2 (cl) :rule th_resolution :premises (t1))": true,
            }
            "Repeated premises" {
                "(step t1 (cl (not r)) :rule trust)
                (step t2 (cl p q r s) :rule trust)
                (step t3 (cl p q s) :rule th_resolution :premises (t1 t2 t2))": true,
            }
            "Implicit elimination of \"(cl false)\"" {
                "(step t1 (cl p q false) :rule trust)
                (step t2 (cl (not p)) :rule trust)
                (step t3 (cl (not q)) :rule trust)
                (step t4 (cl) :rule resolution :premises (t1 t2 t3))": true,

                // This implicit elimination is allowed, but not required
                "(step t1 (cl p q false) :rule trust)
                (step t2 (cl (not p)) :rule trust)
                (step t3 (cl (not q)) :rule trust)
                (step t4 (cl false) :rule resolution :premises (t1 t2 t3))": true,
            }
        }
    }

    #[test]
    fn tautology() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
                (declare-fun r () Bool)
                (declare-fun s () Bool)
            ",
            "Simple working examples" {
                "(step t1 (cl (not p) p) :rule trust)
                (step t2 (cl true) :rule tautology :premises (t1))": true,

                "(step t1 (cl p q (not q) r s) :rule trust)
                (step t2 (cl true) :rule tautology :premises (t1))": true,

                "(step t1 (cl p (not (not s)) q r (not (not (not s)))) :rule trust)
                (step t2 (cl true) :rule tautology  :premises (t1))": true,
            }
            "Conclusion is not \"true\"" {
                "(step t1 (cl p q (not q) r s) :rule trust)
                (step t2 (cl false) :rule tautology :premises (t1))": false,

                "(step t1 (cl p q (not q) r s) :rule trust)
                (step t2 (cl) :rule tautology :premises (t1))": false,
            }
            "Premise is not a tautology" {
                "(step t1 (cl p) :rule trust)
                (step t2 (cl true) :rule tautology :premises (t1))": false,

                "(step t1 (cl p (not (not s)) q r s) :rule trust)
                (step t2 (cl true) :rule tautology :premises (t1))": false,
            }
        }
    }

    #[test]
    fn contraction() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
                (declare-fun r () Bool)
                (declare-fun s () Bool)
            ",
            "Simple working examples" {
                "(step t1 (cl p q q r s s) :rule trust)
                (step t2 (cl p q r s) :rule contraction :premises (t1))": true,

                "(step t1 (cl p p p q q r s s s) :rule trust)
                (step t2 (cl p q r s) :rule contraction :premises (t1))": true,

                "(step t1 (cl p q r s) :rule trust)
                (step t2 (cl p q r s) :rule contraction :premises (t1))": true,
            }
            "Number of premises != 1" {
                "(step t1 (cl p q) :rule contraction)": false,

                "(assume h1 q)
                (assume h2 p)
                (step t3 (cl p q) :rule contraction :premises (h1 h2))": false,
            }
            "Premise is not a \"step\" command" {
                "(assume h1 q)
                (step t2 (cl q) :rule contraction :premises (h1))": true,
            }
            "Encountered wrong term" {
                "(step t1 (cl p p q) :rule trust)
                (step t2 (cl p r) :rule contraction :premises (t1))": false,
            }
            "Terms are not in correct order" {
                "(step t1 (cl p q q r) :rule trust)
                (step t2 (cl p r q) :rule contraction :premises (t1))": false,
            }
            "Conclusion is missing terms" {
                "(step t1 (cl p q q r) :rule trust)
                (step t2 (cl p r) :rule contraction :premises (t1))": false,

                "(step t1 (cl p p q r) :rule trust)
                (step t2 (cl p q) :rule contraction :premises (t1))": false,
            }
            "Conclusion has extra term at the end" {
                "(step t1 (cl p p q) :rule trust)
                (step t2 (cl p q r s) :rule contraction :premises (t1))": false,
            }
        }
    }
}
