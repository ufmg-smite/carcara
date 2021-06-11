use super::{get_clause_from_command, to_option, RuleArgs};
use crate::ast::*;
use std::collections::HashSet;

pub fn resolution(
    RuleArgs {
        conclusion,
        premises,
        ..
    }: RuleArgs,
) -> Option<()> {
    /// Removes all leading negations in a term and returns how many there were.
    fn remove_negations(mut term: &Term) -> (i32, &Term) {
        let mut n = 0;
        while let Some(t) = term.remove_negation() {
            term = t;
            n += 1;
        }
        (n, term)
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
    let conclusion: HashSet<_> = conclusion
        .iter()
        .map(|t| remove_negations(t.as_ref()))
        .collect();

    // The working clause contains the terms from the conclusion clause that we already encountered
    let mut working_clause = HashSet::new();

    // The pivots are the encountered terms that are not present in the conclusion clause, and so
    // should be removed
    let mut pivots = HashSet::new();

    for command in premises {
        let premise_clause = get_clause_from_command(command);
        for term in premise_clause {
            let (n, inner) = remove_negations(term.as_ref());

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
            // remove it. Otherwise, we insert the encountered term in the working clause or the
            // pivots set, depending on wether it is present in the conclusion clause or not
            let removed = n > 0 && pivots.remove(&below) || pivots.remove(&above);
            if !removed {
                if conclusion.contains(&(n, inner)) {
                    working_clause.insert((n, inner));
                } else {
                    pivots.insert((n, inner));
                }
            }
        }
    }

    // In some cases, when the result of the resolution is just one term, it may appear in the
    // conclusion clause with an even number of leading negations added to it. The following is an
    // example of this, adapted from a generated proof:
    //
    //     (step t1 (cl (not e)) :rule irrelevant)
    //     (step t2 (cl (= (not e) (not (not f)))) :rule irrelevant)
    //     (step t3 (cl (not (= (not e) (not (not f)))) e f) :rule irrelevant)
    //     (step t4 (cl (not (not f))) :rule resolution :premises (t1 t2 t3))
    //
    // Usually, we would expect the clause in the t4 step to be (cl f).
    if pivots.len() == 1 && conclusion.len() == 1 {
        let (i, pivot) = pivots.into_iter().next().unwrap();
        let (j, conclusion) = conclusion.into_iter().next().unwrap();
        return to_option(conclusion == pivot && (i % 2) == (j % 2));
    }

    // At the end, we expect all pivots to have been removed, and the working clause to be equal to
    // the conclusion clause
    to_option(pivots.is_empty() && working_clause == conclusion)
}

pub fn contraction(
    RuleArgs {
        conclusion,
        premises,
        ..
    }: RuleArgs,
) -> Option<()> {
    if premises.len() != 1 {
        return None;
    }

    let premise_clause = get_clause_from_command(premises[0]);

    // This set will be populated with the terms we enconter as we iterate through the premise
    let mut encountered = HashSet::<&Term>::with_capacity(premise_clause.len());
    let mut conclusion_iter = conclusion.iter();

    for t in premise_clause {
        // `HashSet::insert` returns true if the inserted element was not in the set
        let is_new_term = encountered.insert(t.as_ref());

        // If the term in the premise clause has not been encountered before, we advance the
        // conclusion clause iterator, and check if its next term is the encountered term
        if is_new_term && conclusion_iter.next() != Some(t) {
            return None;
        }
    }

    // At the end, the conclusion clause iterator must be empty, meaning all terms in the
    // conclusion are in the premise
    to_option(conclusion_iter.next().is_none())
}
