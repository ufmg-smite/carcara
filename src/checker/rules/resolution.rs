use super::{get_clause_from_command, to_option, RuleArgs};
use crate::ast::*;
use std::collections::HashSet;

/// Removes all leading negations in a term and returns how many there were.
fn remove_all_negations(mut term: &Term) -> (u32, &Term) {
    let mut n = 0;
    while let Some(t) = term.remove_negation() {
        term = t;
        n += 1;
    }
    (n, term)
}

pub fn resolution(
    RuleArgs {
        conclusion,
        premises,
        ..
    }: RuleArgs,
) -> Option<()> {
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
        .map(|t| remove_all_negations(t.as_ref()))
        .map(|(n, t)| (n as i32, t))
        .collect();

    // The working clause contains the terms from the conclusion clause that we already encountered
    let mut working_clause = HashSet::new();

    // The pivots are the encountered terms that are not present in the conclusion clause, and so
    // should be removed
    let mut pivots = HashSet::new();

    for command in premises {
        let premise_clause = get_clause_from_command(command);
        for term in premise_clause {
            let (n, inner) = remove_all_negations(term.as_ref());
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

pub fn tautology(
    RuleArgs {
        conclusion,
        premises,
        ..
    }: RuleArgs,
) -> Option<()> {
    if conclusion.len() != 1 || conclusion[0].try_as_var() != Some("true") || premises.len() != 1 {
        return None;
    }
    let premise = get_clause_from_command(premises[0]);
    let mut seen = HashSet::with_capacity(premise.len());
    let with_negations_removed = premise
        .iter()
        .map(|t| remove_all_negations(t.as_ref()))
        .map(|(n, t)| (n % 2 == 0, t));
    for (polarity, term) in with_negations_removed {
        if seen.contains(&(!polarity, term)) {
            return Some(());
        }
        seen.insert((polarity, term));
    }
    None
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

#[cfg(test)]
mod tests {
    #[test]
    fn resolution() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
                (declare-fun r () Bool)
            ",
            "Simple working examples" {
                "(assume h1 (not p))
                (step t2 (cl p q) :rule trust_me)
                (step t3 (cl q) :rule resolution :premises (h1 t2))": true,

                "(assume h1 (not p))
                (assume h2 (not q))
                (assume h3 (not r))
                (step t4 (cl p q r) :rule trust_me)
                (step t5 (cl) :rule resolution :premises (h1 h2 h3 t4))": true,

                "(assume h1 (not p))
                (assume h2 q)
                (step t3 (cl p (not q)) :rule trust_me)
                (step t4 (cl) :rule resolution :premises (h1 h2 t3))": true,
            }
            "Missing term in final clause" {
                "(assume h1 (not p))
                (step t2 (cl p q r) :rule trust_me)
                (step t3 (cl q) :rule resolution :premises (h1 t2))": false,
            }
            "Extra term in final clause" {
                "(assume h1 (not p))
                (step t2 (cl p q r) :rule trust_me)
                (step t3 (cl p q r) :rule resolution :premises (h1 t2))": false,
            }
            "Term appears in final clause with wrong polarity" {
                "(assume h1 (not p))
                (step t2 (cl p q r) :rule trust_me)
                (step t3 (cl (not q) r) :rule resolution :premises (h1 t2))": false,
            }
            "Duplicate term in final clause" {
                "(step t1 (cl q (not p)) :rule trust_me)
                (step t2 (cl p q r) :rule trust_me)
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
                "(step t1 (cl (not q) (not (not p)) (not p)) :rule trust_me)
                (step t2 (cl (not (not (not p))) p) :rule trust_me)
                (step t3 (cl (not q) p (not p)) :rule resolution :premises (t1 t2))": true,

                "(step t1 (cl (not q) (not (not p)) (not p)) :rule trust_me)
                (step t2 (cl (not (not (not p))) p) :rule trust_me)
                (step t3 (cl (not q) (not (not (not p))) (not (not p)))
                    :rule resolution :premises (t1 t2))": true,

                "(step t1 (cl (not q) (not (not p)) (not p)) :rule trust_me)
                (step t2 (cl (not (not (not p))) p) :rule trust_me)
                (step t3 (cl (not q) p (not p) (not (not (not p))) (not (not p)))
                    :rule resolution :premises (t1 t2))": true,
            }
            "Weird behaviour where leading negations sometimes are added to conclusion" {
                "(assume h1 (not p))
                (assume h2 (= (not p) (not (not q))))
                (step t3 (cl (not (= (not p) (not (not q)))) p q) :rule trust_me)
                (step t4 (cl (not (not q))) :rule resolution :premises (h1 h2 t3))": true,
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
                "(step t1 (cl (not p) p) :rule trust_me)
                (step t2 (cl true) :rule tautology :premises (t1))": true,

                "(step t1 (cl p q (not q) r s) :rule trust_me)
                (step t2 (cl true) :rule tautology :premises (t1))": true,

                "(step t1 (cl p (not (not s)) q r (not (not (not s)))) :rule trust_me)
                (step t2 (cl true) :rule tautology  :premises (t1))": true,
            }
            "Conclusion is not \"true\"" {
                "(step t1 (cl p q (not q) r s) :rule trust_me)
                (step t2 (cl false) :rule tautology :premises (t1))": false,

                "(step t1 (cl p q (not q) r s) :rule trust_me)
                (step t2 (cl) :rule tautology :premises (t1))": false,
            }
            "Premise is not a tautology" {
                "(step t1 (cl p) :rule trust_me)
                (step t2 (cl true) :rule tautology :premises (t1))": false,

                "(step t1 (cl p (not (not s)) q r s) :rule trust_me)
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
                "(step t1 (cl p q q r s s) :rule trust_me)
                (step t2 (cl p q r s) :rule contraction :premises (t1))": true,

                "(step t1 (cl p p p q q r s s s) :rule trust_me)
                (step t2 (cl p q r s) :rule contraction :premises (t1))": true,

                "(step t1 (cl p q r s) :rule trust_me)
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
                "(step t1 (cl p p q) :rule trust_me)
                (step t2 (cl p r) :rule contraction :premises (t1))": false,
            }
            "Terms are not in correct order" {
                "(step t1 (cl p q q r) :rule trust_me)
                (step t2 (cl p r q) :rule contraction :premises (t1))": false,
            }
            "Conclusion is missing terms" {
                "(step t1 (cl p q q r) :rule trust_me)
                (step t2 (cl p r) :rule contraction :premises (t1))": false,

                "(step t1 (cl p p q r) :rule trust_me)
                (step t2 (cl p q) :rule contraction :premises (t1))": false,
            }
            "Conclusion has extra term at the end" {
                "(step t1 (cl p p q) :rule trust_me)
                (step t2 (cl p q r s) :rule contraction :premises (t1))": false,
            }
        }
    }
}
