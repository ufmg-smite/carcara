//! This module contains rules that are not yet in the specification for the Alethe format.

use super::{
    assert_clause_len, assert_eq, assert_num_premises, get_clause_from_command, get_premise_term,
    CheckerError, RuleArgs, RuleResult,
};
use ahash::AHashSet;

pub fn reordering(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(&premises, 1)?;

    let premise = get_clause_from_command(premises[0]);
    assert_clause_len(conclusion, premise.len())?;

    let premise_set: AHashSet<_> = premise.iter().collect();
    let conclusion_set: AHashSet<_> = conclusion.iter().collect();
    if let Some(&t) = premise_set.difference(&conclusion_set).next() {
        Err(CheckerError::ReorderingMissingTerm(t.clone()))
    } else if let Some(&t) = conclusion_set.difference(&premise_set).next() {
        Err(CheckerError::ReorderingExtraTerm(t.clone()))
    } else {
        Ok(())
    }
}

pub fn symm(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(&premises, 1)?;
    assert_clause_len(conclusion, 1)?;

    let premise = get_premise_term(premises[0])?;
    let (p_1, q_1) = match_term_err!((= p q) = premise)?;
    let (q_2, p_2) = match_term_err!((= q p) = &conclusion[0])?;
    assert_eq(p_1, p_2)?;
    assert_eq(q_1, q_2)
}

pub fn not_symm(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(&premises, 1)?;
    assert_clause_len(conclusion, 1)?;

    let premise = get_premise_term(premises[0])?;
    let (p_1, q_1) = match_term_err!((not (= p q)) = premise)?;
    let (q_2, p_2) = match_term_err!((not (= q p)) = &conclusion[0])?;
    assert_eq(p_1, p_2)?;
    assert_eq(q_1, q_2)
}

#[cfg(test)]
mod tests {
    #[test]
    fn reordering() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
                (declare-fun r () Bool)
                (declare-fun s () Bool)
            ",
            "Simple working examples" {
                "(step t1 (cl p q r s) :rule trust)
                (step t2 (cl r q p s) :rule reordering :premises (t1))": true,

                "(step t1 (cl p q q p r s) :rule trust)
                (step t2 (cl r q p p s q) :rule reordering :premises (t1))": true,

                "(step t1 (cl) :rule trust)
                (step t2 (cl) :rule reordering :premises (t1))": true,
            }
        }
    }

    #[test]
    fn symm() {
        test_cases! {
            definitions = "
                (declare-sort T 0)
                (declare-fun a () T)
                (declare-fun b () T)
            ",
            "Simple working examples" {
                "(assume h1 (= a b))
                (step t1 (cl (= b a)) :rule symm :premises (h1))": true,
            }
            "Failing examples" {
                "(assume h1 (not (= a b)))
                (step t1 (cl (not (= b a))) :rule symm :premises (h1))": false,
            }
        }
    }

    #[test]
    fn not_symm() {
        test_cases! {
            definitions = "
                (declare-sort T 0)
                (declare-fun a () T)
                (declare-fun b () T)
            ",
            "Simple working examples" {
                "(assume h1 (not (= a b)))
                (step t1 (cl (not (= b a))) :rule not_symm :premises (h1))": true,
            }
            "Failing examples" {
                "(assume h1 (= a b))
                (step t1 (cl (= b a)) :rule not_symm :premises (h1))": false,
            }
        }
    }
}
