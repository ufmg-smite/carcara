//! This module contains rules that are not yet in the specification for the Alethe format.

use super::{get_clause_from_command, get_single_term_from_command, to_option, RuleArgs};
use crate::ast::*;
use ahash::AHashSet;

pub fn reordering(RuleArgs { conclusion, premises, .. }: RuleArgs) -> Option<()> {
    rassert!(premises.len() == 1);

    let premise = get_clause_from_command(premises[0]);
    rassert!(premise.len() == conclusion.len());

    let premise_set: AHashSet<_> = premise.iter().collect();
    let conclusion_set: AHashSet<_> = conclusion.iter().collect();
    to_option(premise_set == conclusion_set)
}

pub fn symm(RuleArgs { conclusion, premises, .. }: RuleArgs) -> Option<()> {
    rassert!(premises.len() == 1 && conclusion.len() == 1);

    let premise = get_single_term_from_command(premises[0])?;
    let (p_1, q_1) = match_term!((= p q) = premise)?;
    let (q_2, p_2) = match_term!((= q p) = conclusion[0])?;
    to_option(p_1 == p_2 && q_1 == q_2)
}

pub fn not_symm(RuleArgs { conclusion, premises, .. }: RuleArgs) -> Option<()> {
    rassert!(premises.len() == 1 && conclusion.len() == 1);

    let premise = get_single_term_from_command(premises[0])?;
    let (p_1, q_1) = match_term!((not (= p q)) = premise)?;
    let (q_2, p_2) = match_term!((not (= q p)) = conclusion[0])?;
    to_option(p_1 == p_2 && q_1 == q_2)
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
