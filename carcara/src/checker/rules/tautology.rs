use super::{
    assert_clause_len, assert_eq, assert_num_args, assert_num_premises, assert_polyeq,
    get_premise_term, CheckerError, RuleArgs, RuleResult,
};
use crate::{ast::*, checker::rules::assert_operation_len};

pub fn r#true(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    if !conclusion[0].is_bool_true() {
        return Err(CheckerError::ExpectedBoolConstant(
            true,
            conclusion[0].clone(),
        ));
    }
    Ok(())
}

pub fn r#false(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let t = conclusion[0].remove_negation_err()?;
    if !t.is_bool_false() {
        return Err(CheckerError::ExpectedBoolConstant(false, t.clone()));
    }
    Ok(())
}

pub fn not_not(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 2)?;

    let p = match_term_err!((not (not (not p))) = &conclusion[0])?;
    assert_eq(p, &conclusion[1])
}

pub fn and_pos(RuleArgs { conclusion, args, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 2)?;
    assert_num_args(args, 1)?;

    let and_contents = match_term_err!((not (and ...)) = &conclusion[0])?;
    let i = args[0].as_usize_err()?;

    if i >= and_contents.len() {
        return Err(CheckerError::NoIthChildInTerm(i, conclusion[0].clone()));
    }

    assert_eq(&conclusion[1], &and_contents[i])
}

pub fn and_neg(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 2..)?;

    let and_contents = match_term_err!((and ...) = &conclusion[0])?;
    assert_operation_len(Operator::And, and_contents, conclusion.len() - 1)?;

    for (t, u) in and_contents.iter().zip(&conclusion[1..]) {
        let u = u.remove_negation_err()?;
        assert_eq(t, u)?;
    }
    Ok(())
}

pub fn or_pos(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 2..)?;

    let or_contents = match_term_err!((not (or ...)) = &conclusion[0])?;
    assert_operation_len(Operator::Or, or_contents, conclusion.len() - 1)?;

    for (t, u) in or_contents.iter().zip(&conclusion[1..]) {
        assert_eq(t, u)?;
    }
    Ok(())
}

pub fn or_neg(RuleArgs { conclusion, args, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 2)?;
    assert_num_args(args, 1)?;

    let or_contents = match_term_err!((or ...) = &conclusion[0])?;
    let other = conclusion[1].remove_negation_err()?;
    let i = args[0].as_usize_err()?;

    if i >= or_contents.len() {
        return Err(CheckerError::NoIthChildInTerm(i, conclusion[0].clone()));
    }

    assert_eq(other, &or_contents[i])
}

pub fn xor_pos1(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 3)?;
    let (phi_1, phi_2) = match_term_err!((not (xor phi_1 phi_2)) = &conclusion[0])?;
    assert_eq(phi_1, &conclusion[1])?;
    assert_eq(phi_2, &conclusion[2])
}

pub fn xor_pos2(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 3)?;
    let (phi_1, phi_2) = match_term_err!((not (xor phi_1 phi_2)) = &conclusion[0])?;
    assert_eq(phi_1, conclusion[1].remove_negation_err()?)?;
    assert_eq(phi_2, conclusion[2].remove_negation_err()?)
}

pub fn xor_neg1(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 3)?;
    let (phi_1, phi_2) = match_term_err!((xor phi_1 phi_2) = &conclusion[0])?;
    assert_eq(phi_1, &conclusion[1])?;
    assert_eq(phi_2, conclusion[2].remove_negation_err()?)
}

pub fn xor_neg2(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 3)?;
    let (phi_1, phi_2) = match_term_err!((xor phi_1 phi_2) = &conclusion[0])?;
    assert_eq(phi_1, conclusion[1].remove_negation_err()?)?;
    assert_eq(phi_2, &conclusion[2])
}

pub fn implies_pos(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 3)?;
    let (phi_1, phi_2) = match_term_err!((not (=> phi_1 phi_2)) = &conclusion[0])?;
    assert_eq(phi_1, conclusion[1].remove_negation_err()?)?;
    assert_eq(phi_2, &conclusion[2])
}

pub fn implies_neg1(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 2)?;
    let (phi_1, _) = match_term_err!((=> phi_1 phi_2) = &conclusion[0])?;
    assert_eq(phi_1, &conclusion[1])
}

pub fn implies_neg2(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 2)?;
    let (_, phi_2) = match_term_err!((=> phi_1 phi_2) = &conclusion[0])?;
    assert_eq(phi_2, conclusion[1].remove_negation_err()?)
}

pub fn equiv_pos1(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 3)?;
    let (phi_1, phi_2) = match_term_err!((not (= phi_1 phi_2)) = &conclusion[0])?;
    assert_eq(phi_1, &conclusion[1])?;
    assert_eq(phi_2, conclusion[2].remove_negation_err()?)
}

pub fn equiv_pos2(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 3)?;
    let (phi_1, phi_2) = match_term_err!((not (= phi_1 phi_2)) = &conclusion[0])?;
    assert_eq(phi_1, conclusion[1].remove_negation_err()?)?;
    assert_eq(phi_2, &conclusion[2])
}

pub fn equiv_neg1(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 3)?;
    let (phi_1, phi_2) = match_term_err!((= phi_1 phi_2) = &conclusion[0])?;
    assert_eq(phi_1, conclusion[1].remove_negation_err()?)?;
    assert_eq(phi_2, conclusion[2].remove_negation_err()?)
}

pub fn equiv_neg2(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 3)?;
    let (phi_1, phi_2) = match_term_err!((= phi_1 phi_2) = &conclusion[0])?;
    assert_eq(phi_1, &conclusion[1])?;
    assert_eq(phi_2, &conclusion[2])
}

pub fn ite_pos1(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 3)?;
    let (phi_1, _, phi_3) = match_term_err!((not (ite phi_1 phi_2 phi_3)) = &conclusion[0])?;
    assert_eq(phi_1, &conclusion[1])?;
    assert_eq(phi_3, &conclusion[2])
}

pub fn ite_pos2(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 3)?;
    let (phi_1, phi_2, _) = match_term_err!((not (ite phi_1 phi_2 phi_3)) = &conclusion[0])?;
    assert_eq(phi_1, conclusion[1].remove_negation_err()?)?;
    assert_eq(phi_2, &conclusion[2])
}

pub fn ite_neg1(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 3)?;
    let (phi_1, _, phi_3) = match_term_err!((ite phi_1 phi_2 phi_3) = &conclusion[0])?;
    assert_eq(phi_1, &conclusion[1])?;
    assert_eq(phi_3, conclusion[2].remove_negation_err()?)
}

pub fn ite_neg2(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 3)?;
    let (phi_1, phi_2, _) = match_term_err!((ite phi_1 phi_2 phi_3) = &conclusion[0])?;
    assert_eq(phi_1, conclusion[1].remove_negation_err()?)?;
    assert_eq(phi_2, conclusion[2].remove_negation_err()?)
}

pub fn equiv1(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 2)?;
    let premise_term = get_premise_term(&premises[0])?;
    let (phi_1, phi_2) = match_term_err!((= phi_1 phi_2) = premise_term)?;
    assert_eq(phi_1, conclusion[0].remove_negation_err()?)?;
    assert_eq(phi_2, &conclusion[1])
}

pub fn equiv2(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 2)?;
    let premise_term = get_premise_term(&premises[0])?;
    let (phi_1, phi_2) = match_term_err!((= phi_1 phi_2) = premise_term)?;
    assert_eq(phi_1, &conclusion[0])?;
    assert_eq(phi_2, conclusion[1].remove_negation_err()?)
}

pub fn not_equiv1(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 2)?;
    let premise_term = get_premise_term(&premises[0])?;
    let (phi_1, phi_2) = match_term_err!((not (= phi_1 phi_2)) = premise_term)?;
    assert_eq(phi_1, &conclusion[0])?;
    assert_eq(phi_2, &conclusion[1])
}

pub fn not_equiv2(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 2)?;
    let premise_term = get_premise_term(&premises[0])?;
    let (phi_1, phi_2) = match_term_err!((not (= phi_1 phi_2)) = premise_term)?;
    assert_eq(phi_1, conclusion[0].remove_negation_err()?)?;
    assert_eq(phi_2, conclusion[1].remove_negation_err()?)
}

pub fn ite1(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 2)?;
    let premise_term = get_premise_term(&premises[0])?;
    let (phi_1, _, phi_3) = match_term_err!((ite phi_1 phi_2 phi_3) = premise_term)?;
    assert_eq(phi_1, &conclusion[0])?;
    assert_eq(phi_3, &conclusion[1])
}

pub fn ite2(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 2)?;
    let premise_term = get_premise_term(&premises[0])?;
    let (phi_1, phi_2, _) = match_term_err!((ite phi_1 phi_2 phi_3) = premise_term)?;
    assert_eq(phi_1, conclusion[0].remove_negation_err()?)?;
    assert_eq(phi_2, &conclusion[1])
}

pub fn not_ite1(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 2)?;
    let premise_term = get_premise_term(&premises[0])?;
    let (phi_1, _, phi_3) = match_term_err!((not (ite phi_1 phi_2 phi_3)) = premise_term)?;
    assert_eq(phi_1, &conclusion[0])?;
    assert_eq(phi_3, conclusion[1].remove_negation_err()?)
}

pub fn not_ite2(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 2)?;
    let premise_term = get_premise_term(&premises[0])?;
    let (phi_1, phi_2, _) = match_term_err!((not (ite phi_1 phi_2 phi_3)) = premise_term)?;
    assert_eq(phi_1, conclusion[0].remove_negation_err()?)?;
    assert_eq(phi_2, conclusion[1].remove_negation_err()?)
}

pub fn ite_intro(RuleArgs { conclusion, polyeq_time, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;

    let (root_term, right_side) = match_term_err!((= t u) = &conclusion[0])?;

    // In some cases, no `ite` subterm is extracted from `t` (even if `t` has `ite` subterms), so
    // the conjunction in the right side of the equality has only one term: `t` itself, modulo
    // reordering of equalities. One example where this happens is the test file
    // SH_problems_all_filtered/isabelle-mirabelle/HOL-Library/smt_verit/x2020_07_23_15_09_29_511_18566192.smt_in.proof
    // Step `t7` in that proof is:
    // ```
    //     (step t7 (cl (=
    //         (= (times$ c$ (ite (< (g$ n$) 0.0) (- (g$ n$)) (g$ n$)))
    //            (times$ (ite (< (g$ n$) 0.0) (- (g$ n$)) (g$ n$)) c$))
    //         (= (times$ c$ (ite (< (g$ n$) 0.0) (- (g$ n$)) (g$ n$)))
    //            (times$ (ite (< (g$ n$) 0.0) (- (g$ n$)) (g$ n$)) c$))
    //     )) :rule ite_intro)
    // ```
    // For cases like this, we first check if `t` equals the right side term modulo reordering of
    // equalities. If not, we unwrap the conjunction and continue checking the rule normally.
    if polyeq(root_term, right_side, polyeq_time) {
        return Ok(());
    }
    let us = match_term_err!((and ...) = right_side)?;

    // `us` must be a conjunction where the first term is the root term
    assert_polyeq(&us[0], root_term, polyeq_time)?;

    // The remaining terms in `us` should be of the correct form
    for u_i in &us[1..] {
        let (cond, (a, b), (c, d)) = match_term_err!((ite cond (= a b) (= c d)) = u_i)?;

        let mut is_valid = |r_1, s_1, r_2, s_2| {
            // s_1 == s_2 == (ite cond r_1 r_2)
            if polyeq(s_1, s_2, polyeq_time) {
                if let Some((a, b, c)) = match_term!((ite a b c) = s_1) {
                    return polyeq(a, cond, polyeq_time)
                        && polyeq(b, r_1, polyeq_time)
                        && polyeq(c, r_2, polyeq_time);
                }
            }
            false
        };
        // Since the (= r_1 s_1) and (= r_2 s_2) equalities may be flipped, we have to check all
        // four possibilities: neither are flipped, either one is flipped, or both are flipped
        let is_valid = is_valid(a, b, c, d)
            || is_valid(b, a, c, d)
            || is_valid(a, b, d, c)
            || is_valid(b, a, d, c);

        if !is_valid {
            return Err(CheckerError::IsNotValidIteIntro(u_i.clone()));
        }
    }
    Ok(())
}

pub fn connective_def(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;

    let (first, second) = match_term_err!((= f s) = &conclusion[0])?;

    if let Some((phi_1, phi_2)) = match_term!((xor phi_1 phi_2) = first) {
        // phi_1 xor phi_2 <-> (¬phi_1 ^ phi_2) v (phi_1 ^ ¬phi_2)
        let ((a, b), (c, d)) = match_term_err!((or (and (not a) b) (and c (not d))) = second)?;
        assert_eq(a, phi_1)?;
        assert_eq(b, phi_2)?;
        assert_eq(c, phi_1)?;
        assert_eq(d, phi_2)
    } else if let Some((phi_1, phi_2)) = match_term!((= phi_1 phi_2) = first) {
        // (phi_1 <-> phi_2) <-> (phi_1 -> phi_2) ^ (phi_2 -> phi_1)
        let ((a, b), (c, d)) = match_term_err!((and (=> a b) (=> c d)) = second)?;
        assert_eq(a, phi_1)?;
        assert_eq(b, phi_2)?;
        assert_eq(c, phi_2)?;
        assert_eq(d, phi_1)
    } else if let Some((phi_1, phi_2, phi_3)) = match_term!((ite phi_1 phi_2 phi_3) = first) {
        // ite phi_1 phi_2 phi_3 <-> (phi_1 -> phi_2) ^ (¬phi_1 -> phi_3)
        let ((a, b), (c, d)) = match_term_err!((and (=> a b) (=> (not c) d)) = second)?;
        assert_eq(a, phi_1)?;
        assert_eq(b, phi_2)?;
        assert_eq(c, phi_1)?;
        assert_eq(d, phi_3)
    } else if let Some((first_bindings, first_inner)) = match_term!((forall ... f) = first) {
        let (second_bindings, second_inner) = match_term_err!((not (exists ... (not s))) = second)?;
        assert_eq(first_inner, second_inner)?;
        assert_eq(first_bindings, second_bindings)
    } else {
        Err(CheckerError::TermIsNotConnective(first.clone()))
    }
}
