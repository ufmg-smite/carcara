use super::{get_single_term_from_command, to_option, RuleArgs};
use crate::ast::*;

pub fn not_not(RuleArgs { conclusion, .. }: RuleArgs) -> Option<()> {
    if conclusion.len() != 2 {
        return None;
    }
    let p = match_term!((not (not (not p))) = conclusion[0])?;
    let q = conclusion[1].as_ref();
    to_option(p == q)
}

pub fn and_pos(RuleArgs { conclusion, .. }: RuleArgs) -> Option<()> {
    if conclusion.len() != 2 {
        return None;
    }
    let and_contents = match_term!((not (and ...)) = conclusion[0])?;
    and_contents
        .iter()
        .find(|&t| *t == conclusion[1])
        .map(|_| ())
}

pub fn and_neg(RuleArgs { conclusion, .. }: RuleArgs) -> Option<()> {
    if conclusion.len() < 2 {
        return None;
    }
    let and_contents = match_term!((and ...) = conclusion[0])?
        .iter()
        .map(|t| Some(t.as_ref()));
    let remaining = conclusion[1..].iter().map(|t| t.remove_negation());
    to_option(and_contents.eq(remaining))
}

pub fn or_pos(RuleArgs { conclusion, .. }: RuleArgs) -> Option<()> {
    if conclusion.len() < 2 {
        return None;
    }
    let or_contents = match_term!((not (or ...)) = conclusion[0])?;
    to_option(or_contents.iter().eq(&conclusion[1..]))
}

pub fn or_neg(RuleArgs { conclusion, .. }: RuleArgs) -> Option<()> {
    if conclusion.len() < 2 {
        return None;
    }
    let or_contents = match_term!((or ...) = conclusion[0])?;
    let other = conclusion[1].remove_negation()?;
    or_contents
        .iter()
        .find(|&t| t.as_ref() == other)
        .map(|_| ())
}

pub fn equiv_pos1(RuleArgs { conclusion, .. }: RuleArgs) -> Option<()> {
    if conclusion.len() != 3 {
        return None;
    }
    let (phi_1, phi_2) = match_term!((not (= phi_1 phi_2)) = conclusion[0])?;
    to_option(phi_1 == conclusion[1].as_ref() && phi_2 == conclusion[2].remove_negation()?)
}

pub fn equiv_pos2(RuleArgs { conclusion, .. }: RuleArgs) -> Option<()> {
    if conclusion.len() != 3 {
        return None;
    }
    let (phi_1, phi_2) = match_term!((not (= phi_1 phi_2)) = conclusion[0])?;
    to_option(phi_1 == conclusion[1].remove_negation()? && phi_2 == conclusion[2].as_ref())
}

pub fn ite1(
    RuleArgs {
        conclusion,
        premises,
        ..
    }: RuleArgs,
) -> Option<()> {
    if premises.len() != 1 || conclusion.len() != 2 {
        return None;
    }
    let premise_term = get_single_term_from_command(premises[0])?;
    let (phi_1, _, phi_3) = match_term!((ite phi_1 phi_2 phi_3) = premise_term)?;

    to_option(phi_1 == conclusion[0].as_ref() && phi_3 == conclusion[1].as_ref())
}

pub fn ite2(
    RuleArgs {
        conclusion,
        premises,
        ..
    }: RuleArgs,
) -> Option<()> {
    if premises.len() != 1 || conclusion.len() != 2 {
        return None;
    }
    let premise_term = get_single_term_from_command(premises[0])?;
    let (phi_1, phi_2, _) = match_term!((ite phi_1 phi_2 phi_3) = premise_term)?;

    to_option(phi_1 == conclusion[0].remove_negation()? && phi_2 == conclusion[1].as_ref())
}

pub fn ite_intro(RuleArgs { conclusion, .. }: RuleArgs) -> Option<()> {
    if conclusion.len() != 1 {
        return None;
    }
    let (root_term, right_side) = match_term!((= t u) = conclusion[0])?;

    // In some cases, no "ite" subterm is extracted from "t" (even if "t" has "ite" subterms), so
    // the conjunction in the right side of the equality has only one term: "t" itself, modulo
    // reordering of equalities. One example where this happens is the test file
    // SH_problems_all_filtered/isabelle-mirabelle/HOL-Library/smt_verit/x2020_07_23_15_09_29_511_18566192.smt_in.proof
    // Step "t7" in that proof is:
    //     (step t7 (cl (=
    //         (= (times$ c$ (ite (< (g$ n$) 0.0) (- (g$ n$)) (g$ n$)))
    //            (times$ (ite (< (g$ n$) 0.0) (- (g$ n$)) (g$ n$)) c$))
    //         (= (times$ c$ (ite (< (g$ n$) 0.0) (- (g$ n$)) (g$ n$)))
    //            (times$ (ite (< (g$ n$) 0.0) (- (g$ n$)) (g$ n$)) c$))
    //     )) :rule ite_intro)
    // For cases like this, we first check if "t" equals the right side term modulo reordering of
    // equalities. If not, we unwrap the conjunction and continue checking the rule normally.
    if DeepEq::eq_modulo_reordering(root_term, right_side) {
        return Some(());
    }
    let us = match_term!((and ...) = right_side)?;

    // "us" must be a conjunction where the first term is the root term
    if !DeepEq::eq_modulo_reordering(us[0].as_ref(), root_term) {
        return None;
    }
    let us = &us[1..];

    let subterms = root_term.subterms();
    let mut ite_subterms = subterms.filter_map(|term| match_term!((ite a b c) = term));

    // We assume that the "ite" terms appear in the conjunction in the same order as they
    // appear as subterms of the root term
    'outer: for u_i in &us[1..] {
        let (cond, (a, b), (c, d)) = match_term!((ite cond (= a b) (= c d)) = u_i)?;

        // For every term in "us", we find the next "ite" subterm that matches the expected form.
        // This is because some "ite" subterms may be skipped, and may not have a corresponding "u"
        // term
        while let Some(s_i) = ite_subterms.next() {
            // Since the (= r_1 s_1) and (= r_2 s_2) equalities may be flipped, we have to check
            // all four possibilities: neither are flipped, either one is flipped, or both are
            // flipped
            let is_valid = |r_1, s_1, r_2, s_2: &Term| {
                // s_i == s_1 == s_2 == (ite cond r_1 r_2)
                s_1 == s_2 && (cond, r_1, r_2) == s_i && match_term!((ite a b c) = s_1) == Some(s_i)
            };
            let is_valid = is_valid(a, b, c, d)
                || is_valid(b, a, c, d)
                || is_valid(a, b, d, c)
                || is_valid(b, a, d, c);

            if is_valid {
                continue 'outer;
            }
        }
        return None;
    }
    Some(())
}
