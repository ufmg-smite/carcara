use super::{
    assert_clause_len, assert_eq, assert_num_premises, assert_polyeq, get_premise_term,
    CheckerError, RuleArgs, RuleResult,
};
use crate::ast::{Binder, BindingList, Sort, Term};

pub fn idx(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;

    let (_, i1, e1, i2, e2) = match_term_err!((= (select (store a i1 e1) i2) e2) = &conclusion[0])?;
    // same index in read over write
    assert_eq(i1, i2)?;
    // same element in lhs and rhs of equality
    assert_eq(e1, e2)?;
    Ok(())
}

pub fn row(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    let premise = get_premise_term(&premises[0])?;
    let (ip, jp) = match_term_err!((not (= ip jp)) = premise)?;

    assert_clause_len(conclusion, 1)?;
    let (a1, ic, _, jc1, a2, jc2) =
        match_term_err!((= (select (store a1 ic e) jc1) (select a2 jc2)) = &conclusion[0])?;
    // indices are the same in premise and conclusion
    assert_eq(ip, ic)?;
    assert_eq(jp, jc1)?;
    // indices are the same in the lhs and rhs of the conclusion
    assert_eq(jc1, jc2)?;
    // arrays are the same in the lhs and rhs of the conclusion
    assert_eq(a1, a2)?;
    Ok(())
}

pub fn row_contra(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    let premise = get_premise_term(&premises[0])?;
    let (a1, ip, _, jp1, a2, jp2) =
        match_term_err!((not (= (select (store a1 ip e) jp1) (select a2 jp2))) = premise)?;
    assert_clause_len(conclusion, 1)?;
    let (ic, jc) = match_term_err!((= ic jc) = &conclusion[0])?;
    // indices are the same in the lhs and rhs of the premise
    assert_eq(jp1, jp2)?;
    // arrays are the same in the lhs and rhs of the premise
    assert_eq(a1, a2)?;
    // indices are the same in conclusion and premise
    assert_eq(ip, ic)?;
    assert_eq(jp2, jc)?;
    Ok(())
}

pub fn ext(
    RuleArgs {
        conclusion,
        premises,
        pool,
        polyeq_time,
        ..
    }: RuleArgs,
) -> RuleResult {
    assert_num_premises(premises, 1)?;
    let premise = get_premise_term(&premises[0])?;
    let (ap, bp) = match_term_err!((not (= a b)) = premise)?;
    let (ac, i1, bc, i2) =
        match_term_err!((not (= (select ac k1) (select bc k2))) = &conclusion[0])?;
    // arrays the same in premise and conclusion
    assert_eq(ap, ac)?;
    assert_eq(bp, bc)?;
    // same index
    assert_eq(i1, i2)?;
    // build (choice (x I) (or (= a b) (not (= (select a x) (select b x))))) where
    // the type of x comes from the array sort of a. With that I can
    // check alpha equiv of (select a choice) with the lhs of
    // conclusion and likewise for the rhs

    // check index is (choice (x I) (not (= (select a x) (select b x))))
    let Sort::Array(index_sort, _) = pool.sort(ap).as_sort().cloned().unwrap() else {
        return Err(CheckerError::Explanation(format!(
            "Could not get Array sort from term {}",
            ap
        )));
    };
    let x = pool.add(Term::new_var("x", index_sort.clone()));
    let body = build_term!(pool, (or (= {ap.clone()} {bp.clone()}) (not (= (select { ap.clone() } { x.clone() }) (select { bp.clone() } { x.clone() })))));
    let choice = pool.add(Term::Binder(
        Binder::Choice,
        BindingList(vec![("x".to_owned(), index_sort.clone())]),
        body,
    ));

    let alpha_equiv_conclusion = build_term!(pool,
                (not (= (select {ap.clone()} {choice.clone()}) (select {bp.clone()} {choice.clone()})))
    );

    assert_polyeq(&conclusion[0], &alpha_equiv_conclusion, polyeq_time)
}
