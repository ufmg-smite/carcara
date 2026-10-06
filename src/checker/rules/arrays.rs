use super::{
    RuleArgs, RuleResult, assert_clause_len, assert_eq, assert_num_premises, assert_polyeq,
    get_premise_term,
};
use crate::ast::{Binder, BindingList, Sort, Term, build_term, match_term_err};
use crate::checker::error::err;

pub fn idx(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    match_term_err!((= (select (store a i e) i) e) = &conclusion[0])?;
    Ok(())
}

pub fn row(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    let premise = get_premise_term(&premises[0])?;
    let (ip, jp) = match_term_err!((not (= i j)) = premise)?;

    assert_clause_len(conclusion, 1)?;
    let (_, ic, _, jc) =
        match_term_err!((= (select (store a i e) j) (select a j)) = &conclusion[0])?;
    // indices are the same in premise and conclusion
    assert_eq(ip, ic)?;
    assert_eq(jp, jc)?;
    Ok(())
}

pub fn row_contra(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    let premise = get_premise_term(&premises[0])?;
    let (_, ip, _, jp) =
        match_term_err!((not (= (select (store a i e) j) (select a j))) = premise)?;
    assert_clause_len(conclusion, 1)?;
    let (ic, jc) = match_term_err!((= i j) = &conclusion[0])?;
    // indices are the same in conclusion and premise, but conclusion might be flipped
    if ip != ic {
        assert_eq(ip, jc)?;
        assert_eq(jp, ic)
    } else {
        assert_eq(jp, jc)
    }
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
    assert_clause_len(conclusion, 1)?;
    let premise = get_premise_term(&premises[0])?;
    let (ap, bp) = match_term_err!((not (= a b)) = premise)?;
    let (ac, _, bc) = match_term_err!((not (= (select ac k) (select bc k))) = &conclusion[0])?;
    // arrays the same in premise and conclusion
    assert_eq(ap, ac)?;
    assert_eq(bp, bc)?;
    // build (choice (x I) (or (= a b) (not (= (select a x) (select b x))))) where
    // the type of x comes from the array sort of a. With that I can
    // check alpha equiv of (select a choice) with the lhs of
    // conclusion and likewise for the rhs

    // check index is (choice (x I) (not (= (select a x) (select b x))))
    let Sort::Array(index_sort, _) = pool.sort(ap).as_ref().clone() else {
        return err!("Could not get Array sort from term {ap}");
    };
    let x = pool.add(Term::new_var("x", index_sort.clone()));
    let body = build_term!(pool, (or
        (= {ap.clone()} {bp.clone()})
        (not (= (select { ap.clone() } { x.clone() }) (select { bp.clone() } { x.clone() })))
    ));
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
