pub mod normalization;
pub mod utils;

pub use normalization::NormalizedConcat;
pub use utils::*;

use super::{
    RuleArgs, RuleResult, assert_clause_len, assert_eq, assert_num_args, assert_num_premises,
    assert_polyeq, get_premise_term,
};

use crate::{
    ast::{
        Binder, BindingList, Constant, Operator, Rc, Sort, Term, build_term, match_term_err,
        pool::TermPool,
    },
    automata::{
        Automaton,
        operations::{self, has_reachable_accepting_state, is_subautomaton},
    },
    checker::error::{CheckerError, StringError},
};
use rug::Integer;

// CPC rule helper
/// Helper function for implementing the `re_kleene_unfold_pos` and `re_concat_unfold_pos` rules.
///
/// Internally handles the generation of the Skolem term resulting from `re_unfold_pos_component`,
/// as well as the recursive step `re_unfold_pos_concat_recursive` to produce the resulting term.
fn re_unfold_pos_concat(
    pool: &mut dyn TermPool,
    t: Rc<Term>,
    r: Rc<Term>,
) -> Result<(Rc<Term>, Rc<Term>), CheckerError> {
    /// Generates a Skolem term used for the positive unfolding in the general case.
    ///
    /// The generated Skolem has the following structure:
    /// ```text
    /// ε x. ∃ k_0, ..., k_n, R_0, ..., R_n.
    ///   (and (= t (str.++ k_0 k_1 ... k_i-1 x k_i+1 ... k_n))
    ///        (str.in_re k_0 R_0)
    ///        (str.in_re k_1 R_1)
    ///        ...
    ///        (str.in_re x R_i)
    ///        ...
    ///        (str.in_re k_n R_n))
    /// ```
    ///
    /// where `t` is the target string reconstructed by concatenating all `k_i`, and `i` is the
    /// index of the current string k being processed in the concatenation.
    fn re_unfold_pos_component(
        pool: &mut dyn TermPool,
        t: Rc<Term>,
        i: usize,
        previous_ks: &mut Vec<Rc<Term>>,
        previous_rs: &mut Vec<Rc<Term>>,
    ) -> Rc<Term> {
        let str_sort = pool.add_sort(Sort::String);
        let reglan_sort = pool.add_sort(Sort::RegLan);
        let x = pool.add(Term::new_var("x", str_sort.clone()));

        let mut and_args: Vec<Rc<Term>> = Vec::new();
        let mut concat_args: Vec<Rc<Term>> = Vec::new();
        let mut exists_binding_list: Vec<(String, Rc<Sort>)> = Vec::new();

        for j in 0..i {
            let name_k = format!("k_{j}");
            let name_r = format!("R_{j}");
            let k_j = pool.add(Term::new_var(name_k.clone(), str_sort.clone()));
            let r_j = pool.add(Term::new_var(name_r.clone(), reglan_sort.clone()));
            concat_args.push(k_j.clone());
            and_args.push(build_term!(pool, (strinre {k_j} {r_j})));
            exists_binding_list.push((name_k, str_sort.clone()));
            exists_binding_list.push((name_r, reglan_sort.clone()));
        }

        concat_args.push(x.clone());
        concat_args.extend(previous_ks.clone());
        let ks_concat = pool.add(Term::Op(Operator::StrConcat, concat_args));

        let name_r_i = format!("R_{i}");
        let r_i = pool.add(Term::new_var(name_r_i.clone(), reglan_sort.clone()));
        exists_binding_list.push((name_r_i, reglan_sort.clone()));
        and_args.push(build_term!(pool, (strinre {x.clone()} {r_i.clone()})));
        for (j, prev_r) in previous_rs.iter().enumerate() {
            and_args.push(build_term!(pool, (strinre {previous_ks[j].clone()} {prev_r.clone()})));
            let sum = i + j + 1;
            exists_binding_list.push((format!("R_{sum}"), reglan_sort.clone()));
        }

        let equality = build_term!(pool, (= {t.clone()} {ks_concat.clone()}));
        and_args.insert(0, equality);

        let conjunction = pool.add(Term::Op(Operator::And, and_args));
        let exists_binder = pool.add(Term::Binder(
            Binder::Exists,
            BindingList(exists_binding_list),
            conjunction,
        ));
        let choice_binder = pool.add(Term::Binder(
            Binder::Choice,
            BindingList(vec![("x".into(), str_sort.clone())]),
            exists_binder,
        ));

        previous_ks.insert(0, choice_binder.clone());
        previous_rs.insert(0, r_i.clone());

        choice_binder
    }

    fn re_unfold_pos_concat_recursive(
        pool: &mut dyn TermPool,
        t: Rc<Term>,
        r: Rc<Term>,
        previous_ks: &mut Vec<Rc<Term>>,
        previous_rs: &mut Vec<Rc<Term>>,
        n: usize,
    ) -> Result<(Rc<Term>, Rc<Term>), CheckerError> {
        match r.as_ref() {
            Term::Op(Operator::ReConcat, args) => {
                if let [r_1, r_2 @ ..] = &args[..] {
                    let re_conc = pool.add(Term::Op(Operator::ReConcat, r_2.to_vec()));
                    let (c, m) = re_unfold_pos_concat_recursive(
                        pool,
                        t.clone(),
                        re_conc,
                        previous_ks,
                        previous_rs,
                        n + 1,
                    )?;
                    match r_1.as_ref() {
                        Term::Op(Operator::StrToRe, str_to_re_args) => {
                            let s = str_to_re_args.first().unwrap();
                            Ok((build_term!(pool, (strconcat {s.clone()} {c.clone()})), m))
                        }
                        _ => {
                            let k = re_unfold_pos_component(pool, t, n, previous_ks, previous_rs);
                            if args.len() == 1 {
                                Ok((
                                    build_term!(pool, (strconcat {k.clone()} {c.clone()})),
                                    build_term!(
                                        pool,
                                        (and (strinre {k.clone()} {r_1.clone()}) {m.clone()})
                                    ),
                                ))
                            } else {
                                Ok((
                                    build_term!(pool, (strconcat {k.clone()} {c.clone()})),
                                    build_term!(
                                        pool,
                                        (and (strinre {k.clone()} {r.clone()}) {m.clone()})
                                    ),
                                ))
                            }
                        }
                    }
                } else {
                    Ok((
                        pool.add(Term::new_string("")),
                        pool.add(Term::new_bool(true)),
                    ))
                }
            }
            _ => Err(CheckerError::CannotApplyReUnfoldPos(r.clone())),
        }
    }

    re_unfold_pos_concat_recursive(
        pool,
        t.clone(),
        r.clone(),
        &mut Vec::new(),
        &mut Vec::new(),
        0,
    )
}

// CPC Rules (a little outdated)
pub fn concat_eq(
    RuleArgs {
        premises,
        args,
        conclusion,
        pool,
        polyeq_time,
        ..
    }: RuleArgs,
) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_num_args(args, 1)?;
    assert_clause_len(conclusion, 1)?;

    match_term_err!((= x y) = &conclusion[0])?;

    let term = get_premise_term(&premises[0])?;
    let rev = args[0].as_bool_err()?;
    let (s, t) = match_term_err!((= s t) = term)?;

    let s_norm = NormalizedConcat::from_term(pool, s);
    let t_norm = NormalizedConcat::from_term(pool, t);
    let (ss, ts) = s_norm.strip_prefix_or_suffix(&t_norm, s, t, rev, polyeq_time)?;
    let expected = build_term!(
        pool,
        (= {ss.into_term(pool)} {ts.into_term(pool)})
    );

    let expanded = NormalizedConcat::expand_constants(pool, &conclusion[0]);

    assert_eq(&expected, &expanded)
}

pub fn concat_unify(
    RuleArgs {
        premises,
        args,
        conclusion,
        pool,
        polyeq_time,
        ..
    }: RuleArgs,
) -> RuleResult {
    assert_num_premises(premises, 2)?;
    assert_num_args(args, 1)?;
    assert_clause_len(conclusion, 1)?;

    match_term_err!((= x y) = &conclusion[0])?;

    let term = get_premise_term(&premises[0])?;
    let prefixes = get_premise_term(&premises[1])?;
    let rev = args[0].as_bool_err()?;
    let (s, t) = match_term_err!((= s t) = term)?;
    let (s_1, t_1) = match_term_err!((= (strlen s_1) (strlen t_1)) = prefixes)?;

    let s_norm = NormalizedConcat::from_term(pool, s);
    let t_norm = NormalizedConcat::from_term(pool, t);
    let s_1_norm = NormalizedConcat::from_term(pool, s_1);
    let t_1_norm = NormalizedConcat::from_term(pool, t_1);

    s_1_norm.assert_is_prefix_or_suffix_of(&s_norm, s_1, s, rev, polyeq_time)?;
    t_1_norm.assert_is_prefix_or_suffix_of(&t_norm, t_1, t, rev, polyeq_time)?;

    let s_concat = s_1_norm.into_term(pool);
    let t_concat = t_1_norm.into_term(pool);
    let expected = build_term!(
        pool,
        (= {s_concat} {t_concat})
    );

    let expanded = NormalizedConcat::expand_constants(pool, &conclusion[0]);

    assert_eq(&expected, &expanded)
}

pub fn concat_conflict(
    RuleArgs {
        premises,
        args,
        conclusion,
        pool,
        polyeq_time,
        ..
    }: RuleArgs,
) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_num_args(args, 1)?;
    assert_clause_len(conclusion, 1)?;

    let term = get_premise_term(&premises[0])?;
    let rev = args[0].as_bool_err()?;
    if conclusion[0].as_bool_err()? {
        return Err(CheckerError::ExpectedBoolConstant(
            false,
            conclusion[0].clone(),
        ));
    }

    let (s, t) = match_term_err!((= s t) = term)?;
    let s_norm = NormalizedConcat::from_term(pool, s);
    let t_norm = NormalizedConcat::from_term(pool, t);
    let (ss, ts) = s_norm.strip_prefix_or_suffix(&t_norm, s, t, rev, polyeq_time)?;

    let ss_head = if rev { ss.last() } else { ss.first() };
    let ts_head = if rev { ts.last() } else { ts.first() };

    if let Some(ss_head) = ss_head {
        NormalizedConcat::assert_length_one(ss_head)?;
        if let Some(ts_head) = ts_head {
            NormalizedConcat::assert_length_one(ts_head)?;
        }
    } else if let Some(ts_head) = ts_head {
        NormalizedConcat::assert_length_one(ts_head)?;
    } else {
        return Err(CheckerError::ExpectedDifferentConstantPrefixes(
            s.clone(),
            t.clone(),
        ));
    }

    Ok(())
}

pub fn concat_csplit_prefix(
    RuleArgs {
        premises,
        conclusion,
        pool,
        polyeq_time,
        ..
    }: RuleArgs,
) -> RuleResult {
    assert_num_premises(premises, 2)?;
    assert_clause_len(conclusion, 1)?;

    match_term_err!((= t_1 x) = &conclusion[0])?;

    let terms = get_premise_term(&premises[0])?;
    let length = get_premise_term(&premises[1])?;
    let (t, s) = match_term_err!((= t s) = terms)?;
    let t_1 = match_term_err!((not (= (strlen t_1) 0)) = length)?;

    let s_norm = NormalizedConcat::from_term(pool, s);
    let t_norm = NormalizedConcat::from_term(pool, t);
    if t_norm.is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", t.clone()));
    }
    if s_norm.is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", s.clone()));
    }

    let t_1_norm = NormalizedConcat::from_term(pool, t_1);
    t_1_norm.assert_is_prefix_of(&t_norm, t_1, t, polyeq_time)?;
    let mut right_eq: Vec<Rc<Term>> = vec![];
    if let Some(c) = s_norm.first() {
        NormalizedConcat::assert_length_one(c)?;
        right_eq.push(c.clone());
        let n = pool.add(Term::new_int(1));
        right_eq.push(pool.build_str_suffix_rem(t_1, &n));
    }

    let t_1 = NormalizedConcat::expand_constants(pool, t_1);
    let right_eq_concat = NormalizedConcat::new(right_eq).into_term(pool);
    let expected = build_term!(
        pool,
        (= {t_1} {right_eq_concat})
    );

    let expanded = NormalizedConcat::expand_constants(pool, &conclusion[0]);

    assert_eq(&expected, &expanded)
}

pub fn concat_csplit_suffix(
    RuleArgs {
        premises,
        conclusion,
        pool,
        polyeq_time,
        ..
    }: RuleArgs,
) -> RuleResult {
    assert_num_premises(premises, 2)?;
    assert_clause_len(conclusion, 1)?;

    match_term_err!((= t_2 x) = &conclusion[0])?;

    let terms = get_premise_term(&premises[0])?;
    let length = get_premise_term(&premises[1])?;
    let (t, s) = match_term_err!((= t s) = terms)?;
    let t_2 = match_term_err!((not (= (strlen t_2) 0)) = length)?;

    let s_norm = NormalizedConcat::from_term(pool, s);
    let t_norm = NormalizedConcat::from_term(pool, t);
    if t_norm.is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", t.clone()));
    }
    if s_norm.is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", s.clone()));
    }

    let t_2_norm = NormalizedConcat::from_term(pool, t_2);
    t_2_norm.assert_is_suffix_of(&t_norm, t_2, t, polyeq_time)?;
    let mut right_eq: Vec<Rc<Term>> = vec![];
    if let Some(c) = s_norm.last() {
        NormalizedConcat::assert_length_one(c)?;
        let n = build_term!(pool, (- (strlen {t_2.clone()}) 1));
        right_eq.push(pool.build_str_prefix(t_2, &n));
        right_eq.push(c.clone());
    }

    let t_2 = NormalizedConcat::expand_constants(pool, t_2);
    let right_eq_concat = NormalizedConcat::new(right_eq).into_term(pool);
    let expected = build_term!(
        pool,
        (= {t_2} {right_eq_concat})
    );

    let expanded = NormalizedConcat::expand_constants(pool, &conclusion[0]);

    assert_eq(&expected, &expanded)
}

pub fn concat_split_prefix(
    RuleArgs {
        premises,
        conclusion,
        pool,
        polyeq_time,
        ..
    }: RuleArgs,
) -> RuleResult {
    assert_num_premises(premises, 2)?;
    assert_clause_len(conclusion, 1)?;

    match_term_err!(
        (and
            (or (= t_1 x) (= s_1 y))
            (not (= r ""))
            (> (strlen r) 0)
        ) = &conclusion[0]
    )?;

    let terms = get_premise_term(&premises[0])?;
    let length = get_premise_term(&premises[1])?;
    let (t, s) = match_term_err!((= t s) = terms)?;
    let (t_1, s_1) = match_term_err!((not (= (strlen t_1) (strlen s_1))) = length)?;

    let t_norm = NormalizedConcat::from_term(pool, t);
    let s_norm = NormalizedConcat::from_term(pool, s);
    if t_norm.is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", t.clone()));
    }
    if s_norm.is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", s.clone()));
    }

    let t_1_norm = NormalizedConcat::from_term(pool, t_1);
    let s_1_norm = NormalizedConcat::from_term(pool, s_1);
    t_1_norm.assert_is_prefix_of(&t_norm, t_1, t, polyeq_time)?;
    s_1_norm.assert_is_prefix_of(&s_norm, s_1, s, polyeq_time)?;
    let t_1 = NormalizedConcat::expand_constants(pool, t_1);
    let s_1 = NormalizedConcat::expand_constants(pool, s_1);
    let r = pool.build_str_unify_split_prefix(&t_1, &s_1);

    let or = build_term!(
        pool,
        (or
            (=
                {t_1.clone()}
                (strconcat {s_1.clone()} {r.clone()})
            )
            (=
                {s_1.clone()}
                (strconcat {t_1.clone()} {r.clone()})
            )
        )
    );

    let empty = pool.add(Term::new_string(""));
    let expanded = build_term!(
        pool,
        (and
            {or}
            (not (= {r.clone()} {empty}))
            (> (strlen {r}) 0)
        )
    );

    let expanded = NormalizedConcat::expand_constants(pool, &expanded);
    let expected = NormalizedConcat::expand_constants(pool, &conclusion[0]);

    assert_eq(&expected, &expanded)
}

pub fn concat_split_suffix(
    RuleArgs {
        premises,
        conclusion,
        pool,
        polyeq_time,
        ..
    }: RuleArgs,
) -> RuleResult {
    assert_num_premises(premises, 2)?;
    assert_clause_len(conclusion, 1)?;

    match_term_err!(
        (and
            (or (= t_2 x) (= s_2 y))
            (not (= r ""))
            (> (strlen r) 0)
        ) = &conclusion[0]
    )?;

    let terms = get_premise_term(&premises[0])?;
    let length = get_premise_term(&premises[1])?;
    let (t, s) = match_term_err!((= t s) = terms)?;
    let (t_2, s_2) = match_term_err!((not (= (strlen t_2) (strlen s_2))) = length)?;

    let t_norm = NormalizedConcat::from_term(pool, t);
    let s_norm = NormalizedConcat::from_term(pool, s);
    if t_norm.is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", t.clone()));
    }
    if s_norm.is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", s.clone()));
    }

    let t_2_norm = NormalizedConcat::from_term(pool, t_2);
    let s_2_norm = NormalizedConcat::from_term(pool, s_2);
    t_2_norm.assert_is_suffix_of(&t_norm, t_2, t, polyeq_time)?;
    s_2_norm.assert_is_suffix_of(&s_norm, s_2, s, polyeq_time)?;
    let t_2 = NormalizedConcat::expand_constants(pool, t_2);
    let s_2 = NormalizedConcat::expand_constants(pool, s_2);
    let r = pool.build_str_unify_split_suffix(&t_2, &s_2);

    let or = build_term!(
        pool,
        (or
            (=
                {t_2.clone()}
                (strconcat {r.clone()} {s_2.clone()})
            )
            (=
                {s_2.clone()}
                (strconcat {r.clone()} {t_2.clone()})
            )
        )
    );

    let empty = pool.add(Term::new_string(""));
    let expanded = build_term!(
        pool,
        (and
            {or}
            (not (= {r.clone()} {empty}))
            (> (strlen {r}) 0)
        )
    );

    let expanded = NormalizedConcat::expand_constants(pool, &expanded);
    let expected = NormalizedConcat::expand_constants(pool, &conclusion[0]);

    assert_eq(&expected, &expanded)
}

pub fn concat_lprop_prefix(
    RuleArgs {
        premises,
        conclusion,
        pool,
        polyeq_time,
        ..
    }: RuleArgs,
) -> RuleResult {
    assert_num_premises(premises, 2)?;
    assert_clause_len(conclusion, 1)?;

    match_term_err!(
        (and
            (= t_1 x)
            (not (= r ""))
            (> (strlen r) 0)
        ) = &conclusion[0]
    )?;

    let terms = get_premise_term(&premises[0])?;
    let length = get_premise_term(&premises[1])?;
    let (t, s) = match_term_err!((= t s) = terms)?;
    let (t_1, s_1) = match_term_err!((> (strlen t_1) (strlen s_1)) = length)?;

    let t_norm = NormalizedConcat::from_term(pool, t);
    let s_norm = NormalizedConcat::from_term(pool, s);
    if t_norm.is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", t.clone()));
    }
    if s_norm.is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", s.clone()));
    }

    let t_1_norm = NormalizedConcat::from_term(pool, t_1);
    let s_1_norm = NormalizedConcat::from_term(pool, s_1);
    t_1_norm.assert_is_prefix_of(&t_norm, t_1, t, polyeq_time)?;
    s_1_norm.assert_is_prefix_of(&s_norm, s_1, s, polyeq_time)?;
    let t_1 = NormalizedConcat::expand_constants(pool, t_1);
    let s_1 = NormalizedConcat::expand_constants(pool, s_1);
    let r = pool.build_str_unify_split_prefix(&t_1, &s_1);

    let eq = build_term!(pool, (strconcat {s_1} {r.clone()}));
    let empty = pool.add(Term::new_string(""));
    let expanded = build_term!(
        pool,
        (and
            (= {t_1} {eq})
            (not (= {r.clone()} {empty}))
            (> (strlen {r}) 0)
        )
    );

    let expanded = NormalizedConcat::expand_constants(pool, &expanded);
    let expected = NormalizedConcat::expand_constants(pool, &conclusion[0]);

    assert_eq(&expected, &expanded)
}

pub fn concat_lprop_suffix(
    RuleArgs {
        premises,
        conclusion,
        pool,
        polyeq_time,
        ..
    }: RuleArgs,
) -> RuleResult {
    assert_num_premises(premises, 2)?;
    assert_clause_len(conclusion, 1)?;

    match_term_err!(
        (and
            (= t_2 x)
            (not (= r ""))
            (> (strlen r) 0)
        ) = &conclusion[0]
    )?;

    let terms = get_premise_term(&premises[0])?;
    let length = get_premise_term(&premises[1])?;
    let (t, s) = match_term_err!((= t s) = terms)?;
    let (t_2, s_2) = match_term_err!((> (strlen t_2) (strlen s_2)) = length)?;

    let t_norm = NormalizedConcat::from_term(pool, t);
    let s_norm = NormalizedConcat::from_term(pool, s);
    if t_norm.is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", t.clone()));
    }
    if s_norm.is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", s.clone()));
    }

    let t_2_norm = NormalizedConcat::from_term(pool, t_2);
    let s_2_norm = NormalizedConcat::from_term(pool, s_2);
    t_2_norm.assert_is_suffix_of(&t_norm, t_2, t, polyeq_time)?;
    s_2_norm.assert_is_suffix_of(&s_norm, s_2, s, polyeq_time)?;
    let t_2 = NormalizedConcat::expand_constants(pool, t_2);
    let s_2 = NormalizedConcat::expand_constants(pool, s_2);
    let r = pool.build_str_unify_split_suffix(&t_2, &s_2);

    let eq = build_term!(pool, (strconcat {r.clone()} {s_2}));
    let empty = pool.add(Term::new_string(""));
    let expanded = build_term!(
        pool,
        (and
            (= {t_2} {eq})
            (not (= {r.clone()} {empty}))
            (> (strlen {r}) 0)
        )
    );

    let expanded = NormalizedConcat::expand_constants(pool, &expanded);
    let expected = NormalizedConcat::expand_constants(pool, &conclusion[0]);

    assert_eq(&expected, &expanded)
}

pub fn concat_cprop_prefix(RuleArgs { premises, conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 2)?;
    assert_clause_len(conclusion, 1)?;

    match_term_err!((= t_1 (strconcat t_3 r)) = &conclusion[0])?;

    let terms = get_premise_term(&premises[0])?;
    let length = get_premise_term(&premises[1])?;
    let (t, s) = match_term_err!((= t s) = terms)?;
    let t_1 = match_term_err!((not (= (strlen t_1) 0)) = length)?;

    let args_t = match t.as_ref() {
        Term::Op(Operator::StrConcat, args) if args.len() == 3 => Ok(args),
        _ => Err(CheckerError::TermOfWrongForm(
            "(str.++ t1 t2 t3)",
            t.clone(),
        )),
    }?;

    assert_eq(&args_t[0], t_1)?;

    let empty = pool.add(Term::new_string(""));
    let ss = match s.as_ref() {
        Term::Const(Constant::String(text)) => {
            if text.is_empty() {
                return Err(CheckerError::ExpectedToNotBeEmpty(s.clone()));
            }
            vec![s.clone(), empty.clone()]
        }
        Term::Op(Operator::StrConcat, args) => args.clone(),
        _ => return Err(CheckerError::TermOfWrongForm("(str.++ s1 s2)", s.clone())),
    };

    let sc = NormalizedConcat::from_term(pool, &ss[0]);
    let sc_tail = sc.get(1..).unwrap_or_default();

    let t_2_flat = NormalizedConcat::from_term(pool, &args_t[1]);

    let v = 1 + NormalizedConcat::overlap(sc_tail, &t_2_flat);
    let v = pool.add(Term::new_int(v));
    let oc = pool.build_str_prefix(&ss[0], &v);
    let oc_len = build_term!(pool, (strlen {oc.clone()}));

    let r = pool.build_str_suffix_rem(t_1, &oc_len);
    let expanded = build_term!(pool, (= {t_1.clone()} (strconcat {oc.clone()} {r.clone()})));

    let expanded = NormalizedConcat::expand_constants(pool, &expanded);
    let expected = NormalizedConcat::expand_constants(pool, &conclusion[0]);

    assert_eq(&expected, &expanded)
}

pub fn concat_cprop_suffix(RuleArgs { premises, conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 2)?;
    assert_clause_len(conclusion, 1)?;

    match_term_err!((= t_2 (strconcat r t_3)) = &conclusion[0])?;

    let terms = get_premise_term(&premises[0])?;
    let length = get_premise_term(&premises[1])?;
    let (t, s) = match_term_err!((= t s) = terms)?;
    let t_2 = match_term_err!((not (= (strlen t_2) 0)) = length)?;

    let args_t = match t.as_ref() {
        Term::Op(Operator::StrConcat, args) if args.len() == 3 => Ok(args),
        _ => Err(CheckerError::TermOfWrongForm(
            "(str.++ t1 t2 t3)",
            t.clone(),
        )),
    }?;

    assert_eq(&args_t[2], t_2)?;

    let empty = pool.add(Term::new_string(""));
    let ss = match s.as_ref() {
        Term::Const(Constant::String(text)) => {
            if text.is_empty() {
                return Err(CheckerError::ExpectedToNotBeEmpty(s.clone()));
            }
            vec![empty.clone(), s.clone()]
        }
        Term::Op(Operator::StrConcat, args) => args.clone(),
        _ => return Err(CheckerError::TermOfWrongForm("(str.++ s1 s2)", s.clone())),
    };

    let mut sc = NormalizedConcat::from_term(pool, &ss[1]);
    sc.reverse();
    let sc_tail = sc.get(1..).unwrap_or_default();

    let mut t_2_flat = NormalizedConcat::from_term(pool, &args_t[1]);
    t_2_flat.reverse();

    let v = 1 + NormalizedConcat::overlap(sc_tail, &t_2_flat);
    let v = pool.add(Term::new_int(v));
    let oc = pool.build_str_suffix(&ss[1], &v);

    let rhs = build_term!(pool, (- (strlen {t_2.clone()}) (strlen {oc.clone()})));
    let r = pool.build_str_prefix(t_2, &rhs);
    let expanded = build_term!(pool, (= {t_2.clone()} (strconcat {r.clone()} {oc.clone()})));

    let expanded = NormalizedConcat::expand_constants(pool, &expanded);
    let expected = NormalizedConcat::expand_constants(pool, &conclusion[0]);

    assert_eq(&expected, &expanded)
}

pub fn string_decompose(
    RuleArgs {
        premises,
        args,
        conclusion,
        pool,
        polyeq_time,
        ..
    }: RuleArgs,
) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_num_args(args, 1)?;
    assert_clause_len(conclusion, 1)?;

    let term = get_premise_term(&premises[0])?;
    let rev = args[0].as_bool_err()?;
    let (t, n) = match_term_err!((>= (strlen t) n) = term)?;

    match_term_err!(
        (and
            (= t x)
            (= (strlen y) n)
        ) = &conclusion[0]
    )?;

    let w_1 = pool.build_str_prefix(t, n);
    let w_2 = pool.build_str_suffix_rem(t, n);
    let len_term = if rev { w_2.clone() } else { w_1.clone() };

    let expanded = build_term!(
            pool,
            (and
                (= {t.clone()} (strconcat {w_1.clone()} {w_2.clone()}))
                (= (strlen {len_term.clone()}) {n.clone()})
            )
    );

    assert_polyeq(&conclusion[0], &expanded, polyeq_time)
}

pub fn string_length_pos(RuleArgs { args, conclusion, polyeq_time, .. }: RuleArgs) -> RuleResult {
    assert_num_args(args, 1)?;
    assert_clause_len(conclusion, 1)?;

    let t = &args[0];
    // Note that the three occurrences of 't' are matched independently, since they
    // don't have to be identical to each other.
    let (t_1, t_2, t_3) = match_term_err!(
        (or
            (and
                (= (strlen t_1) 0)
                (= t_2 "")
            )
            (> (strlen t_3) 0)
        ) = &conclusion[0]
    )?;

    assert_polyeq(t_1, t, polyeq_time)?;
    assert_polyeq(t_2, t, polyeq_time)?;
    assert_polyeq(t_3, t, polyeq_time)?;

    Ok(())
}

pub fn string_length_non_empty(
    RuleArgs {
        premises, conclusion, polyeq_time, ..
    }: RuleArgs,
) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 1)?;

    let term = get_premise_term(&premises[0])?;
    let t = match_term_err!((not (= t "")) = term)?;

    let t_conc = match_term_err!(
        (not
            (= (strlen t) 0)
        ) = &conclusion[0]
    )?;

    assert_polyeq(t_conc, t, polyeq_time)?;

    Ok(())
}

pub fn re_inter(
    RuleArgs {
        premises, conclusion, polyeq_time, ..
    }: RuleArgs,
) -> RuleResult {
    assert_num_premises(premises, 2)?;
    assert_clause_len(conclusion, 1)?;

    let (x_conc, s_conc, t_conc) = match_term_err!((strinre x (reinter s t)) = &conclusion[0])?;

    let t_1 = get_premise_term(&premises[0])?;
    let t_2 = get_premise_term(&premises[1])?;
    let (x_1, s) = match_term_err!((strinre x s) = t_1)?;
    let (x_2, t) = match_term_err!((strinre x t) = t_2)?;

    assert_polyeq(x_conc, x_1, polyeq_time)?;
    assert_polyeq(x_conc, x_2, polyeq_time)?;

    assert_eq(s_conc, s)?;
    assert_eq(t_conc, t)?;

    Ok(())
}

pub fn re_kleene_star_unfold_pos(
    RuleArgs { premises, conclusion, pool, .. }: RuleArgs,
) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 1)?;

    let term = get_premise_term(&premises[0])?;
    let (t, r) = match_term_err!((strinre t r) = term)?;

    match_term_err!((or (= t_1 "") (strinre t_2 t_3) (and t_4 (not (= t_5 "")) (not (= t_6 "")))) = &conclusion[0])?;

    let expanded = match r.as_ref() {
        Term::Op(Operator::ReKleeneClosure, args) => {
            if let Some(r_1) = args.first() {
                let new_t = pool.add(Term::Op(
                    Operator::ReConcat,
                    vec![r_1.clone(), r.clone(), r_1.clone()],
                ));
                let (k, m) = re_unfold_pos_concat(pool, t.clone(), new_t)?;
                let concat_args = NormalizedConcat::from_term_unsplit(&k);
                match &concat_args[..] {
                    [k_0, k_1, k_2] => {
                        let eq = build_term!(pool, (= {t.clone()} (strconcat {k_0.clone()} {k_1.clone()} {k_2.clone()})));
                        let empty = pool.add(Term::new_string(""));
                        let simplified = if m.is_bool_true() {
                            pool.add(Term::Op(Operator::And, vec![eq.clone()]))
                        } else {
                            match m.as_ref() {
                                Term::Op(Operator::And, args) => {
                                    let mut new_args: Vec<Rc<Term>> = Vec::new();
                                    new_args.push(eq.clone());
                                    new_args.extend(args.clone());
                                    pool.add(Term::Op(Operator::And, new_args))
                                }
                                _ => unreachable!(),
                            }
                        };
                        Ok(build_term!(
                            pool,
                            (or
                                (= {t.clone()} {empty.clone()})
                                (strinre {t.clone()} {r_1.clone()})
                                (and
                                    {simplified}
                                    (not (= {k_0.clone()} {empty.clone()}))
                                    (not (= {k_2.clone()} {empty}))
                                )
                            )
                        ))
                    }
                    _ => Err(CheckerError::TermOfWrongForm(
                        "(str.++ k1 k2 k3)",
                        k.clone(),
                    )),
                }
            } else {
                unreachable!()
            }
        }
        _ => Err(CheckerError::TermOfWrongForm("(re.* ...)", r.clone())),
    }?;

    assert_eq(&conclusion[0], &expanded)
}

pub fn re_concat_unfold_pos(RuleArgs { premises, conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 1)?;

    let term = get_premise_term(&premises[0])?;
    let (t, r) = match_term_err!((strinre t r) = term)?;

    // Check conclusion possible formats
    let first_format = match_term_err!((= t_1 (strconcat ...)) = &conclusion[0]);
    let second_format = match_term_err!((and (= t_1 (strconcat ...)) (and ...)) = &conclusion[0]);
    if first_format.is_err() && second_format.is_err() {
        return Err(CheckerError::TermOfWrongForm(
            "(= t_1 (str.++ ...)) or (and (= t_1 (str.++ ...)) (and ...))",
            conclusion[0].clone(),
        ));
    }

    let expanded = match r.as_ref() {
        Term::Op(Operator::ReConcat, _) => {
            let (tk, m) = re_unfold_pos_concat(pool, t.clone(), r.clone())?;
            let new_concat = NormalizedConcat::from_term_unsplit(&tk).into_term(pool);
            let teq = build_term!(pool, (= {t.clone()} {new_concat.clone()}));
            if m.is_bool_true() {
                Ok(teq)
            } else {
                Ok(build_term!(pool, (and {teq.clone()} {m.clone()})))
            }
        }
        _ => Err(CheckerError::TermOfWrongForm("(re.++ ...)", r.clone())),
    }?;

    assert_eq(&conclusion[0], &expanded)
}

pub fn re_unfold_neg(RuleArgs { premises, conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 1)?;

    let term = get_premise_term(&premises[0])?;
    let (t, r) = match_term_err!((not (strinre t r)) = term)?;

    let int_sort = pool.add_sort(Sort::Int);
    let l = pool.add(Term::new_var("L", int_sort.clone()));
    let pref = pool.build_str_prefix(t, &l);
    let suff = pool.build_str_suffix_rem(t, &l);

    let expanded = match r.as_ref() {
        Term::Op(Operator::ReKleeneClosure, args) => {
            match_term_err!(
                (and
                    (not (= t ""))
                    (forall ...
                        (or
                            (<= l 0)
                            (< (strlen t) l)
                            (not (strinre pref r_1))
                            (not (strinre suff r))
                        )
                    )
                ) = &conclusion[0]
            )?;

            if let Some(r_1) = args.first() {
                let inner = build_term!(pool,
                    (or
                        (<= {l.clone()} 0)
                        (< (strlen {t.clone()}) {l.clone()})
                        (not (strinre {pref.clone()} {r_1.clone()}))
                        (not (strinre {suff.clone()} {r.clone()}))
                    )
                );
                let quantifier = pool.add(Term::Binder(
                    Binder::Forall,
                    BindingList(vec![("L".into(), int_sort.clone())]),
                    inner,
                ));
                let empty = pool.add(Term::new_string(""));
                Ok(build_term!(pool,
                    (and
                        (not (= {t.clone()} {empty.clone()}))
                        {quantifier.clone()}
                    )
                ))
            } else {
                unreachable!()
            }
        }
        Term::Op(Operator::ReConcat, args) => {
            match_term_err!(
                 (forall ...
                     (or
                         (< l 0)
                         (< (strlen t) l)
                         (not (strinre pref r_1))
                         (not (strinre suff r))
                     )
                 ) = &conclusion[0]
            )?;

            if let [r_1, r_2 @ ..] = &args[..] {
                let inner = build_term!(pool,
                    (or
                        (< {l.clone()} 0)
                        (< (strlen {t.clone()}) {l.clone()})
                        (not (strinre {pref.clone()} {r_1.clone()}))
                        (not (strinre {suff.clone()} {singleton_elim(pool, r_2)}))
                    )
                );
                let quantifier = pool.add(Term::Binder(
                    Binder::Forall,
                    BindingList(vec![("L".into(), int_sort.clone())]),
                    inner,
                ));
                Ok(quantifier)
            } else {
                unreachable!()
            }
        }
        _ => Err(CheckerError::TermOfWrongForm(
            "(re.* ...) or (re.++ ...)",
            r.clone(),
        )),
    }?;

    assert_eq(&conclusion[0], &expanded)
}

pub fn re_unfold_neg_concat_fixed_prefix(
    RuleArgs { premises, conclusion, pool, .. }: RuleArgs,
) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 1)?;

    match_term_err!(
        (or
            (not (strinre pref r_1))
            (not (strinre suff r_2))
        ) = &conclusion[0]
    )?;

    let term = get_premise_term(&premises[0])?;
    let (s, r) = match_term_err!((not (strinre s r)) = term)?;

    let expanded = if let Term::Op(Operator::ReConcat, args) = r.as_ref() {
        if let [r_1, r_2 @ ..] = &args[..] {
            let n = Term::new_int(str_fixed_len_re(r_1)?);
            let n = pool.add(n);
            let pref = pool.build_str_prefix(s, &n);
            let suff = pool.build_str_suffix_rem(s, &n);
            Ok(build_term!(pool,
                (or
                    (not (strinre {pref.clone()} {r_1.clone()}))
                    (not (strinre {suff.clone()} {singleton_elim(pool, r_2)}))
                )
            ))
        } else {
            unreachable!()
        }
    } else {
        Err(CheckerError::TermOfWrongForm("(re.++ ...)", r.clone()))
    }?;

    assert_eq(&conclusion[0], &expanded)
}

pub fn re_unfold_neg_concat_fixed_suffix(
    RuleArgs { premises, conclusion, pool, .. }: RuleArgs,
) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 1)?;

    match_term_err!(
        (or
            (not (strinre suff r_1))
            (not (strinre pref r_2))
        ) = &conclusion[0]
    )?;

    let term = get_premise_term(&premises[0])?;
    let (s, r) = match_term_err!((not (strinre s r)) = term)?;

    let expanded = if let Term::Op(Operator::ReConcat, args) = r.as_ref() {
        let mut args_rev = args.clone();
        args_rev.reverse();

        if let [r_1, r_2 @ ..] = &args_rev[..] {
            let n = Term::new_int(str_fixed_len_re(r_1)?);
            let n = pool.add(n);
            let suff = pool.build_str_suffix(s, &n);
            let size = build_term!(pool, (- (strlen {s.clone()}) {n.clone()}));
            let pref = pool.build_str_prefix(s, &size);
            let mut r_2_rev = r_2.to_vec();
            r_2_rev.reverse();
            Ok(build_term!(pool,
                (or
                    (not (strinre {suff.clone()} {r_1.clone()}))
                    (not (strinre {pref.clone()} {singleton_elim(pool, &r_2_rev)}))
                )
            ))
        } else {
            unreachable!()
        }
    } else {
        Err(CheckerError::TermOfWrongForm("(re.++ ...)", r.clone()))
    }?;

    assert_eq(&conclusion[0], &expanded)
}

// RCP Rules
pub fn re_convert(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    let (w1, a1) = match_term_err!((not (strinre w a1)) = &conclusion[0])?;
    let (w2, a2) = match_term_err!((strinre w a2) = &conclusion[1])?;

    assert_eq(w1, w2)?;

    let a1 = Automaton::determinize(&Automaton::create_from_regex_operators(pool, a1)?);
    let a2 = Automaton::determinize(&a2.as_automaton_err()?);

    if !operations::is_equivalent(a1.clone(), a2.clone()) {
        return Err(StringError::ExpectedEquivalentAutomata(a1, a2).into());
    }

    Ok(())
}

pub fn re_empty_intersection(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    let (w1, a1) = match_term_err!((not (strinre w a1)) = &conclusion[0])?;
    let (w2, a2) = match_term_err!((not (strinre w a2)) = &conclusion[1])?;

    assert_eq(w1, w2)?;

    let a1 = a1.as_automaton_err()?;
    let a2 = a2.as_automaton_err()?;

    if !has_reachable_accepting_state(&a1) || !has_reachable_accepting_state(&a2) {
        return Ok(());
    }

    let a1 = Automaton::determinize(&a1);
    let a2 = Automaton::determinize(&a2);
    let intersection = operations::intersection(a1.clone(), a2.clone())?;

    if has_reachable_accepting_state(&intersection) {
        return Err(StringError::ExpectedAutomataEmptyIntersection(intersection, a1, a2).into());
    }

    Ok(())
}

pub fn re_intersection(RuleArgs { premises, conclusion, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 2..)?;
    assert_clause_len(conclusion, 1)?;

    let (w_conc, conc_automaton) = match_term_err!(
        (strinre w a) = &conclusion[0]
    )?;
    let conc_automaton = conc_automaton.as_automaton_err()?;

    let mut has_empty_premise = false;
    let mut premise_automatas: Vec<Automaton> = Vec::with_capacity(premises.len());

    for premise in premises {
        let term = get_premise_term(premise)?;
        let (w, a) = match_term_err!((strinre w a1) = term)?;
        assert_eq(w, w_conc)?;

        let a = a.as_automaton_err()?;
        if !has_reachable_accepting_state(&a) {
            has_empty_premise = true;
        }

        if !has_empty_premise {
            premise_automatas.push(a);
        }
    }

    if has_empty_premise {
        if !has_reachable_accepting_state(&conc_automaton) {
            return Ok(());
        } else {
            let expected = Automaton::empty_automaton();
            return Err(StringError::ExpectedEquivalentAutomata(
                expected,
                Automaton::determinize(&conc_automaton),
            )
            .into());
        }
    }

    let mut expected = Automaton::determinize(&premise_automatas[0]);
    for automaton in &premise_automatas[1..] {
        let det_a = Automaton::determinize(automaton);
        expected = operations::intersection(expected, det_a)?;
        if !has_reachable_accepting_state(&expected) {
            break;
        }
    }

    let conc_is_empty = !has_reachable_accepting_state(&conc_automaton);
    let expected_is_empty = !has_reachable_accepting_state(&expected);
    if conc_is_empty && expected_is_empty {
        return Ok(());
    }

    let conc_automaton = Automaton::determinize(&conc_automaton);
    if !operations::is_equivalent(expected.clone(), conc_automaton.clone()) {
        return Err(StringError::ExpectedEquivalentAutomata(expected, conc_automaton).into());
    }

    Ok(())
}

pub fn re_forward_prop(RuleArgs { premises, conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 2..)?;
    assert_clause_len(conclusion, 1)?;

    let (s, conc_automaton) = match_term_err!(
        (strinre s a) = &conclusion[0]
    )?;

    let mut premise_automatas: Vec<(Rc<Term>, Rc<Term>)> = Vec::new();
    for premise in premises {
        let term = get_premise_term(premise)?;
        let (w, a) = match_term_err!((strinre w a) = term)?;
        premise_automatas.push((w.clone(), a.clone()));
    }

    let expected = Automaton::determinize(&make_automaton_from_string(pool, s, premise_automatas)?);
    let conc_automaton = Automaton::determinize(&conc_automaton.as_automaton_err()?);

    if !operations::is_equivalent(expected.clone(), conc_automaton.clone()) {
        return Err(
            StringError::ExpectedEquivalentAutomata(expected, conc_automaton.clone()).into(),
        );
    }

    Ok(())
}

pub fn concat_bwd_propagation(RuleArgs { premises, conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 2)?;
    assert_clause_len(conclusion, 1..)?;

    let p1 = get_premise_term(&premises[0])?;
    let p2 = get_premise_term(&premises[1])?;

    let (x1, ws) = match_term_err!((= x1 (strconcat ...)) = p1)?;
    let (x2, a) = match_term_err!((strinre x2 a) = p2)?;

    assert_eq(x1, x2)?;

    let a = Automaton::determinize(&Automaton::create_from_regex_operators(pool, a)?);

    for and_term in conclusion {
        let ands = match_term_err!((and ...) = and_term)?;
        assert_eq!(&ws.len(), &ands.len());

        let mut automata = Vec::new();
        for (idx, term) in ands.iter().enumerate() {
            let (w, re) = match_term_err!((strinre w re) = term)?;
            assert_eq(&ws[idx], w)?;
            automata.push(re.clone());
        }

        let re = pool.add(Term::Op(Operator::ReConcat, automata));
        let computed = Automaton::determinize(&Automaton::create_from_regex_operators(pool, &re)?);

        let intersection = operations::intersection(a.clone(), computed.clone())?;
        if !operations::has_reachable_accepting_state(&intersection) {
            return Err(
                StringError::ExpectedAutomataIntersection(a.clone(), computed.clone()).into(),
            );
        }
    }

    Ok(())
}

pub fn concat_aut_bwd_propagation(RuleArgs { premises, conclusion, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 2)?;
    assert_clause_len(conclusion, 1..)?;

    let p1 = get_premise_term(&premises[0])?;
    let p2 = get_premise_term(&premises[1])?;

    let (x2, a) = match_term_err!((strinre x2 a) = p1)?;
    let (x1, ws) = match_term_err!((= x1 (strconcat ...)) = p2)?;

    assert_eq(x1, x2)?;

    let a = a.as_automaton_err()?;

    for and_term in conclusion {
        let ands = match_term_err!((and ...) = and_term)?;
        assert_eq!(&ws.len(), &ands.len());

        for (idx, term) in ands.iter().enumerate() {
            let (w, aut) = match_term_err!((strinre w aut) = term)?;
            assert_eq(&ws[idx], w)?;

            let aut = aut.as_automaton_err()?;
            if !is_subautomaton(aut.clone(), a.clone()) {
                return Err(StringError::ExpectedSubautomaton(aut, a).into());
            }
        }
    }

    Ok(())
}

pub fn str_indexof_re_eval(
    RuleArgs {
        premises,
        conclusion,
        pool,
        automata_cache,
        ..
    }: RuleArgs,
) -> RuleResult {
    assert_num_premises(premises, 0)?;
    assert_clause_len(conclusion, 1)?;

    let (s, r, n, m) = match_term_err!((= (indexofre s r n) m) = &conclusion[0])?;

    let s = s.as_string_err()?;
    let dfa = cached_automaton(pool, automata_cache, r)?;
    let n = n.as_signed_integer_err()?;
    let m = m.as_signed_integer_err()?;

    let chars: Vec<char> = s.chars().collect();
    let len = chars.len();

    let expected: Integer = if n < 0 || n > len {
        Integer::from(-1)
    } else if dfa.accepts("") {
        n.clone()
    } else {
        let start_idx = n.to_usize().unwrap();
        let mut match_pos = None;
        'outer: for i in start_idx..len {
            for j in (i + 1)..=len {
                let substring: String = chars[i..j].iter().collect();
                if dfa.accepts(&substring) {
                    match_pos = Some(i);
                    break 'outer;
                }
            }
        }
        match match_pos {
            Some(i) => Integer::from(i),
            None => Integer::from(-1),
        }
    };

    if expected != m {
        return Err(StringError::RegexIndexOfFailed {
            s,
            regex: r.clone(),
            index: n,
            expected: m,
            got: expected,
        }
        .into());
    }

    Ok(())
}

pub fn str_replace_re_eval(
    RuleArgs {
        premises,
        conclusion,
        pool,
        automata_cache,
        ..
    }: RuleArgs,
) -> RuleResult {
    assert_num_premises(premises, 0)?;
    assert_clause_len(conclusion, 1)?;

    let (s, r, t, u) = match_term_err!((= (replacere s r t) u) = &conclusion[0])?;

    let s = s.as_string_err()?;
    let t = t.as_string_err()?;
    let u = u.as_string_err()?;

    let dfa = cached_automaton(pool, automata_cache, r)?;

    let expected = if dfa.accepts("") {
        format!("{}{}", t, s)
    } else {
        let chars: Vec<char> = s.chars().collect();
        let n = chars.len();
        let mut match_found = None;

        'outer: for i in 0..n {
            for j in (i + 1)..=n {
                let substring: String = chars[i..j].iter().collect();
                if dfa.accepts(&substring) {
                    match_found = Some((i, j));
                    break 'outer;
                }
            }
        }

        if let Some((i, j)) = match_found {
            let prefix: String = chars[0..i].iter().collect();
            let suffix: String = chars[j..n].iter().collect();
            format!("{}{}{}", prefix, t, suffix)
        } else {
            s.clone()
        }
    };

    if expected != u {
        return Err(StringError::RegexReplaceFailed {
            s,
            regex: r.clone(),
            replacement: t,
            expected: u,
            got: expected,
        }
        .into());
    }

    Ok(())
}

pub fn str_replace_re_all_eval(
    RuleArgs {
        premises,
        conclusion,
        pool,
        automata_cache,
        ..
    }: RuleArgs,
) -> RuleResult {
    assert_num_premises(premises, 0)?;
    assert_clause_len(conclusion, 1)?;

    let (s, r, t, u) = match_term_err!((= (replacereall s r t) u) = &conclusion[0])?;

    let s = s.as_string_err()?;
    let t = t.as_string_err()?;
    let u = u.as_string_err()?;

    let dfa = cached_automaton(pool, automata_cache, r)?;

    let chars: Vec<char> = s.chars().collect();
    let n = chars.len();
    let mut result = String::new();
    let mut index = 0;

    while index < n {
        let mut match_found = None;
        'outer: for i in index..n {
            for j in (i + 1)..=n {
                let substring: String = chars[i..j].iter().collect();
                if dfa.accepts(&substring) {
                    match_found = Some((i, j));
                    break 'outer;
                }
            }
        }

        if let Some((i, j)) = match_found {
            let prefix: String = chars[index..i].iter().collect();
            result.push_str(&prefix);
            result.push_str(&t);
            index = j;
        } else {
            let suffix: String = chars[index..n].iter().collect();
            result.push_str(&suffix);
            break;
        }
    }

    if result != u {
        return Err(StringError::RegexReplaceFailed {
            s,
            regex: r.clone(),
            replacement: t.clone(),
            expected: u,
            got: result,
        }
        .into());
    }

    Ok(())
}

pub fn str_in_re_eval(
    RuleArgs {
        premises,
        conclusion,
        pool,
        automata_cache,
        ..
    }: RuleArgs,
) -> RuleResult {
    assert_num_premises(premises, 0)?;
    assert_clause_len(conclusion, 1)?;

    let (s, r, c) = match_term_err!((= (strinre s r) c) = &conclusion[0])?;

    let s = s.as_string_err()?;
    let c = c.as_bool_err()?;

    let aut = cached_automaton(pool, automata_cache, r)?;
    let accepts = aut.accepts(&s);

    if accepts != c {
        return Err(StringError::RegexMatchFailed { s, regex: r.clone(), expected: c }.into());
    }

    Ok(())
}
