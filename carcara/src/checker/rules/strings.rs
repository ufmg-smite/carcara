use super::{
    assert_clause_len, assert_eq, assert_num_args, assert_num_premises, assert_polyeq_expected,
    get_premise_term, RuleArgs, RuleResult,
};
use crate::{
    ast::*,
    checker::{error::CheckerError, rules::assert_polyeq},
};
use std::{cmp, time::Duration};

/// A function that takes an `Rc<Term>` and returns a vector corresponding to
/// the flat form of that term.
///
/// In this flat form, all `str.++` applications are dissolved and every
/// argument of those applications is inserted into the vector (e.g., `(str.++
/// a (str.++ b c))` would lead to `[a, b, c]`, where `a`, `b` and `c` are
/// arbitrary String terms). Furthermore, all String constants are broken
/// into constants of size one and are inserted into the vector too.
///
/// All String terms that aren't `str.++` applications can be seen as `(str.++ term "")`.
/// So, applying `flatten` to them would lead to `[term]`. Furthermore,
/// the empty String isn't mapped to any entry in the vector, so `flatten`
/// applied to `""` leads to an empty vector.
fn string_concat_flatten(pool: &mut dyn TermPool, term: Rc<Term>) -> Vec<Rc<Term>> {
    let mut flattened = Vec::new();
    if let Term::Const(Constant::String(s)) = term.as_ref() {
        flattened.extend(
            s.chars()
                .map(|c| pool.add(Term::Const(Constant::String(c.to_string())))),
        );
    } else if let Some(args) = match_term!((strconcat ...) = term) {
        for arg in args {
            flattened.extend(string_concat_flatten(pool, arg.clone()));
        }
    } else {
        flattened.push(term.clone());
    }
    flattened
}

/// A function that takes an `Rc<Term>` and returns a vector corresponding to
/// the flat form of that term.
///
/// It works almost the same as `string_concat_flatten`, but it does not split string constants.
fn concat_extract(term: Rc<Term>) -> Vec<Rc<Term>> {
    let mut flattened = Vec::new();
    if let Term::Const(Constant::String(s)) = term.as_ref() {
        if !s.is_empty() {
            flattened.push(term.clone());
        }
    } else if let Some(args) = match_term!((strconcat ...) = term) {
        for arg in args {
            flattened.extend(concat_extract(arg.clone()));
        }
    } else {
        flattened.push(term.clone());
    }
    flattened
}

fn is_compatible(s: Vec<Rc<Term>>, t: Vec<Rc<Term>>) -> bool {
    match (&s[..], &t[..]) {
        (_, []) => true,
        ([], _) => true,
        ([h1, t1 @ ..], [h2, t2 @ ..]) => {
            if h1 == h2 {
                is_compatible(t1.to_vec(), t2.to_vec())
            } else {
                false
            }
        }
    }
}

fn overlap(s: Vec<Rc<Term>>, t: Vec<Rc<Term>>) -> usize {
    match &s[..] {
        [] | [_] => 0,
        [_, tail @ ..] => {
            if is_compatible(s.clone(), t.clone()) {
                0
            } else {
                1 + overlap(tail.to_vec(), t.clone())
            }
        }
    }
}

/// A function to standardize String constants and `str.++` applications
/// across a term.
///
/// It takes an `Rc<Term>` and returns an equivalent `Rc<Term>` where all String
/// constants of size greater than one are broken into `str.++` applications
/// of their characters (`"abc"` would become `(str.++ "a" "b" "c")`), and
/// nested `str.++` applications are dissolved, remaining just one application
/// with all the previous nested arguments (e.g., `(str.++ a (str.++ b (str.++ c "")))` would lead to `(str.++ a b c)`).
fn expand_string_constants(pool: &mut dyn TermPool, term: &Rc<Term>) -> Rc<Term> {
    match term.as_ref() {
        Term::Const(Constant::String(s)) => {
            let args: Vec<Rc<Term>> = s
                .chars()
                .map(|c| pool.add(Term::Const(Constant::String(c.to_string()))))
                .collect();
            match args.len() {
                0 => pool.add(Term::new_string("")),
                1 => args[0].clone(),
                _ => pool.add(Term::Op(Operator::StrConcat, args)),
            }
        }
        Term::Op(op, args) => match op {
            Operator::StrConcat => {
                let mut new_args = Vec::new();
                // (str.++ "a" (str.++ "b" "c")) => (str.++ "a" "b" "c")
                for arg in args {
                    new_args.extend(string_concat_flatten(pool, arg.clone()));
                }
                pool.add(Term::Op(*op, new_args))
            }
            _ => {
                let new_args = args
                    .iter()
                    .map(|a| expand_string_constants(pool, a))
                    .collect();
                pool.add(Term::Op(*op, new_args))
            }
        },
        Term::App(func, args) => {
            let new_args = args
                .iter()
                .map(|term| expand_string_constants(pool, term))
                .collect();
            pool.add(Term::App(func.clone(), new_args))
        }
        Term::Let(binding, inner) => {
            let new_inner = expand_string_constants(pool, inner);
            pool.add(Term::Let(binding.clone(), new_inner))
        }
        Term::Binder(q, bindings, inner) => {
            let new_inner = expand_string_constants(pool, inner);
            pool.add(Term::Binder(*q, bindings.clone(), new_inner))
        }
        Term::ParamOp { op, op_args, args } => {
            let new_args = args
                .iter()
                .map(|term| expand_string_constants(pool, term))
                .collect();
            pool.add(Term::ParamOp {
                op: *op,
                op_args: op_args.clone(),
                args: new_args,
            })
        }
        Term::Var(..) | Term::Const(_) | Term::Sort(_) => term.clone(),
    }
}

/// A function to reconstruct a term given its flat form.
///
/// It takes a vector of `Rc<Term>` and returns a new term based on the length
/// of the flat form vector. If the vector is empty, it's equivalent to the
/// empty String. If the length is equal to one, the only term of the vector
/// is returned. Finally, if the length is greater than one, an `str.++`
/// application is returned with the flat form vector as its arguments (e.g.,
/// `[a, "b", c]` would lead to `(str.++ a "b" c)`, where `a` and `c` are
/// arbitrary terms).
fn concat(pool: &mut dyn TermPool, terms: Vec<Rc<Term>>) -> Rc<Term> {
    match terms.len() {
        0 => pool.add(Term::new_string("")),
        1 => terms[0].clone(),
        _ => pool.add(Term::Op(Operator::StrConcat, terms)),
    }
}

/// A function to check if a term is a prefix or suffix of another.
///
/// It takes two `Rc<Term>` and a reverse parameter. If the reverse parameter is
/// set to `false`, it checks if the second term is a prefix of the first one,
/// and if it's set to `true`, it checks if it's a suffix.
///
/// The function throws an error if the prefix/suffix is larger than the main
/// term. It returns the prefix/suffix in flat form if the check was successful.
fn is_prefix_or_suffix(
    pool: &mut dyn TermPool,
    term: Rc<Term>,
    pref: Rc<Term>,
    rev: bool,
    polyeq_time: &mut Duration,
) -> Result<Vec<Rc<Term>>, CheckerError> {
    let mut t_flat = string_concat_flatten(pool, term.clone());
    let mut p_flat = string_concat_flatten(pool, pref.clone());
    if rev {
        t_flat.reverse();
        p_flat.reverse();
    }
    if p_flat.len() > t_flat.len() {
        if rev {
            return Err(CheckerError::ExpectedToBeSuffix(pref, term));
        } else {
            return Err(CheckerError::ExpectedToBePrefix(pref, term));
        }
    }
    for (i, el) in p_flat.iter().enumerate() {
        assert_polyeq_expected(el, t_flat[i].clone(), polyeq_time)?;
    }
    if rev {
        p_flat.reverse();
    }
    Ok(p_flat)
}

/// An application of `is_prefix_or_suffix` where the reverse parameter is set
/// to `false` by default.
fn is_prefix(
    pool: &mut dyn TermPool,
    term: Rc<Term>,
    pref: Rc<Term>,
    polyeq_time: &mut Duration,
) -> Result<Vec<Rc<Term>>, CheckerError> {
    is_prefix_or_suffix(pool, term, pref, false, polyeq_time)
}

/// An application of `is_prefix_or_suffix` where the reverse parameter is set
/// to `true` by default.
fn is_suffix(
    pool: &mut dyn TermPool,
    term: Rc<Term>,
    pref: Rc<Term>,
    polyeq_time: &mut Duration,
) -> Result<Vec<Rc<Term>>, CheckerError> {
    is_prefix_or_suffix(pool, term, pref, true, polyeq_time)
}

type Suffixes = (Vec<Rc<Term>>, Vec<Rc<Term>>);

/// A function to remove the longest common prefix or suffix.
///
/// It takes two `Rc<Term>` and a reverse parameter. If the parameter is set to
/// `false`, it removes the longest common prefix, and if it's set to `true`,
/// the longest common suffix.
///
/// The function throws an error if the terms aren't `str.++` applications.
/// It returns two vectors with the remaining terms after the removal in flat
/// form (e.g., the remaining suffixes after a prefix removal or vice versa).
///
/// If the terms don't share common prefixes or suffixes, the function
/// doesn't remove anything, so the tuple returned is the flat form for both of
/// them.
fn strip_prefix_or_suffix(
    pool: &mut dyn TermPool,
    s: Rc<Term>,
    t: Rc<Term>,
    rev: bool,
    polyeq_time: &mut Duration,
) -> Result<Suffixes, CheckerError> {
    let mut s_flat = string_concat_flatten(pool, s.clone());
    let mut t_flat = string_concat_flatten(pool, t.clone());
    if rev {
        s_flat.reverse();
        t_flat.reverse();
    }
    if s_flat.is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", s));
    }
    if t_flat.is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", t));
    }
    let mut prefix = 0;
    while (prefix < cmp::min(s_flat.len(), t_flat.len()))
        && polyeq(&s_flat[prefix], &t_flat[prefix], polyeq_time)
    {
        prefix += 1;
    }
    let mut s_suffix = s_flat.get(prefix..).unwrap_or_default().to_vec();
    let mut t_suffix = t_flat.get(prefix..).unwrap_or_default().to_vec();
    if rev {
        s_suffix.reverse();
        t_suffix.reverse();
    }
    Ok((s_suffix, t_suffix))
}

/// A function to check if a String has a length equal to one.
///
/// It takes an `Rc<Term>` and throws an error if the term isn't a String
/// constant (we can't compute lengths properly in this case) or isn't a String
/// constant of size one.
fn string_check_length_one(term: Rc<Term>) -> Result<(), CheckerError> {
    if let Term::Const(Constant::String(s)) = term.as_ref() {
        if s.len() == 1 {
            return Ok(());
        }
    }
    Err(CheckerError::ExpectedStringConstantOfLengthOne(term))
}

fn build_skolem_prefix(pool: &mut dyn TermPool, u: Rc<Term>, n: Rc<Term>) -> Rc<Term> {
    build_term!(pool, (strsubstr {u.clone()} 0 {n.clone()}))
}

fn build_skolem_suffix_rem(pool: &mut dyn TermPool, u: Rc<Term>, n: Rc<Term>) -> Rc<Term> {
    build_term!(pool, (strsubstr {u.clone()} {n.clone()} (- (strlen {u.clone()}) {n})))
}

fn build_skolem_suffix(pool: &mut dyn TermPool, u: Rc<Term>, n: Rc<Term>) -> Rc<Term> {
    build_term!(pool, (strsubstr {u.clone()} (- (strlen {u.clone()}) {n.clone()}) {n.clone()}))
}

fn build_skolem_unify_split_prefix(pool: &mut dyn TermPool, t: Rc<Term>, s: Rc<Term>) -> Rc<Term> {
    let t_len = pool.add(Term::Op(Operator::StrLen, vec![t.clone()]));
    let s_len = pool.add(Term::Op(Operator::StrLen, vec![s.clone()]));
    let true_branch = build_skolem_suffix_rem(pool, t.clone(), s_len).clone();
    let false_branch = build_skolem_suffix_rem(pool, s.clone(), t_len).clone();
    build_term!(pool, (ite (>= (strlen {t.clone()}) (strlen {s.clone()})) {true_branch} {false_branch}))
}

fn build_skolem_unify_split_suffix(pool: &mut dyn TermPool, t: Rc<Term>, s: Rc<Term>) -> Rc<Term> {
    let t_len = pool.add(Term::Op(Operator::StrLen, vec![t.clone()]));
    let s_len = pool.add(Term::Op(Operator::StrLen, vec![s.clone()]));
    let n_t = build_term!(pool, (- {t_len.clone()} {s_len.clone()}));
    let n_s = build_term!(pool, (- {s_len.clone()} {t_len.clone()}));
    let true_branch = build_skolem_prefix(pool, t.clone(), n_t).clone();
    let false_branch = build_skolem_prefix(pool, s.clone(), n_s).clone();
    build_term!(pool, (ite (>= (strlen {t.clone()}) (strlen {s.clone()})) {true_branch} {false_branch}))
}

fn build_str_suffix_len(pool: &mut dyn TermPool, s: Rc<Term>, n: Rc<Term>) -> Rc<Term> {
    build_term!(pool, (strsubstr {s.clone()} (- (strlen {s.clone()}) {n.clone()}) {n.clone()}))
}

/// Helper function to properly extract the arguments of the `concat_cprop` rule.
fn extract_arguments(t: &Rc<Term>) -> Result<Vec<Rc<Term>>, CheckerError> {
    let args_t = match t.as_ref() {
        Term::Op(Operator::StrConcat, args) => {
            if args.len() != 3 {
                return Err(CheckerError::TermOfWrongForm(
                    "(str.++ t1 t2 t3)",
                    t.clone(),
                ));
            }
            args
        }
        _ => {
            return Err(CheckerError::TermOfWrongForm(
                "(str.++ t1 t2 t3)",
                t.clone(),
            ))
        }
    };
    Ok(args_t.clone())
}

/// A function that takes a list of regular expressions and returns the term corresponding to the
/// application of the concatenation operator to them.
///
/// If the list contains only one regular expression, it returns it directly.
fn singleton_elim(pool: &mut dyn TermPool, r_list: Vec<Rc<Term>>) -> Rc<Term> {
    match r_list.len() {
        1 => r_list[0].clone(),
        _ => pool.add(Term::Op(Operator::ReConcat, r_list)),
    }
}

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
        let str_sort = pool.add(Term::Sort(Sort::String));
        let reglan_sort = pool.add(Term::Sort(Sort::RegLan));
        let x = pool.add(Term::new_var("x", str_sort.clone()));

        let mut and_args: Vec<Rc<Term>> = Vec::new();
        let mut concat_args: Vec<Rc<Term>> = Vec::new();
        let mut exists_binding_list: Vec<(String, Rc<Term>)> = Vec::new();

        for j in 0..i {
            let k_j = pool.add(Term::new_var(format!("k_{j}"), str_sort.clone()));
            let r_j = pool.add(Term::new_var(format!("R_{j}"), reglan_sort.clone()));
            concat_args.push(k_j.clone());
            and_args.push(build_term!(pool, (strinre {k_j.clone()} {r_j.clone()})));
            exists_binding_list.push((format!("k_{j}"), str_sort.clone()));
            exists_binding_list.push((format!("R_{j}"), reglan_sort.clone()));
        }

        concat_args.push(x.clone());
        concat_args.extend(previous_ks.clone());
        let ks_concat = pool.add(Term::Op(Operator::StrConcat, concat_args));

        let r_i = pool.add(Term::new_var(format!("R_{i}"), reglan_sort.clone()));
        exists_binding_list.push((format!("R_{i}"), reglan_sort.clone()));
        and_args.push(build_term!(pool, (strinre {x.clone()} {r_i.clone()})));
        for (j, _) in previous_rs.iter().enumerate() {
            and_args.push(
                build_term!(pool, (strinre {previous_ks[j].clone()} {previous_rs[j].clone()})),
            );
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

/// A function to calculate the fixed length of a regular expression `r` (size of strings that
/// match that RE) if it can be inferred.
///
/// It takes an `Rc<Term>` and recursively match over the regular expression operators whose length
/// can be inferred. It throws an error if the term length cannot be evaluated, i.e., if the length
/// of the term itself or one of its arguments cannot be inferred.
fn str_fixed_len_re(pool: &mut dyn TermPool, r: Rc<Term>) -> Result<usize, CheckerError> {
    fn has_same_length(
        pool: &mut dyn TermPool,
        args: &[Rc<Term>],
        r: Rc<Term>,
        ignore: Operator,
    ) -> Result<usize, CheckerError> {
        let should_ignore = |term: &Term| term.as_op().is_some_and(|(op, _)| op == ignore);
        let mut iter = args
            .iter()
            .filter(|a| !should_ignore(a))
            .map(|a| str_fixed_len_re(pool, a.clone()));
        let Some(first) = iter.next() else {
            return Err(CheckerError::LengthCannotBeEvaluated(r.clone()));
        };
        let first = first?;
        for size in iter {
            let size = size?;
            if size != first {
                return Err(CheckerError::LengthCannotBeEvaluated(r.clone()));
            }
        }
        Ok(first)
    }

    match r.as_ref() {
        Term::Op(Operator::ReConcat, args) => {
            let mut lengths = args.iter().map(|a| str_fixed_len_re(pool, a.clone()));
            lengths.try_fold(0, |acc, x| Ok(acc + x?))
        }
        Term::Op(Operator::ReAllChar, _) => Ok(1),
        Term::Op(Operator::ReRange, _) => Ok(1),
        Term::Op(Operator::StrToRe, args) => {
            let s_1 = args.first().unwrap();
            match s_1.as_ref() {
                Term::Const(Constant::String(s)) => Ok(s.len()),
                _ => Err(CheckerError::LengthCannotBeEvaluated(r.clone())),
            }
        }
        Term::Op(Operator::ReUnion, args) => {
            has_same_length(pool, args, r.clone(), Operator::ReNone)
        }
        Term::Op(Operator::ReIntersection, args) => {
            has_same_length(pool, args, r.clone(), Operator::ReAll)
        }
        _ => Err(CheckerError::LengthCannotBeEvaluated(r.clone())),
    }
}

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

    let (ss, ts) = strip_prefix_or_suffix(pool, s.clone(), t.clone(), rev, polyeq_time)?;
    let ss_concat = concat(pool, ss);
    let ts_concat = concat(pool, ts);
    let expected = build_term!(
        pool,
        (= {ss_concat.clone()} {ts_concat.clone()})
    );

    let expanded = expand_string_constants(pool, &conclusion[0]);

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

    let s_1 = is_prefix_or_suffix(pool, s.clone(), s_1.clone(), rev, polyeq_time)?;
    let t_1 = is_prefix_or_suffix(pool, t.clone(), t_1.clone(), rev, polyeq_time)?;
    let s_concat = concat(pool, s_1);
    let t_concat = concat(pool, t_1);
    let expected = build_term!(
        pool,
        (= {s_concat.clone()} {t_concat.clone()})
    );

    let expanded = expand_string_constants(pool, &conclusion[0]);

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
    let (mut ss, mut ts) = strip_prefix_or_suffix(pool, s.clone(), t.clone(), rev, polyeq_time)?;
    if rev {
        ss.reverse();
        ts.reverse();
    }

    if let Some(ss_head) = ss.first() {
        string_check_length_one(ss_head.clone())?;
        if let Some(ts_head) = ts.first() {
            string_check_length_one(ts_head.clone())?;
        }
    } else if let Some(ts_head) = ts.first() {
        string_check_length_one(ts_head.clone())?;
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
    let (t_1, _) = match_term_err!((not (= (strlen t_1) 0)) = length)?;

    let s_flat = string_concat_flatten(pool, s.clone());
    if string_concat_flatten(pool, t.clone()).is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", t.clone()));
    }
    if s_flat.is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", s.clone()));
    }

    is_prefix(pool, t.clone(), t_1.clone(), polyeq_time)?;
    let mut right_eq: Vec<Rc<Term>> = vec![];
    if let Some(c) = s_flat.first() {
        string_check_length_one(c.clone())?;
        right_eq.push(c.clone());
        let n = pool.add(Term::new_int(1));
        right_eq.push(build_skolem_suffix_rem(pool, t_1.clone(), n).clone());
    }

    let t_1 = expand_string_constants(pool, t_1);
    let right_eq_concat = concat(pool, right_eq);
    let expected = build_term!(
        pool,
        (= {t_1.clone()} {right_eq_concat.clone()})
    );

    let expanded = expand_string_constants(pool, &conclusion[0]);

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
    let (t_2, _) = match_term_err!((not (= (strlen t_2) 0)) = length)?;

    let s_flat = string_concat_flatten(pool, s.clone());
    if string_concat_flatten(pool, t.clone()).is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", t.clone()));
    }
    if s_flat.is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", s.clone()));
    }

    is_suffix(pool, t.clone(), t_2.clone(), polyeq_time)?;
    let mut right_eq: Vec<Rc<Term>> = vec![];
    if let Some(c) = s_flat.last() {
        string_check_length_one(c.clone())?;
        let n = build_term!(pool, (- (strlen {t_2.clone()}) 1));
        right_eq.push(build_skolem_prefix(pool, t_2.clone(), n).clone());
        right_eq.push(c.clone());
    }

    let t_2 = expand_string_constants(pool, t_2);
    let right_eq_concat = concat(pool, right_eq);
    let expected = build_term!(
        pool,
        (= {t_2.clone()} {right_eq_concat.clone()})
    );

    let expanded = expand_string_constants(pool, &conclusion[0]);

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

    if string_concat_flatten(pool, t.clone()).is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", t.clone()));
    }
    if string_concat_flatten(pool, s.clone()).is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", s.clone()));
    }

    is_prefix(pool, t.clone(), t_1.clone(), polyeq_time)?;
    is_prefix(pool, s.clone(), s_1.clone(), polyeq_time)?;
    let t_1 = expand_string_constants(pool, t_1);
    let s_1 = expand_string_constants(pool, s_1);
    let r = build_skolem_unify_split_prefix(pool, t_1.clone(), s_1.clone());

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
            {or.clone()}
            (not (= {r.clone()} {empty.clone()}))
            (> (strlen {r.clone()}) 0)
        )
    );

    let expanded = expand_string_constants(pool, &expanded);
    let expected = expand_string_constants(pool, &conclusion[0]);

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

    if string_concat_flatten(pool, t.clone()).is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", t.clone()));
    }
    if string_concat_flatten(pool, s.clone()).is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", s.clone()));
    }

    is_suffix(pool, t.clone(), t_2.clone(), polyeq_time)?;
    is_suffix(pool, s.clone(), s_2.clone(), polyeq_time)?;
    let t_2 = expand_string_constants(pool, t_2);
    let s_2 = expand_string_constants(pool, s_2);
    let r = build_skolem_unify_split_suffix(pool, t_2.clone(), s_2.clone());

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
            {or.clone()}
            (not (= {r.clone()} {empty.clone()}))
            (> (strlen {r.clone()}) 0)
        )
    );

    let expanded = expand_string_constants(pool, &expanded);
    let expected = expand_string_constants(pool, &conclusion[0]);

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

    if string_concat_flatten(pool, t.clone()).is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", t.clone()));
    }
    if string_concat_flatten(pool, s.clone()).is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", s.clone()));
    }

    is_prefix(pool, t.clone(), t_1.clone(), polyeq_time)?;
    is_prefix(pool, s.clone(), s_1.clone(), polyeq_time)?;
    let t_1 = expand_string_constants(pool, t_1);
    let s_1 = expand_string_constants(pool, s_1);
    let r = build_skolem_unify_split_prefix(pool, t_1.clone(), s_1.clone());

    let eq = build_term!(pool, (strconcat {s_1.clone()} {r.clone()}));
    let empty = pool.add(Term::new_string(""));
    let expanded = build_term!(
        pool,
        (and
            (= {t_1.clone()} {eq.clone()})
            (not (= {r.clone()} {empty.clone()}))
            (> (strlen {r.clone()}) 0)
        )
    );

    let expanded = expand_string_constants(pool, &expanded);
    let expected = expand_string_constants(pool, &conclusion[0]);

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

    if string_concat_flatten(pool, t.clone()).is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", t.clone()));
    }
    if string_concat_flatten(pool, s.clone()).is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", s.clone()));
    }

    is_suffix(pool, t.clone(), t_2.clone(), polyeq_time)?;
    is_suffix(pool, s.clone(), s_2.clone(), polyeq_time)?;
    let t_2 = expand_string_constants(pool, t_2);
    let s_2 = expand_string_constants(pool, s_2);
    let r = build_skolem_unify_split_suffix(pool, t_2.clone(), s_2.clone());

    let eq = build_term!(pool, (strconcat {r.clone()} {s_2.clone()}));
    let empty = pool.add(Term::new_string(""));
    let expanded = build_term!(
        pool,
        (and
            (= {t_2.clone()} {eq.clone()})
            (not (= {r.clone()} {empty.clone()}))
            (> (strlen {r.clone()}) 0)
        )
    );

    let expanded = expand_string_constants(pool, &expanded);
    let expected = expand_string_constants(pool, &conclusion[0]);

    assert_eq(&expected, &expanded)
}

pub fn concat_cprop_prefix(RuleArgs { premises, conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 2)?;
    assert_clause_len(conclusion, 1)?;

    match_term_err!((= t_1 (strconcat t_3 r)) = &conclusion[0])?;

    let terms = get_premise_term(&premises[0])?;
    let length = get_premise_term(&premises[1])?;
    let (t, s) = match_term_err!((= t s) = terms)?;
    let (t_1, _) = match_term_err!((not (= (strlen t_1) 0)) = length)?;

    let args_t = extract_arguments(t)?;

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

    let sc = string_concat_flatten(pool, ss[0].clone());
    let sc_tail = sc[1..].to_vec();

    let t_2_flat = string_concat_flatten(pool, args_t[1].clone());

    let v = 1 + overlap(sc_tail.clone(), t_2_flat.clone());
    let v = pool.add(Term::new_int(v));
    let oc = build_skolem_prefix(pool, ss[0].clone(), v);
    let oc_len = build_term!(pool, (strlen {oc.clone()}));

    let r = build_skolem_suffix_rem(pool, t_1.clone(), oc_len);
    let expanded = build_term!(pool, (= {t_1.clone()} (strconcat {oc.clone()} {r.clone()})));

    let expanded = expand_string_constants(pool, &expanded);
    let expected = expand_string_constants(pool, &conclusion[0]);

    assert_eq(&expected, &expanded)
}

pub fn concat_cprop_suffix(RuleArgs { premises, conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 2)?;
    assert_clause_len(conclusion, 1)?;

    match_term_err!((= t_2 (strconcat r t_3)) = &conclusion[0])?;

    let terms = get_premise_term(&premises[0])?;
    let length = get_premise_term(&premises[1])?;
    let (t, s) = match_term_err!((= t s) = terms)?;
    let (t_2, _) = match_term_err!((not (= (strlen t_2) 0)) = length)?;

    let args_t = extract_arguments(t)?;

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

    let mut sc = string_concat_flatten(pool, ss[1].clone());
    sc.reverse();
    let sc_tail = &sc[1..];

    let mut t_2_flat = string_concat_flatten(pool, args_t[1].clone());
    t_2_flat.reverse();

    let v = 1 + overlap(sc_tail.to_vec(), t_2_flat.clone());
    let v = pool.add(Term::new_int(v));
    let oc = build_str_suffix_len(pool, ss[1].clone(), v);

    let rhs = build_term!(pool, (- (strlen {t_2.clone()}) (strlen {oc.clone()})));
    let r = build_skolem_prefix(pool, t_2.clone(), rhs.clone());
    let expanded = build_term!(pool, (= {t_2.clone()} (strconcat {r.clone()} {oc.clone()})));

    let expanded = expand_string_constants(pool, &expanded);
    let expected = expand_string_constants(pool, &conclusion[0]);

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

    let w_1 = build_skolem_prefix(pool, t.clone(), n.clone());
    let w_2 = build_skolem_suffix_rem(pool, t.clone(), n.clone());
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
    let (((t_1, _), (t_2, _)), (t_3, _)) = match_term_err!(
        (or
            (and
                (= (strlen t) 0)
                (= t "")
            )
            (> (strlen t) 0)
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
    let (t, _) = match_term_err!((not (= t "")) = term)?;

    let (t_conc, _) = match_term_err!(
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

    let (x_conc, (s_conc, t_conc)) = match_term_err!((strinre x (reinter s t)) = &conclusion[0])?;

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
                let concat_args = concat_extract(k.clone());
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
            let concat_args = concat_extract(tk.clone());
            let new_concat = pool.add(Term::Op(Operator::StrConcat, concat_args));
            let teq = build_term!(pool, (= {t.clone()} {new_concat.clone()}));
            if m.is_bool_true() {
                Ok(teq)
            } else {
                Ok(build_term!(pool, (and {teq.clone()} {m.clone()})))
            }
        }
        _ => Err(CheckerError::TermOfWrongForm("(re.++ ...)", r.clone())),
    }?;

    println!("concluded: {}", &conclusion[0]);
    println!("epxanded: {}", &expanded);

    assert_eq(&conclusion[0], &expanded)
}

pub fn re_unfold_neg(RuleArgs { premises, conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 1)?;

    let term = get_premise_term(&premises[0])?;
    let (t, r) = match_term_err!((not (strinre t r)) = term)?;

    let int_sort = pool.add(Term::Sort(Sort::Int));
    let l = pool.add(Term::new_var("L", int_sort.clone()));
    let pref = build_skolem_prefix(pool, t.clone(), l.clone());
    let suff = build_skolem_suffix_rem(pool, t.clone(), l.clone());

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
                        (not (strinre {suff.clone()} {singleton_elim(pool, r_2.to_vec())}))
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
            let n = Term::new_int(str_fixed_len_re(pool, r_1.clone())?);
            let n = pool.add(n);
            let pref = build_skolem_prefix(pool, s.clone(), n.clone());
            let suff = build_skolem_suffix_rem(pool, s.clone(), n.clone());
            Ok(build_term!(pool,
                (or
                    (not (strinre {pref.clone()} {r_1.clone()}))
                    (not (strinre {suff.clone()} {singleton_elim(pool, r_2.to_vec())}))
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
            let n = Term::new_int(str_fixed_len_re(pool, r_1.clone())?);
            let n = pool.add(n);
            let suff = build_skolem_suffix(pool, s.clone(), n.clone());
            let size = build_term!(pool, (- (strlen {s.clone()}) {n.clone()}));
            let pref = build_skolem_prefix(pool, s.clone(), size.clone());
            let mut r_2_rev = r_2.to_vec();
            r_2_rev.reverse();
            Ok(build_term!(pool,
                (or
                    (not (strinre {suff.clone()} {r_1.clone()}))
                    (not (strinre {pref.clone()} {singleton_elim(pool, r_2_rev.clone())}))
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
