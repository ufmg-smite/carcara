use super::{
    assert_clause_len, assert_eq, assert_num_args, assert_num_premises, assert_polyeq_expected,
    get_premise_term, RuleArgs, RuleResult,
};
use crate::{ast::*, checker::error::CheckerError};
use rug::Integer;
use std::{cmp, time::Duration};

fn flatten(pool: &mut dyn TermPool, term: Rc<Term>) -> Vec<Rc<Term>> {
    let mut flattened = Vec::new();
    if let Term::Const(Constant::String(s)) = term.as_ref() {
        flattened.extend(
            s.chars()
                .map(|c| pool.add(Term::Const(Constant::String(c.to_string())))),
        );
    } else if let Some(args) = match_term!((strconcat ...) = term) {
        for arg in args {
            flattened.extend(flatten(pool, arg.clone()));
        }
    } else {
        flattened.push(term.clone());
    }
    flattened
}

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
                    new_args.extend(flatten(pool, arg.clone()));
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
            let new_op_args = op_args
                .iter()
                .map(|term| expand_string_constants(pool, term))
                .collect();
            let new_args = args
                .iter()
                .map(|term| expand_string_constants(pool, term))
                .collect();
            pool.add(Term::ParamOp {
                op: *op,
                op_args: new_op_args,
                args: new_args,
            })
        }
        Term::Var(..) | Term::Const(_) | Term::Sort(_) => term.clone(),
    }
}

fn concat(pool: &mut dyn TermPool, terms: Vec<Rc<Term>>) -> Rc<Term> {
    match terms.len() {
        0 => pool.add(Term::new_string("")),
        1 => terms[0].clone(),
        _ => pool.add(Term::Op(Operator::StrConcat, terms)),
    }
}

fn is_prefix_or_suffix(
    pool: &mut dyn TermPool,
    term: Rc<Term>,
    pref: Rc<Term>,
    rev: bool,
    polyeq_time: &mut Duration,
) -> Result<Vec<Rc<Term>>, CheckerError> {
    let mut t_flat = flatten(pool, term.clone());
    let mut p_flat = flatten(pool, pref.clone());
    if rev {
        t_flat.reverse();
        p_flat.reverse();
    }
    if p_flat.len() > t_flat.len() {
        return Err(CheckerError::ExpectedToBePrefix(pref, term));
    }
    for (i, el) in p_flat.iter().enumerate() {
        assert_polyeq_expected(el, t_flat[i].clone(), polyeq_time)?;
    }
    if rev {
        p_flat.reverse();
    }
    Ok(p_flat)
}

fn is_prefix(
    pool: &mut dyn TermPool,
    term: Rc<Term>,
    pref: Rc<Term>,
    polyeq_time: &mut Duration,
) -> Result<Vec<Rc<Term>>, CheckerError> {
    is_prefix_or_suffix(pool, term, pref, false, polyeq_time)
}

fn is_suffix(
    pool: &mut dyn TermPool,
    term: Rc<Term>,
    pref: Rc<Term>,
    polyeq_time: &mut Duration,
) -> Result<Vec<Rc<Term>>, CheckerError> {
    is_prefix_or_suffix(pool, term, pref, true, polyeq_time)
}

type Suffixes = (Vec<Rc<Term>>, Vec<Rc<Term>>);

fn strip_prefix_or_suffix(
    pool: &mut dyn TermPool,
    s: Rc<Term>,
    t: Rc<Term>,
    rev: bool,
    polyeq_time: &mut Duration,
) -> Result<Suffixes, CheckerError> {
    let mut s_flat = flatten(pool, s.clone());
    let mut t_flat = flatten(pool, t.clone());
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

    let term = get_premise_term(&premises[0])?;
    let rev = args[0].as_term()?.as_bool_err()?;
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

    let term = get_premise_term(&premises[0])?;
    let prefixes = get_premise_term(&premises[1])?;
    let rev = args[0].as_term()?.as_bool_err()?;
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
    let rev = args[0].as_term()?.as_bool_err()?;
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

pub fn concat_csplit(
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

    let terms = get_premise_term(&premises[0])?;
    let length = get_premise_term(&premises[1])?;
    let rev = args[0].as_term()?.as_bool_err()?;
    let (t, s) = match_term_err!((= t s) = terms)?;
    let (u, zero) = match_term_err!((not (= (strlen u) zero)) = length)?;
    if zero.as_integer_err()? != 0 {
        return Err(CheckerError::ExpectedInteger(
            Integer::from(0),
            zero.clone(),
        ));
    }

    let mut s_flat = flatten(pool, s.clone());
    if flatten(pool, t.clone()).is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", t.clone()));
    }
    if s_flat.is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", s.clone()));
    }

    if rev {
        s_flat.reverse();
    }

    let left_eq = is_prefix_or_suffix(pool, t.clone(), u.clone(), rev, polyeq_time)?;
    let mut right_eq: Vec<Rc<Term>> = vec![];
    if let Some(s_head) = s_flat.first() {
        string_check_length_one(s_head.clone())?;
        if rev {
            let n = build_term!(pool, (- (strlen {u.clone()}) 1));
            right_eq.push(build_skolem_prefix(pool, u.clone(), n).clone());
            right_eq.push(s_head.clone());
        } else {
            right_eq.push(s_head.clone());
            let n = pool.add(Term::new_int(1));
            right_eq.push(build_skolem_suffix_rem(pool, u.clone(), n).clone());
        }
    }

    let left_eq_concat = concat(pool, left_eq);
    let right_eq_concat = concat(pool, right_eq);
    let expected = build_term!(
        pool,
        (= {left_eq_concat.clone()} {right_eq_concat.clone()})
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

    if flatten(pool, t.clone()).is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", t.clone()));
    }
    if flatten(pool, s.clone()).is_empty() {
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

    if flatten(pool, t.clone()).is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", t.clone()));
    }
    if flatten(pool, s.clone()).is_empty() {
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

mod tests {
    #[test]
    fn concat_eq() {
        test_cases! {
            definitions = "
                (declare-fun a () String)
                (declare-fun b () String)
                (declare-fun c () String)
            ",
            "Simple working examples" {
                r#"(assume h1 (= "0A" (str.++ "0" (str.from_code (str.len a)))))
                   (step t1 (cl (= "A" (str.from_code (str.len a)))) :rule concat_eq :premises (h1) :args (false))"#: true,
                r#"(assume h1 (= (str.++ "0" "A") (str.++ "0" (str.from_code (str.len a)))))
                   (step t1 (cl (= "A" (str.from_code (str.len a)))) :rule concat_eq :premises (h1) :args (false))"#: true,
                r#"(assume h1 (= (str.++ "A" (str.++ b "A")) (str.++ "AA" (str.at c (str.len c)))))
                   (step t1 (cl (= (str.++ b "A") (str.++ "A" (str.at c (str.len c))))) :rule concat_eq :premises (h1) :args (false))"#: true,
            }
            "Term are not a str.++ application" {
                r#"(assume h1 (= (str.++ "0" (str.from_int (str.len c))) ""))
                   (step t1 (cl (= (str.from_int (str.len c)) "")) :rule concat_eq :premises (h1) :args (false))"#: false,
                r#"(assume h1 (= "0" (str.++ "" (str.from_int (str.len b)))))
                   (step t1 (cl (= "" (str.from_int (str.len b)))) :rule concat_eq :premises (h1) :args (false))"#: false,
            }
            "Terms with no common prefixes" {
                r#"(assume h1 (= "yxzw" (str.++ "xy" "z" a)))
                   (step t1 (cl (= "yxzw" (str.++ "xy" "z" a))) :rule concat_eq :premises (h1) :args (false))"#: true,
                r#"(assume h1 (= (str.++ a (str.from_int (str.len b))) (str.++ "0" (str.++ "A" c))))
                   (step t1 (cl (= (str.++ a (str.from_int (str.len b))) (str.++ "0" (str.++ "A" c)))) :rule concat_eq :premises (h1) :args (false))"#: true,
            }
            "Concatenation with more than 2 arguments" {
                r#"(assume h1 (= "xyzw" (str.++ "xy" "z" a)))
                   (step t1 (cl (= "w" a)) :rule concat_eq :premises (h1) :args (false))"#: true,
                r#"(assume h1 (= "xyzw" (str.++ "x" (str.++ "y" "z") a)))
                   (step t1 (cl (= "w" a)) :rule concat_eq :premises (h1) :args (false))"#: true,
            }
            "Reverse argument set to true" {
                r#"(assume h1 (= "wzyx" (str.++ a "z" "yx")))
                   (step t1 (cl (= "w" a)) :rule concat_eq :premises (h1) :args (true))"#: true,
                r#"(assume h1 (= (str.++ "A" (str.++ b "A")) (str.++ (str.at c (str.len c)) "AA")))
                   (step t1 (cl (= (str.++ "A" b) (str.++ (str.at c (str.len c)) "A"))) :rule concat_eq :premises (h1) :args (true))"#: true,
                r#"(assume h1 (= (str.++ (str.from_int (str.len c)) "0") "0"))
                   (step t1 (cl (= (str.from_int (str.len c)) "")) :rule concat_eq :premises (h1) :args (true))"#: true,
                r#"(assume h1 (= "0" (str.++ (str.from_int (str.len b)) "0")))
                   (step t1 (cl (= "" (str.from_int (str.len b)))) :rule concat_eq :premises (h1) :args (true))"#: true,
            }
            "Invalid argument type" {
                r#"(assume h1 (not (= "xyzw" (str.++ "xy" (str.++ "z" a)))))
                   (step t1 (cl (= "w" a)) :rule concat_eq :premises (h1) :args (1))"#: false,
                r#"(assume h1 (not (= "xyzw" (str.++ "xy" (str.++ "z" a)))))
                   (step t1 (cl (= "w" a)) :rule concat_eq :premises (h1) :args (1.5))"#: false,
                r#"(assume h1 (not (= "xyzw" (str.++ "xy" (str.++ "z" a)))))
                   (step t1 (cl (= "w" a)) :rule concat_eq :premises (h1) :args ((- 1)))"#: false,
                r#"(assume h1 (not (= "xyzw" (str.++ "xy" (str.++ "z" a)))))
                   (step t1 (cl (= "w" a)) :rule concat_eq :premises (h1) :args ("test"))"#: false,
            }
            "Premise term is not an equality" {
                r#"(assume h1 (not (= "xyzw" (str.++ "xy" (str.++ "z" a)))))
                   (step t1 (cl (= "w" a)) :rule concat_eq :premises (h1) :args (false))"#: false,
            }
            "Conclusion term is not an equality" {
                r#"(assume h1 (= "xyzw" (str.++ "xy" "z" a)))
                   (step t1 (cl (not (= "w" a))) :rule concat_eq :premises (h1) :args (false))"#: false,
            }
            "Switched conclusion terms" {
                r#"(assume h1 (= "xyzw" (str.++ "xy" (str.++ "z" a))))
                   (step t1 (cl (= a "w")) :rule concat_eq :premises (h1) :args (false))"#: false,
                r#"(assume h1 (= (str.++ "xy" (str.++ "z" a)) (str.++ "x" "yzw")))
                   (step t1 (cl (= "w" a)) :rule concat_eq :premises (h1) :args (false))"#: false,
                r#"(assume h1 (= (str.++ "A" (str.++ b "A")) (str.++ "AA" (str.at c (str.len c)))))
                   (step t1 (cl (= (str.++ "A" (str.at c (str.len c))) (str.++ b "A"))) :rule concat_eq :premises (h1) :args (false))"#: false,
            }
            "Prefix was not fully consumed" {
                r#"(assume h1 (= (str.++ "a" "b" b (str.++ "c" "d")) (str.++ "a" "b" (str.++ b c))))
                   (step t1 (cl (= (str.++ b "cd") (str.++ b c))) :rule concat_eq :premises (h1) :args (false))"#: false,
                r#"(assume h1 (= (str.++ "A" (str.++ b "AA")) (str.++ (str.at c (str.len c)) "AA")))
                   (step t1 (cl (= (str.++ "A" (str.++ b "A")) (str.++ (str.at c (str.len c)) "A"))) :rule concat_eq :premises (h1) :args (true))"#: false,
            }
            "Inverted argument value" {
                r#"(assume h1 (= (str.++ "w" (str.++ "z" "y" "x")) (str.++ a "z" "yx")))
                   (step t1 (cl (= "w" a)) :rule concat_eq :premises (h1) :args (false))"#: false,
                r#"(assume h1 (= (str.++ "A" (str.++ b "A")) (str.++ (str.at c (str.len c)) "AA")))
                   (step t1 (cl (= (str.++ "A" b) (str.++ (str.at c (str.len c)) "A"))) :rule concat_eq :premises (h1) :args (false))"#: false,
            }
        }
    }

    #[test]
    fn concat_unify() {
        test_cases! {
            definitions = "
                (declare-fun a () String)
                (declare-fun b () String)
                (declare-fun c () String)
                (declare-fun d () String)
            ",
            "Simple working examples" {
                r#"(assume h1 (= "abcd" "abcd"))
                   (assume h2 (= (str.len "abc") (str.len "abc")))
                   (step t1 (cl (= "abc" "abc")) :rule concat_unify :premises (h1 h2) :args (false))"#: true,
                r#"(assume h1 (= (str.++ "a" b "c" (str.++ d "e")) (str.++ "a" c "de")))
                   (assume h2 (= (str.len (str.++ "a" b)) (str.len "a")))
                   (step t1 (cl (= (str.++ "a" b) "a")) :rule concat_unify :premises (h1 h2) :args (false))"#: true,
                r#"(assume h1 (= (str.++ a b c) d))
                   (assume h2 (= (str.len (str.++ a b)) (str.len "")))
                   (step t1 (cl (= (str.++ a b) "")) :rule concat_unify :premises (h1 h2) :args (false))"#: true,
            }
            "Reverse argument set to true" {
                r#"(assume h1 (= "abcd" "abcd"))
                   (assume h2 (= (str.len "cd") (str.len "cd")))
                   (step t1 (cl (= "cd" "cd")) :rule concat_unify :premises (h1 h2) :args (true))"#: true,
                r#"(assume h1 (= (str.++ "a" b "c" (str.++ d "e")) (str.++ "a" c "de")))
                   (assume h2 (= (str.len (str.++ d "e")) (str.len (str.++ "d" "e"))))
                   (step t1 (cl (= (str.++ d "e") "de")) :rule concat_unify :premises (h1 h2) :args (true))"#: true,
            }
            "Failing examples" {
                r#"(assume h1 (= (str.++ "a" b "c" (str.++ d "e")) (str.++ a c "de")))
                   (assume h2 (= (str.len (str.++ "a" "b")) (str.len a)))
                   (step t1 (cl (= (str.++ "a" b) a)) :rule concat_unify :premises (h1 h2) :args (false))"#: false,
                r#"(assume h1 (= (str.++ "a" b "c" (str.++ d "e")) (str.++ a c "de")))
                   (assume h2 (= (str.len (str.++ "a" "b")) (str.len a)))
                   (step t1 (cl (= (str.++ a b) "")) :rule concat_unify :premises (h1 h2) :args (false))"#: false,
            }
            "Invalid argument type" {
                r#"(assume h1 (= (str.++ a "b" c) (str.++ a d "e")))
                   (assume h2 (= (str.len a) (str.len "")))
                   (step t1 (cl (= a "")) :rule concat_unify :premises (h1 h2) :args (1))"#: false,
                r#"(assume h1 (= (str.++ a "b" c) (str.++ a d "e")))
                   (assume h2 (= (str.len a) (str.len "")))
                   (step t1 (cl (= a "")) :rule concat_unify :premises (h1 h2) :args ((- 1)))"#: false,
                r#"(assume h1 (= (str.++ a "b" c) (str.++ a d "e")))
                   (assume h2 (= (str.len a) (str.len "")))
                   (step t1 (cl (= a "")) :rule concat_unify :premises (h1 h2) :args ("test"))"#: false,
            }
            "Premise term is not an equality" {
                r#"(assume h1 (not (= (str.++ a "b" c) (str.++ a d "e"))))
                   (assume h2 (= (str.len a) (str.len "")))
                   (step t1 (cl (= a "")) :rule concat_unify :premises (h1 h2) :args (false))"#: false,
                r#"(assume h1 (= (str.++ a "b" c) (str.++ a d "e")))
                   (assume h2 (not (= (str.len a) (str.len ""))))
                   (step t1 (cl (= a "")) :rule concat_unify :premises (h1 h2) :args (false))"#: false,
            }
            "Conclusion term is not an equality" {
                r#"(assume h1 (= (str.++ a "b" c) (str.++ a d "e")))
                   (assume h2 (= (str.len a) (str.len "")))
                   (step t1 (cl (not (= a ""))) :rule concat_unify :premises (h1 h2) :args (false))"#: false,
            }
            "Switched conclusion terms" {
                r#"(assume h1 (= (str.++ "a" b "c" (str.++ d "e")) (str.++ "a" c "de")))
                   (assume h2 (= (str.len (str.++ "a" b)) (str.len "a")))
                   (step t1 (cl (= "a" (str.++ "a" b))) :rule concat_unify :premises (h1 h2) :args (false))"#: false,
                r#"(assume h1 (= (str.++ "a" c "de") (str.++ "a" b "c" (str.++ d "e"))))
                   (assume h2 (= (str.len "a") (str.len (str.++ "a" b))))
                   (step t1 (cl (= (str.++ "a" b) "a")) :rule concat_unify :premises (h1 h2) :args (false))"#: false,
            }
            "Inverted argument value" {
                r#"(assume h1 (= (str.++ "x" (str.++ a "y") b) (str.++ "x" c "de")))
                   (assume h2 (= (str.len (str.++ "y" b)) (str.len (str.++ c "d"))))
                   (step t1 (cl (= (str.++ "y" b) (str.++ c "d"))) :rule concat_unify :premises (h1 h2) :args (false))"#: false,
                r#"(assume h1 (= (str.++ "a" b "c" (str.++ d "e")) (str.++ "a" c "de")))
                   (assume h2 (= (str.len (str.++ d "e")) (str.len (str.++ c "de"))))
                   (step t1 (cl (= (str.++ d "e") (str.++ c "de"))) :rule concat_unify :premises (h1 h2) :args (false))"#: false,
            }
            "Invalid prefixes" {
                r#"(assume h1 (= (str.++ "a" b "c" (str.++ d "e")) (str.++ "a" c "de")))
                   (assume h2 (= (str.len (str.++ "a" "b")) (str.len "a")))
                   (step t1 (cl (= (str.++ "a" "b") "a")) :rule concat_unify :premises (h1 h2) :args (false))"#: false,
                r#"(assume h1 (= (str.++ "a" b "c" (str.++ d "e")) (str.++ "a" c "de")))
                   (assume h2 (= (str.len (str.++ "a" b)) (str.len "b")))
                   (step t1 (cl (= (str.++ "a" b) "b")) :rule concat_unify :premises (h1 h2) :args (false))"#: false,
            }
            "Prefix is bigger than the term" {
                r#"(assume h1 (= (str.++ "a" b "c") (str.++ "a" c "de")))
                   (assume h2 (= (str.len (str.++ "a" b "c" "d")) (str.len (str.++ "a" c))))
                   (step t1 (cl (= (str.++ "a" b "c" "d") (str.++ "a" c))) :rule concat_unify :premises (h1 h2) :args (false))"#: false,
                r#"(assume h1 (= (str.++ "a" b "c") (str.++ "a" c "de")))
                   (assume h2 (= (str.len (str.++ "a" b)) (str.len (str.++ "a" c "de" "f"))))
                   (step t1 (cl (= (str.++ "a" b) (str.++ "a" c (str.++ "de" "f")))) :rule concat_unify :premises (h1 h2) :args (false))"#: false,
            }
        }
    }

    #[test]
    fn concat_conflict() {
        test_cases! {
            definitions = "
                (declare-fun a () String)
                (declare-fun b () String)
                (declare-fun c () String)
                (declare-fun d () String)
                (declare-fun e () String)
            ",
            "Simple working examples" {
                r#"(assume h1 (= (str.++ "ab" c) (str.++ "c" e)))
                   (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: true,
                r#"(assume h1 (= (str.++ "abc" d) (str.++ "abd" (str.++ c e))))
                   (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: true,
                r#"(assume h1 (= (str.++ "ac" (str.++ b d)) (str.++ "abd" (str.++ a b))))
                   (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: true,
            }
            "Reverse argument set to true" {
                r#"(assume h1 (= (str.++ d "cba") (str.++ (str.++ e c) "dba")))
                   (step t1 (cl false) :rule concat_conflict :premises (h1) :args (true))"#: true,
                r#"(assume h1 (= (str.++ (str.++ d b) "ac") (str.++ (str.++ b a) "dba")))
                   (step t1 (cl false) :rule concat_conflict :premises (h1) :args (true))"#: true,
            }
            "All possible constants are prefixes of each other" {
                r#"(assume h1 (= (str.++ "ac" "bd" c e) (str.++ "acb" b c)))
                   (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: false,
                r#"(assume h1 (= (str.++ "d" a b) (str.++ "de" c d)))
                   (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: false,
                r#"(assume h1 (= (str.++ "ab" a b) (str.++ "ab" c d)))
                   (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: false,
            }
            "Remaining suffix is empty" {
                r#"(assume h1 (= "ab" (str.++ "ab" c d)))
                   (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: false,
                r#"(assume h1 (= "ab" (str.++ "ab" (str.++ "" c d))))
                   (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: false,
                r#"(assume h1 (= "cbd" (str.++ "c" "bd")))
                   (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: false,
                r#"(assume h1 (= (str.++ "cbd" a) (str.++ "c" (str.++ "bd" a))))
                   (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: false,
                r#"(assume h1 (= (str.++ "ab" c d) "ab"))
                   (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: false,
                r#"(assume h1 (= (str.++ "ab" (str.++ "" c d)) "ab"))
                   (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: false,
            }
            "Term does not have a constant prefix" {
                r#"(assume h1 (= (str.++ a "bc" d) (str.++ "ab" c)))
                   (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: false,
                r#"(assume h1 (= (str.++ "b" "cd" e) (str.++ b "cb" e)))
                   (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: false,
            }
            "Term are not a str.++ application" {
                r#"(assume h1 (= (str.++ "ac" "bd" c e) ""))
                   (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: false,
                r#"(assume h1 (= "" (str.++ "ab" c)))
                   (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: false,
            }
            "Invalid argument type" {
                r#"(assume h1 (= (str.++ "ab" c) (str.++ "c" e)))
                   (step t1 (cl false) :rule concat_conflict :premises (h1) :args (1))"#: false,
                r#"(assume h1 (= (str.++ "ab" c) (str.++ "c" e)))
                   (step t1 (cl false) :rule concat_conflict :premises (h1) :args (1.5))"#: false,
                r#"(assume h1 (= (str.++ "ab" c) (str.++ "c" e)))
                   (step t1 (cl false) :rule concat_conflict :premises (h1) :args ((- 1)))"#: false,
                r#"(assume h1 (= (str.++ "ab" c) (str.++ "c" e)))
                   (step t1 (cl false) :rule concat_conflict :premises (h1) :args ("test"))"#: false,
            }
            "Premise term is not an equality" {
                r#"(assume h1 (not (= (str.++ "ab" c) (str.++ "c" e))))
                   (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: false,
            }
            "Conclusion term is not the false bool constant" {
                r#"(assume h1 (= (str.++ "ab" c) (str.++ "c" e)))
                   (step t1 (cl true) :rule concat_conflict :premises (h1) :args (false))"#: false,
                r#"(assume h1 (= (str.++ "ab" c) (str.++ "c" e)))
                   (step t1 (cl (= "a" b)) :rule concat_conflict :premises (h1) :args (false))"#: false,
                r#"(assume h1 (= (str.++ "ab" c) (str.++ "c" e)))
                   (step t1 (cl (= "a" "b")) :rule concat_conflict :premises (h1) :args (false))"#: false,
                r#"(assume h1 (= (str.++ "ab" c) (str.++ "c" e)))
                   (step t1 (cl (not (= "a" "b"))) :rule concat_conflict :premises (h1) :args (false))"#: false,
            }
            "Inverted argument value" {
                r#"(assume h1 (= (str.++ "ab" c) (str.++ "c" e)))
                   (step t1 (cl false) :rule concat_conflict :premises (h1) :args (true))"#: false,
                r#"(assume h1 (= (str.++ "abc" d) (str.++ "abd" (str.++ c e))))
                   (step t1 (cl false) :rule concat_conflict :premises (h1) :args (true))"#: false,
                r#"(assume h1 (= (str.++ d "cba") (str.++ (str.++ e c) "dba")))
                   (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: false,
                r#"(assume h1 (= (str.++ (str.++ d b) "ac") (str.++ (str.++ b a) "dba")))
                   (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: false,
            }
        }
    }

    #[test]
    fn concat_csplit() {
        test_cases! {
            definitions = "
                (declare-fun a () String)
                (declare-fun b () String)
                (declare-fun c () String)
                (declare-fun d () String)
            ",
            "Simple working examples" {
                r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
                   (assume h2 (not (= (str.len "a") 0)))
                   (step t1 (cl (= "a" (str.++ "a" (str.substr "a" 1 (- (str.len "a") 1))))) :rule concat_csplit :premises (h1 h2) :args (false))"#: true,
                r#"(assume h1 (= (str.++ a "b" c) (str.++ "ab" c)))
                   (assume h2 (not (= (str.len (str.++ a "b")) 0)))
                   (step t1 (cl (= (str.++ a "b") (str.++ "a" (str.substr (str.++ a "b") 1 (- (str.len (str.++ a "b")) 1))))) :rule concat_csplit :premises (h1 h2) :args (false))"#: true,
                r#"(assume h1 (= (str.++ d (str.++ c (str.++ b "a"))) (str.++ "b" (str.++ "c" d))))
                   (assume h2 (not (= (str.len (str.++ d c)) 0)))
                   (step t1 (cl (= (str.++ d c) (str.++ "b" (str.substr (str.++ d c) 1 (- (str.len (str.++ d c)) 1))))) :rule concat_csplit :premises (h1 h2) :args (false))"#: true,
            }
            "Reverse argument set to true" {
                r#"(assume h1 (= (str.++ "c" "b" a) (str.++ "a" (str.++ c "b"))))
                   (assume h2 (not (= (str.len (str.++ "b" a)) 0)))
                   (step t1 (cl (= (str.++ "b" a) (str.++ (str.substr (str.++ "b" a) 0 (- (str.len (str.++ "b" a)) 1)) "b"))) :rule concat_csplit :premises (h1 h2) :args (true))"#: true,
                r#"(assume h1 (= (str.++ d (str.++ c (str.++ "b" a))) (str.++ "b" (str.++ "c" "de"))))
                   (assume h2 (not (= (str.len (str.++ c (str.++ "b" a))) 0)))
                   (step t1 (cl (= (str.++ c (str.++ "b" a)) (str.++ (str.substr (str.++ c (str.++ "b" a)) 0 (- (str.len (str.++ c (str.++ "b" a))) 1)) "e"))) :rule concat_csplit :premises (h1 h2) :args (true))"#: true,
            }
            "Term does not have a constant prefix" {
                r#"(assume h1 (= (str.++ d (str.++ c (str.++ b "a"))) (str.++ b (str.++ "c" d))))
                   (assume h2 (not (= (str.len (str.++ d c)) 0)))
                   (step t1 (cl (= (str.++ d c) (str.++ b (str.substr (str.++ d c) 1 (- (str.len (str.++ d c)) 1))))) :rule concat_csplit :premises (h1 h2) :args (false))"#: false,
            }
            "Term are not a str.++ application" {
                r#"(assume h1 (= (str.++ "a" "b" b) ""))
                   (assume h2 (not (= (str.len "a") 0)))
                   (step t1 (cl (= "a" (str.++ "a" (str.substr "a" 1 (- (str.len "a") 1))))) :rule concat_csplit :premises (h1 h2) :args (false))"#: false,
                r#"(assume h1 (= "" (str.++ "a" c)))
                   (assume h2 (not (= (str.len "a") 0)))
                   (step t1 (cl (= "a" (str.++ "a" (str.substr "a" 1 (- (str.len "a") 1))))) :rule concat_csplit :premises (h1 h2) :args (false))"#: false,
            }
            "Invalid argument type" {
                r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
                   (assume h2 (not (= (str.len "a") 0)))
                   (step t1 (cl (= "a" (str.++ "a" (str.substr "a" 1 (- (str.len "a") 1))))) :rule concat_csplit :premises (h1 h2) :args (1))"#: false,
                r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
                   (assume h2 (not (= (str.len "a") 0)))
                   (step t1 (cl (= "a" (str.++ "a" (str.substr "a" 1 (- (str.len "a") 1))))) :rule concat_csplit :premises (h1 h2) :args (1.5))"#: false,
                r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
                   (assume h2 (not (= (str.len "a") 0)))
                   (step t1 (cl (= "a" (str.++ "a" (str.substr "a" 1 (- (str.len "a") 1))))) :rule concat_csplit :premises (h1 h2) :args ((- 1)))"#: false,
                r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
                   (assume h2 (not (= (str.len "a") 0)))
                   (step t1 (cl (= "a" (str.++ "a" (str.substr "a" 1 (- (str.len "a") 1))))) :rule concat_csplit :premises (h1 h2) :args ("test"))"#: false,
            }
            "Premise term is not an equality" {
                r#"(assume h1 (not (= (str.++ d (str.++ c (str.++ b "a"))) (str.++ "b" (str.++ "c" d)))))
                   (assume h2 (not (= (str.len (str.++ d c)) 0)))
                   (step t1 (cl (= (str.++ d c) (str.++ "b" (str.substr (str.++ d c) 1 (- (str.len (str.++ d c)) 1))))) :rule concat_csplit :premises (h1 h2) :args (false))"#: false,
            }
            "Premise term is not an inequality of the form (not (= (str.len str) 0))" {
                r#"(assume h1 (= (str.++ d (str.++ c (str.++ b "a"))) (str.++ "b" (str.++ "c" d))))
                   (assume h2 (= (str.len (str.++ d c)) 0))
                   (step t1 (cl (= (str.++ d c) (str.++ "b" (str.substr (str.++ d c) 1 (- (str.len (str.++ d c)) 1))))) :rule concat_csplit :premises (h1 h2) :args (false))"#: false,
                r#"(assume h1 (= (str.++ d (str.++ c (str.++ b "a"))) (str.++ "b" (str.++ "c" d))))
                   (assume h2 (not (= (str.len (str.++ d c)) 1)))
                   (step t1 (cl (= (str.++ d c) (str.++ "b" (str.substr (str.++ d c) 1 (- (str.len (str.++ d c)) 1))))) :rule concat_csplit :premises (h1 h2) :args (false))"#: false,
            }
            "Conclusion term is not an equality" {
                r#"(assume h1 (= (str.++ d (str.++ c (str.++ b "a"))) (str.++ "b" (str.++ "c" d))))
                   (assume h2 (not (= (str.len (str.++ d c)) 0)))
                   (step t1 (cl (not (= (str.++ d c) (str.++ "b" (str.substr (str.++ d c) 1 (- (str.len (str.++ d c)) 1)))))) :rule concat_csplit :premises (h1 h2) :args (false))"#: false,
            }
            "Switched conclusion terms" {
                r#"(assume h1 (= (str.++ d (str.++ c (str.++ b "a"))) (str.++ "b" (str.++ "c" d))))
                   (assume h2 (not (= (str.len (str.++ d c)) 0)))
                   (step t1 (cl (= (str.++ "b" (str.substr (str.++ d c) 1 (- (str.len (str.++ d c)) 1))) (str.++ d c))) :rule concat_csplit :premises (h1 h2) :args (false))"#: false,
                r#"(assume h1 (= (str.++ d (str.++ c (str.++ "b" a))) (str.++ "b" (str.++ "c" "de"))))
                   (assume h2 (not (= (str.len (str.++ c (str.++ "b" a))) 0)))
                   (step t1 (cl (= (str.++ (str.substr (str.++ c (str.++ "b" a)) 0 (- (str.len (str.++ c (str.++ "b" a))) 1)) "e") (str.++ c (str.++ "b" a)))) :rule concat_csplit :premises (h1 h2) :args (true))"#: false,
            }
            "Inverted argument value" {
                r#"(assume h1 (= (str.++ d (str.++ c (str.++ b "a"))) (str.++ "b" (str.++ "c" d))))
                   (assume h2 (not (= (str.len (str.++ d c)) 0)))
                   (step t1 (cl (= (str.++ d c) (str.++ "b" (str.substr (str.++ d c) 0 (- (str.len (str.++ d c)) 1))))) :rule concat_csplit :premises (h1 h2) :args (true))"#: false,
                r#"(assume h1 (= (str.++ d (str.++ c (str.++ "b" a))) (str.++ "b" (str.++ "c" "de"))))
                   (assume h2 (not (= (str.len (str.++ c (str.++ "b" a))) 0)))
                   (step t1 (cl (= (str.++ c (str.++ "b" a)) (str.++ (str.substr (str.++ c (str.++ "b" a)) 1 (- (str.len (str.++ c (str.++ "b" a))) 1)) "e"))) :rule concat_csplit :premises (h1 h2) :args (false))"#: false,
            }
        }
    }

    #[test]
    fn concat_split_prefix() {
        test_cases! {
            definitions = "
                (declare-fun a () String)
                (declare-fun b () String)
                (declare-fun c () String)
                (declare-fun d () String)
                (declare-fun e () String)
            ",
            "Simple working examples" {
                r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
                   (assume h2 (not (= (str.len "a") (str.len (str.++ "a" c)))))
                   (define-fun r_skolem () String (ite (>= (str.len "a") (str.len (str.++ "a" c))) (str.substr "a" (str.len (str.++ "a" c)) (- (str.len "a") (str.len (str.++ "a" c)))) (str.substr (str.++ "a" c) (str.len "a") (- (str.len (str.++ "a" c)) (str.len "a")))))
                   (step t1 (cl (and (or (= "a" (str.++ "a" c r_skolem)) (= (str.++ "a" c) (str.++ "a" r_skolem))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_prefix :premises (h1 h2))"#: true,
                r#"(assume h1 (= (str.++ a b c) (str.++ c d e)))
                   (assume h2 (not (= (str.len (str.++ a b)) (str.len c))))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ a b)) (str.len c)) (str.substr (str.++ a b) (str.len c) (- (str.len (str.++ a b)) (str.len c))) (str.substr c (str.len (str.++ a b)) (- (str.len c) (str.len (str.++ a b))))))
                   (step t1 (cl (and (or (= (str.++ a b) (str.++ c r_skolem)) (= c (str.++ a b r_skolem))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_prefix :premises (h1 h2))"#: true,
            }
            "Terms are not str.++ applications" {
                r#"(assume h1 (= "" (str.++ "a" c)))
                   (assume h2 (not (= (str.len "a") (str.len (str.++ "a" c)))))
                   (define-fun r_skolem () String (ite (>= (str.len "a") (str.len (str.++ "a" c))) (str.substr "a" (str.len (str.++ "a" c)) (- (str.len "a") (str.len (str.++ "a" c)))) (str.substr (str.++ "a" c) (str.len "a") (- (str.len (str.++ "a" c)) (str.len "a")))))
                   (step t1 (cl (and (or (= "a" (str.++ "a" c r_skolem)) (= (str.++ "a" c) (str.++ "a" r_skolem))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_prefix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ "a" "b" b) ""))
                   (assume h2 (not (= (str.len "a") (str.len (str.++ "a" c)))))
                   (define-fun r_skolem () String (ite (>= (str.len "a") (str.len (str.++ "a" c))) (str.substr "a" (str.len (str.++ "a" c)) (- (str.len "a") (str.len (str.++ "a" c)))) (str.substr (str.++ "a" c) (str.len "a") (- (str.len (str.++ "a" c)) (str.len "a")))))
                   (step t1 (cl (and (or (= "a" (str.++ "a" c r_skolem)) (= (str.++ "a" c) (str.++ "a" r_skolem))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_prefix :premises (h1 h2))"#: false,
            }
            "Premise term is not an equality" {
                r#"(assume h1 (not (= (str.++ a b c) (str.++ c d e))))
                   (assume h2 (not (= (str.len (str.++ a b)) (str.len c))))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ a b)) (str.len c)) (str.substr (str.++ a b) (str.len c) (- (str.len (str.++ a b)) (str.len c))) (str.substr c (str.len (str.++ a b)) (- (str.len c) (str.len (str.++ a b))))))
                   (step t1 (cl (and (or (= (str.++ a b) (str.++ c r_skolem)) (= c (str.++ a b r_skolem))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_prefix :premises (h1 h2))"#: false,
            }
            "Premise term is not an inequality of the form (not (= (str.len t_1) (str.len s_1)))" {
                r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
                   (assume h2 (= (str.len "a") (str.len (str.++ "a" c))))
                   (define-fun r_skolem () String (ite (>= (str.len "a") (str.len (str.++ "a" c))) (str.substr "a" (str.len (str.++ "a" c)) (- (str.len "a") (str.len (str.++ "a" c)))) (str.substr (str.++ "a" c) (str.len "a") (- (str.len (str.++ "a" c)) (str.len "a")))))
                   (step t1 (cl (and (or (= "a" (str.++ "a" c r_skolem)) (= (str.++ "a" c) (str.++ "a" r_skolem))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_prefix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
                   (assume h2 (not (= (str.to_code "a") (str.to_code (str.++ "a" c)))))
                   (define-fun r_skolem () String (ite (>= (str.len "a") (str.len (str.++ "a" c))) (str.substr "a" (str.len (str.++ "a" c)) (- (str.len "a") (str.len (str.++ "a" c)))) (str.substr (str.++ "a" c) (str.len "a") (- (str.len (str.++ "a" c)) (str.len "a")))))
                   (step t1 (cl (and (or (= "a" (str.++ "a" c r_skolem)) (= (str.++ "a" c) (str.++ "a" r_skolem))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_prefix :premises (h1 h2))"#: false,
            }
            r#"Conclusion term is not of the form (and (or (= x y) (= z w)) (not (= r "")) (> (str.len r) 0))"# {
                r#"(assume h1 (= (str.++ a b c) (str.++ c d e)))
                   (assume h2 (not (= (str.len (str.++ a b)) (str.len c))))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ a b)) (str.len c)) (str.substr (str.++ a b) (str.len c) (- (str.len (str.++ a b)) (str.len c))) (str.substr c (str.len (str.++ a b)) (- (str.len c) (str.len (str.++ a b))))))
                   (step t1 (cl (or (or (= (str.++ a b) (str.++ c r_skolem)) (= c (str.++ a b r_skolem))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_prefix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ a b c) (str.++ c d e)))
                   (assume h2 (not (= (str.len (str.++ a b)) (str.len c))))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ a b)) (str.len c)) (str.substr (str.++ a b) (str.len c) (- (str.len (str.++ a b)) (str.len c))) (str.substr c (str.len (str.++ a b)) (- (str.len c) (str.len (str.++ a b))))))
                   (step t1 (cl (and (and (= (str.++ a b) (str.++ c r_skolem)) (= c (str.++ a b r_skolem))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_prefix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ a b c) (str.++ c d e)))
                   (assume h2 (not (= (str.len (str.++ a b)) (str.len c))))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ a b)) (str.len c)) (str.substr (str.++ a b) (str.len c) (- (str.len (str.++ a b)) (str.len c))) (str.substr c (str.len (str.++ a b)) (- (str.len c) (str.len (str.++ a b))))))
                   (step t1 (cl (and (or (not (= (str.++ a b) (str.++ c r_skolem))) (not (= c (str.++ a b r_skolem)))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_prefix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ a b c) (str.++ c d e)))
                   (assume h2 (not (= (str.len (str.++ a b)) (str.len c))))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ a b)) (str.len c)) (str.substr (str.++ a b) (str.len c) (- (str.len (str.++ a b)) (str.len c))) (str.substr c (str.len (str.++ a b)) (- (str.len c) (str.len (str.++ a b))))))
                   (step t1 (cl (and (or (= (str.++ a b) (str.++ c r_skolem)) (= c (str.++ a b r_skolem))) (= r_skolem "") (> (str.len r_skolem) 0))) :rule concat_split_prefix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ a b c) (str.++ c d e)))
                   (assume h2 (not (= (str.len (str.++ a b)) (str.len c))))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ a b)) (str.len c)) (str.substr (str.++ a b) (str.len c) (- (str.len (str.++ a b)) (str.len c))) (str.substr c (str.len (str.++ a b)) (- (str.len c) (str.len (str.++ a b))))))
                   (step t1 (cl (and (or (= (str.++ a b) (str.++ c r_skolem)) (= c (str.++ a b r_skolem))) (not (= r_skolem "")) (> (str.len r_skolem) 1))) :rule concat_split_prefix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ a b c) (str.++ c d e)))
                   (assume h2 (not (= (str.len (str.++ a b)) (str.len c))))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ a b)) (str.len c)) (str.substr (str.++ a b) (str.len c) (- (str.len (str.++ a b)) (str.len c))) (str.substr c (str.len (str.++ a b)) (- (str.len c) (str.len (str.++ a b))))))
                   (step t1 (cl (and (or (= (str.++ a b) (str.++ c r_skolem)) (= c (str.++ a b r_skolem))) (not (= r_skolem "")) (< (str.len r_skolem) 0))) :rule concat_split_prefix :premises (h1 h2))"#: false,
            }
        }
    }

    #[test]
    fn concat_split_suffix() {
        test_cases! {
            definitions = "
                (declare-fun a () String)
                (declare-fun b () String)
                (declare-fun c () String)
                (declare-fun d () String)
                (declare-fun e () String)
            ",
            "Simple working examples" {
                r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
                   (assume h2 (not (= (str.len (str.++ "b" b)) (str.len c))))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ "b" b)) (str.len c)) (str.substr (str.++ "b" b) 0 (- (str.len (str.++ "b" b)) (str.len c))) (str.substr c 0 (- (str.len c) (str.len (str.++ "b" b))))))
                   (step t1 (cl (and (or (= (str.++ "b" b) (str.++ r_skolem c)) (= c (str.++ r_skolem (str.++ "b" b)))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_suffix :premises (h1 h2))"#: true,
                r#"(assume h1 (= (str.++ a b c d) (str.++ b c d e)))
                   (assume h2 (not (= (str.len (str.++ c d)) (str.len (str.++ c d e)))))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ c d)) (str.len (str.++ c d e))) (str.substr (str.++ c d) 0 (- (str.len (str.++ c d)) (str.len (str.++ c d e)))) (str.substr (str.++ c d e) 0 (- (str.len (str.++ c d e)) (str.len (str.++ c d))))))
                   (step t1 (cl (and (or (= (str.++ c d) (str.++ r_skolem (str.++ c d e))) (= (str.++ c d e) (str.++ r_skolem (str.++ c d)))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_suffix :premises (h1 h2))"#: true,
            }
            "Terms are not str.++ applications" {
                r#"(assume h1 (= "" (str.++ "a" c)))
                   (assume h2 (not (= (str.len (str.++ "b" b)) (str.len c))))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ "b" b)) (str.len c)) (str.substr (str.++ "b" b) 0 (- (str.len (str.++ "b" b)) (str.len c))) (str.substr c 0 (- (str.len c) (str.len (str.++ "b" b))))))
                   (step t1 (cl (and (or (= (str.++ "b" b) (str.++ r_skolem c)) (= c (str.++ r_skolem (str.++ "b" b)))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_suffix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ "a" "b" b) ""))
                   (assume h2 (not (= (str.len (str.++ "b" b)) (str.len c))))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ "b" b)) (str.len c)) (str.substr (str.++ "b" b) 0 (- (str.len (str.++ "b" b)) (str.len c))) (str.substr c 0 (- (str.len c) (str.len (str.++ "b" b))))))
                   (step t1 (cl (and (or (= (str.++ "b" b) (str.++ r_skolem c)) (= c (str.++ r_skolem (str.++ "b" b)))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_suffix :premises (h1 h2))"#: false,
            }
            "Premise term is not an equality" {
                r#"(assume h1 (not (= (str.++ a b c d) (str.++ b c d e))))
                   (assume h2 (not (= (str.len (str.++ c d)) (str.len (str.++ c d e)))))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ c d)) (str.len (str.++ c d e))) (str.substr (str.++ c d) 0 (- (str.len (str.++ c d)) (str.len (str.++ c d e)))) (str.substr (str.++ c d e) 0 (- (str.len (str.++ c d e)) (str.len (str.++ c d))))))
                   (step t1 (cl (and (or (= (str.++ c d) (str.++ r_skolem (str.++ c d e))) (= (str.++ c d e) (str.++ r_skolem (str.++ c d)))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_suffix :premises (h1 h2))"#: false,
            }
            "Premise term is not an inequality of the form (not (= (str.len t_2) (str.len s_2)))" {
                r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
                   (assume h2 (= (str.len (str.++ "b" b)) (str.len c)))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ "b" b)) (str.len c)) (str.substr (str.++ "b" b) 0 (- (str.len (str.++ "b" b)) (str.len c))) (str.substr c 0 (- (str.len c) (str.len (str.++ "b" b))))))
                   (step t1 (cl (and (or (= (str.++ "b" b) (str.++ r_skolem c)) (= c (str.++ r_skolem (str.++ "b" b)))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_suffix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
                   (assume h2 (not (= (str.to_code (str.++ "b" b)) (str.to_code c))))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ "b" b)) (str.len c)) (str.substr (str.++ "b" b) 0 (- (str.len (str.++ "b" b)) (str.len c))) (str.substr c 0 (- (str.len c) (str.len (str.++ "b" b))))))
                   (step t1 (cl (and (or (= (str.++ "b" b) (str.++ r_skolem c)) (= c (str.++ r_skolem (str.++ "b" b)))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_suffix :premises (h1 h2))"#: false,
            }
            r#"Conclusion term is not of the form (and (or (= x y) (= z w)) (not (= r "")) (> (str.len r) 0))"# {
                r#"(assume h1 (= (str.++ a b c d) (str.++ b c d e)))
                   (assume h2 (not (= (str.len (str.++ c d)) (str.len (str.++ c d e)))))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ c d)) (str.len (str.++ c d e))) (str.substr (str.++ c d) 0 (- (str.len (str.++ c d)) (str.len (str.++ c d e)))) (str.substr (str.++ c d e) 0 (- (str.len (str.++ c d e)) (str.len (str.++ c d))))))
                   (step t1 (cl (or (or (= (str.++ c d) (str.++ r_skolem (str.++ c d e))) (= (str.++ c d e) (str.++ r_skolem (str.++ c d)))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_suffix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ a b c d) (str.++ b c d e)))
                   (assume h2 (not (= (str.len (str.++ c d)) (str.len (str.++ c d e)))))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ c d)) (str.len (str.++ c d e))) (str.substr (str.++ c d) 0 (- (str.len (str.++ c d)) (str.len (str.++ c d e)))) (str.substr (str.++ c d e) 0 (- (str.len (str.++ c d e)) (str.len (str.++ c d))))))
                   (step t1 (cl (and (and (= (str.++ c d) (str.++ r_skolem (str.++ c d e))) (= (str.++ c d e) (str.++ r_skolem (str.++ c d)))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_suffix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ a b c d) (str.++ b c d e)))
                   (assume h2 (not (= (str.len (str.++ c d)) (str.len (str.++ c d e)))))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ c d)) (str.len (str.++ c d e))) (str.substr (str.++ c d) 0 (- (str.len (str.++ c d)) (str.len (str.++ c d e)))) (str.substr (str.++ c d e) 0 (- (str.len (str.++ c d e)) (str.len (str.++ c d))))))
                   (step t1 (cl (and (or (= (str.++ c d) (str.++ r_skolem (str.++ c d e))) (not (= (str.++ c d e) (str.++ r_skolem (str.++ c d))))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_suffix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ a b c d) (str.++ b c d e)))
                   (assume h2 (not (= (str.len (str.++ c d)) (str.len (str.++ c d e)))))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ c d)) (str.len (str.++ c d e))) (str.substr (str.++ c d) 0 (- (str.len (str.++ c d)) (str.len (str.++ c d e)))) (str.substr (str.++ c d e) 0 (- (str.len (str.++ c d e)) (str.len (str.++ c d))))))
                   (step t1 (cl (and (or (= (str.++ c d) (str.++ r_skolem (str.++ c d e))) (= (str.++ c d e) (str.++ r_skolem (str.++ c d)))) (= r_skolem "") (> (str.len r_skolem) 0))) :rule concat_split_suffix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ a b c d) (str.++ b c d e)))
                   (assume h2 (not (= (str.len (str.++ c d)) (str.len (str.++ c d e)))))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ c d)) (str.len (str.++ c d e))) (str.substr (str.++ c d) 0 (- (str.len (str.++ c d)) (str.len (str.++ c d e)))) (str.substr (str.++ c d e) 0 (- (str.len (str.++ c d e)) (str.len (str.++ c d))))))
                   (step t1 (cl (and (or (= (str.++ c d) (str.++ r_skolem (str.++ c d e))) (= (str.++ c d e) (str.++ r_skolem (str.++ c d)))) (not (= r_skolem "")) (> (str.len r_skolem) 1))) :rule concat_split_suffix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ a b c d) (str.++ b c d e)))
                   (assume h2 (not (= (str.len (str.++ c d)) (str.len (str.++ c d e)))))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ c d)) (str.len (str.++ c d e))) (str.substr (str.++ c d) 0 (- (str.len (str.++ c d)) (str.len (str.++ c d e)))) (str.substr (str.++ c d e) 0 (- (str.len (str.++ c d e)) (str.len (str.++ c d))))))
                   (step t1 (cl (and (or (= (str.++ c d) (str.++ r_skolem (str.++ c d e))) (= (str.++ c d e) (str.++ r_skolem (str.++ c d)))) (not (= r_skolem "")) (< (str.len r_skolem) 0))) :rule concat_split_suffix :premises (h1 h2))"#: false,
            }
        }
    }
}
