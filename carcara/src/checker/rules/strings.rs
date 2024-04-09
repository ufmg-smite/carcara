use super::{
    assert_clause_len, assert_eq, assert_num_args, assert_num_premises, assert_polyeq_expected,
    get_premise_term, RuleArgs, RuleResult,
};
use crate::{ast::*, checker::error::CheckerError};
use rug::Integer;
use std::{cmp, time::Duration};

fn flatten(term: Rc<Term>, pool: &mut dyn TermPool) -> Vec<Rc<Term>> {
    let mut flattened = Vec::new();
    if let Term::Const(Constant::String(s)) = term.as_ref() {
        flattened.extend(
            s.chars()
                .map(|c| pool.add(Term::Const(Constant::String(c.to_string())))),
        );
    } else if let Some(args) = match_term!((strconcat ...) = term) {
        for arg in args {
            flattened.extend(flatten(arg.clone(), pool));
        }
    } else {
        flattened.push(term.clone());
    }
    flattened
}

fn reconstruct_term(terms: Vec<Rc<Term>>, pool: &mut dyn TermPool) -> Rc<Term> {
    match terms.len() {
        0 => pool.add(Term::Const(Constant::String("".to_owned()))),
        1 => terms[0].clone(),
        _ => pool.add(Term::Op(Operator::StrConcat, terms)),
    }
}

fn build_skolem_prefix(u: Rc<Term>, pool: &mut dyn TermPool) -> Rc<Term> {
    build_term!(pool, (strsubstr {u.clone()} 0 (- (strlen {u.clone()}) 1)))
}

fn build_skolem_suffix(u: Rc<Term>, n: usize, pool: &mut dyn TermPool) -> Rc<Term> {
    let n = pool.add(Term::new_int(n));
    build_term!(pool, (strsubstr {u.clone()} {n.clone()} (- (strlen {u.clone()}) {n})))
}

fn is_prefix(
    term: Rc<Term>,
    pref: Rc<Term>,
    pool: &mut dyn TermPool,
    rev: bool,
    polyeq_time: &mut Duration,
) -> Result<Vec<Rc<Term>>, CheckerError> {
    let mut t_flat = flatten(term.clone(), pool);
    let mut p_flat = flatten(pref.clone(), pool);

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

    Ok(p_flat)
}

type Suffixes = (Vec<Rc<Term>>, Vec<Rc<Term>>);

fn strip_prefix(
    s: Rc<Term>,
    t: Rc<Term>,
    pool: &mut dyn TermPool,
    rev: bool,
    polyeq_time: &mut Duration,
) -> Result<Suffixes, CheckerError> {
    let mut s_flat = flatten(s.clone(), pool);
    let mut t_flat = flatten(t.clone(), pool);

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

    let s_suffix = s_flat.get(prefix..).unwrap_or_default().to_vec();
    let t_suffix = t_flat.get(prefix..).unwrap_or_default().to_vec();

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
    let (l, r) = match_term_err!((= l r) = term)?;

    let (mut l_suffix, mut r_suffix) = strip_prefix(l.clone(), r.clone(), pool, rev, polyeq_time)?;

    if rev {
        l_suffix.reverse();
        r_suffix.reverse();
    }

    let l_concat = reconstruct_term(l_suffix, pool);
    let r_concat = reconstruct_term(r_suffix, pool);
    let expected = pool.add(Term::Op(Operator::Equals, vec![l_concat, r_concat]));

    let (l_conc, r_conc) = match_term_err!((= l r) = &conclusion[0])?;
    let l_conc_flat = flatten(l_conc.clone(), pool);
    let r_conc_flat = flatten(r_conc.clone(), pool);
    let l_conc_concat = reconstruct_term(l_conc_flat.clone(), pool);
    let r_conc_concat = reconstruct_term(r_conc_flat.clone(), pool);
    let expanded_conc = pool.add(Term::Op(
        Operator::Equals,
        vec![l_conc_concat, r_conc_concat],
    ));

    assert_eq(&expected, &expanded_conc)
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
    let (l, r) = match_term_err!((= l r) = term)?;

    let (l_pref, r_pref) = match_term_err!((= (strlen l) (strlen r)) = prefixes)?;
    let mut l_pref_flat = is_prefix(l.clone(), l_pref.clone(), pool, rev, polyeq_time)?;
    let mut r_pref_flat = is_prefix(r.clone(), r_pref.clone(), pool, rev, polyeq_time)?;

    if rev {
        l_pref_flat.reverse();
        r_pref_flat.reverse();
    }

    let l_concat = reconstruct_term(l_pref_flat, pool);
    let r_concat = reconstruct_term(r_pref_flat, pool);
    let expected = pool.add(Term::Op(Operator::Equals, vec![l_concat, r_concat]));

    let (l_conc, r_conc) = match_term_err!((= l r) = &conclusion[0])?;
    let l_conc_concat = reconstruct_term(flatten(l_conc.clone(), pool), pool);
    let r_conc_concat = reconstruct_term(flatten(r_conc.clone(), pool), pool);
    let expanded = pool.add(Term::Op(
        Operator::Equals,
        vec![l_conc_concat, r_conc_concat],
    ));

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

    let (l, r) = match_term_err!((= l r) = term)?;

    let (l_suffix, r_suffix) = strip_prefix(l.clone(), r.clone(), pool, rev, polyeq_time)?;

    if let Some(l_head) = l_suffix.first() {
        string_check_length_one(l_head.clone())?;
        if let Some(r_head) = r_suffix.first() {
            string_check_length_one(r_head.clone())?;
        }
    } else if let Some(r_head) = r_suffix.first() {
        string_check_length_one(r_head.clone())?;
    } else {
        return Err(CheckerError::ExpectedDifferentConstantPrefixes(
            l.clone(),
            r.clone(),
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

    let mut t_flat = flatten(t.clone(), pool);
    let mut s_flat = flatten(s.clone(), pool);

    if t_flat.is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", t.clone()));
    }
    if s_flat.is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", s.clone()));
    }

    if rev {
        t_flat.reverse();
        s_flat.reverse();
    }

    let mut lhs = is_prefix(t.clone(), u.clone(), pool, rev, polyeq_time)?;
    if rev {
        lhs.reverse();
    }

    let mut rhs: Vec<Rc<Term>> = vec![];
    if let Some(s_head) = s_flat.first() {
        string_check_length_one(s_head.clone())?;
        if rev {
            rhs.push(build_skolem_suffix(u.clone(), 1, pool).clone());
            rhs.push(s_head.clone());
        } else {
            rhs.push(s_head.clone());
            rhs.push(build_skolem_prefix(u.clone(), pool).clone());
        }
    }

    let lhs_reconstructed = reconstruct_term(lhs, pool);
    let rhs_reconstructed = reconstruct_term(rhs, pool);
    let expected = pool.add(Term::Op(
        Operator::Equals,
        vec![lhs_reconstructed, rhs_reconstructed],
    ));

    let (l_conc, r_conc) = match_term_err!((= l r) = &conclusion[0])?;
    let l_conc_reconstructed = reconstruct_term(flatten(l_conc.clone(), pool), pool);
    let r_conc_reconstructed = reconstruct_term(flatten(r_conc.clone(), pool), pool);
    let expanded = pool.add(Term::Op(
        Operator::Equals,
        vec![l_conc_reconstructed, r_conc_reconstructed],
    ));

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
                   (step t1 (cl (= "a" (str.++ "a" (str.substr "a" 0 (- (str.len "a") 1))))) :rule concat_csplit :premises (h1 h2) :args (false))"#: true,
                r#"(assume h1 (= (str.++ a "b" c) (str.++ "ab" c)))
                   (assume h2 (not (= (str.len (str.++ a "b")) 0)))
                   (step t1 (cl (= (str.++ a "b") (str.++ "a" (str.substr (str.++ a "b") 0 (- (str.len (str.++ a "b")) 1))))) :rule concat_csplit :premises (h1 h2) :args (false))"#: true,
                r#"(assume h1 (= (str.++ d (str.++ c (str.++ b "a"))) (str.++ "b" (str.++ "c" d))))
                   (assume h2 (not (= (str.len (str.++ d c)) 0)))
                   (step t1 (cl (= (str.++ d c) (str.++ "b" (str.substr (str.++ d c) 0 (- (str.len (str.++ d c)) 1))))) :rule concat_csplit :premises (h1 h2) :args (false))"#: true,
            }
            "Reverse argument set to true" {
                r#"(assume h1 (= (str.++ "c" "b" a) (str.++ "a" (str.++ c "b"))))
                   (assume h2 (not (= (str.len (str.++ "b" a)) 0)))
                   (step t1 (cl (= (str.++ "b" a) (str.++ (str.substr (str.++ "b" a) 1 (- (str.len (str.++ "b" a)) 1)) "b"))) :rule concat_csplit :premises (h1 h2) :args (true))"#: true,
                r#"(assume h1 (= (str.++ d (str.++ c (str.++ "b" a))) (str.++ "b" (str.++ "c" "de"))))
                   (assume h2 (not (= (str.len (str.++ c (str.++ "b" a))) 0)))
                   (step t1 (cl (= (str.++ c (str.++ "b" a)) (str.++ (str.substr (str.++ c (str.++ "b" a)) 1 (- (str.len (str.++ c (str.++ "b" a))) 1)) "e"))) :rule concat_csplit :premises (h1 h2) :args (true))"#: true,
            }
            "Term does not have a constant prefix" {
                r#"(assume h1 (= (str.++ d (str.++ c (str.++ b "a"))) (str.++ b (str.++ "c" d))))
                   (assume h2 (not (= (str.len (str.++ d c)) 0)))
                   (step t1 (cl (= (str.++ d c) (str.++ b (str.substr (str.++ d c) 0 (- (str.len (str.++ d c)) 1))))) :rule concat_csplit :premises (h1 h2) :args (false))"#: false,
            }
            "Term are not a str.++ application" {
                r#"(assume h1 (= (str.++ "a" "b" b) ""))
                   (assume h2 (not (= (str.len "a") 0)))
                   (step t1 (cl (= "a" (str.++ "a" (str.substr "a" 0 (- (str.len "a") 1))))) :rule concat_csplit :premises (h1 h2) :args (false))"#: false,
                r#"(assume h1 (= "" (str.++ "a" c)))
                   (assume h2 (not (= (str.len "a") 0)))
                   (step t1 (cl (= "a" (str.++ "a" (str.substr "a" 0 (- (str.len "a") 1))))) :rule concat_csplit :premises (h1 h2) :args (false))"#: false,
            }
            "Invalid argument type" {
                r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
                   (assume h2 (not (= (str.len "a") 0)))
                   (step t1 (cl (= "a" (str.++ "a" (str.substr "a" 0 (- (str.len "a") 1))))) :rule concat_csplit :premises (h1 h2) :args (1))"#: false,
                r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
                   (assume h2 (not (= (str.len "a") 0)))
                   (step t1 (cl (= "a" (str.++ "a" (str.substr "a" 0 (- (str.len "a") 1))))) :rule concat_csplit :premises (h1 h2) :args (1.5))"#: false,
                r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
                   (assume h2 (not (= (str.len "a") 0)))
                   (step t1 (cl (= "a" (str.++ "a" (str.substr "a" 0 (- (str.len "a") 1))))) :rule concat_csplit :premises (h1 h2) :args ((- 1)))"#: false,
                r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
                   (assume h2 (not (= (str.len "a") 0)))
                   (step t1 (cl (= "a" (str.++ "a" (str.substr "a" 0 (- (str.len "a") 1))))) :rule concat_csplit :premises (h1 h2) :args ("test"))"#: false,
            }
            "Premise term is not an equality" {
                r#"(assume h1 (not (= (str.++ d (str.++ c (str.++ b "a"))) (str.++ "b" (str.++ "c" d)))))
                   (assume h2 (not (= (str.len (str.++ d c)) 0)))
                   (step t1 (cl (= (str.++ d c) (str.++ "b" (str.substr (str.++ d c) 0 (- (str.len (str.++ d c)) 1))))) :rule concat_csplit :premises (h1 h2) :args (false))"#: false,
            }
            "Premise term is not an inequality of the form (not (= (str.len str) 0))" {
                r#"(assume h1 (= (str.++ d (str.++ c (str.++ b "a"))) (str.++ "b" (str.++ "c" d))))
                   (assume h2 (= (str.len (str.++ d c)) 0))
                   (step t1 (cl (= (str.++ d c) (str.++ "b" (str.substr (str.++ d c) 0 (- (str.len (str.++ d c)) 1))))) :rule concat_csplit :premises (h1 h2) :args (false))"#: false,
                r#"(assume h1 (= (str.++ d (str.++ c (str.++ b "a"))) (str.++ "b" (str.++ "c" d))))
                   (assume h2 (not (= (str.len (str.++ d c)) 1)))
                   (step t1 (cl (= (str.++ d c) (str.++ "b" (str.substr (str.++ d c) 0 (- (str.len (str.++ d c)) 1))))) :rule concat_csplit :premises (h1 h2) :args (false))"#: false,
            }
            "Conclusion term is not an equality" {
                r#"(assume h1 (= (str.++ d (str.++ c (str.++ b "a"))) (str.++ "b" (str.++ "c" d))))
                   (assume h2 (not (= (str.len (str.++ d c)) 0)))
                   (step t1 (cl (not (= (str.++ d c) (str.++ "b" (str.substr (str.++ d c) 0 (- (str.len (str.++ d c)) 1)))))) :rule concat_csplit :premises (h1 h2) :args (false))"#: false,
            }
            "Switched conclusion terms" {
                r#"(assume h1 (= (str.++ d (str.++ c (str.++ b "a"))) (str.++ "b" (str.++ "c" d))))
                   (assume h2 (not (= (str.len (str.++ d c)) 0)))
                   (step t1 (cl (= (str.++ "b" (str.substr (str.++ d c) 0 (- (str.len (str.++ d c)) 1))) (str.++ d c))) :rule concat_csplit :premises (h1 h2) :args (false))"#: false,
                r#"(assume h1 (= (str.++ d (str.++ c (str.++ "b" a))) (str.++ "b" (str.++ "c" "de"))))
                   (assume h2 (not (= (str.len (str.++ c (str.++ "b" a))) 0)))
                   (step t1 (cl (= (str.++ (str.substr (str.++ c (str.++ "b" a)) 1 (- (str.len (str.++ c (str.++ "b" a))) 1)) "e") (str.++ c (str.++ "b" a)))) :rule concat_csplit :premises (h1 h2) :args (true))"#: false,
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
}
