use std::{cmp, time::Duration};

use super::{
    assert_clause_len, assert_eq, assert_num_args, assert_num_premises, assert_polyeq_expected,
    get_premise_term, RuleArgs, RuleResult,
};
use crate::{ast::*, checker::error::CheckerError};

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

fn concat_terms(terms: Vec<Rc<Term>>, pool: &mut dyn TermPool) -> Rc<Term> {
    match terms.len() {
        0 => pool.add(Term::Const(Constant::String(String::from("")))),
        1 => terms[0].clone(),
        _ => pool.add(Term::Op(Operator::StrConcat, terms)),
    }
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
    let (left, right) = match_term_err!((= l r) = term)?;
    let mut left_flattened = flatten(left.clone(), pool);
    let mut right_flattened = flatten(right.clone(), pool);

    if rev {
        left_flattened.reverse();
        right_flattened.reverse();
    }

    let mut prefix = 0;
    while (prefix < cmp::min(left_flattened.len(), right_flattened.len()))
        && polyeq(
            &left_flattened[prefix],
            &right_flattened[prefix],
            polyeq_time,
        )
    {
        prefix += 1;
    }

    let mut left_suffix = left_flattened.get(prefix..).unwrap_or_default().to_vec();
    let mut right_suffix = right_flattened.get(prefix..).unwrap_or_default().to_vec();

    if rev {
        left_suffix.reverse();
        right_suffix.reverse();
    }

    let left_concat = concat_terms(left_suffix, pool);
    let right_concat = concat_terms(right_suffix, pool);
    let expected = pool.add(Term::Op(Operator::Equals, vec![left_concat, right_concat]));

    let (conc_left, conc_right) = match_term_err!((= l r) = &conclusion[0])?;
    let conc_left_flattened = flatten(conc_left.clone(), pool);
    let conc_right_flattened = flatten(conc_right.clone(), pool);
    let conc_left_concat = concat_terms(conc_left_flattened.clone(), pool);
    let conc_right_concat = concat_terms(conc_right_flattened.clone(), pool);
    let expanded_conc = pool.add(Term::Op(
        Operator::Equals,
        vec![conc_left_concat, conc_right_concat],
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

    let left_concat = concat_terms(l_pref_flat, pool);
    let right_concat = concat_terms(r_pref_flat, pool);
    let expected = pool.add(Term::Op(Operator::Equals, vec![left_concat, right_concat]));

    let (l_conc, r_conc) = match_term_err!((= l r) = &conclusion[0])?;
    let l_conc_concat = concat_terms(flatten(l_conc.clone(), pool), pool);
    let r_conc_concat = concat_terms(flatten(r_conc.clone(), pool), pool);
    let expanded = pool.add(Term::Op(
        Operator::Equals,
        vec![l_conc_concat, r_conc_concat],
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
                r#"(assume h1 (= (str.++ "0" (str.from_int (str.len c))) "0"))
                   (step t1 (cl (= (str.from_int (str.len c)) "")) :rule concat_eq :premises (h1) :args (false))"#: true,
                r#"(assume h1 (= "0" (str.++ "0" (str.from_int (str.len b)))))
                   (step t1 (cl (= "" (str.from_int (str.len b)))) :rule concat_eq :premises (h1) :args (false))"#: true,
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
}
