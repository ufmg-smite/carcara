#![cfg(test)]

use super::*;

fn run_tests(test_name: &str, definitions: &str, cases: &[(&str, bool)]) {
    use crate::parser::parse_problem_proof;
    use std::io::Cursor;

    for (i, (proof, expected)) in cases.iter().enumerate() {
        // This parses the definitions again for every case, which is not ideal
        let parsed = parse_problem_proof(Cursor::new(definitions), Cursor::new(proof))
            .unwrap_or_else(|_| panic!("parser error during test \"{}\"", test_name));
        let got = ProofChecker::new(parsed, false).check().is_ok();
        assert_eq!(
            *expected, got,
            "test case \"{}\" index {} failed",
            test_name, i
        );
    }
}

macro_rules! test_cases {
    (
        definitions = $defs:expr,
        $($name:literal { $($proof:literal: $exp:literal,)* } )*
    ) => {{
        let definitions: &str = $defs;
        $(
            let name: &str = $name;
            let cases = [ $(($proof, $exp),)* ];
            run_tests(name, definitions, &cases);
        )*
    }};
}

#[test]
fn test_not_not_rule() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
        ",
        "Simple working examples" {
            "(step t1 (cl (not (not (not p))) p) :rule not_not)": true,
            "(step t1 (cl (not (not (not (not q)))) (not q)) :rule not_not)": true,
        }
        "Number of terms in clause != 2" {
            "(step t1 (cl (not (not (not p)))) :rule not_not)": false,
            "(step t1 (cl (not (not (not p))) p q) :rule not_not)": false,
        }
        "First term in clause is not of the correct form" {
            "(step t1 (cl (not (not p)) (not p)) :rule not_not)": false,
            "(step t1 (cl p (not p)) :rule not_not)": false,
        }
        "Terms don't match" {
            "(step t1 (cl (not (not (not p))) (not p)) :rule not_not)": false,
            "(step t1 (cl (not (not (not p))) q) :rule not_not)": false,
        }
    }
}

#[test]
fn test_and_pos_rule() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun r () Bool)
            (declare-fun s () Bool)
        ",
        "Simple working examples" {
            "(step t1 (cl (not (and p q r)) r) :rule and_pos)": true,
            "(step t1 (cl (not (and (or (not r) p) q)) (or (not r) p)) :rule and_pos)": true,
        }
        "First term in clause is not of the correct form" {
            "(step t1 (cl (and p q r) r) :rule and_pos)": false,
            "(step t1 (cl (not (or p q r)) r) :rule and_pos)": false,
        }
        "Second term is not in \"and\" term" {
            "(step t1 (cl (not (and p q r)) s) :rule and_pos)": false,
            "(step t1 (cl (not (and p (not q) r)) q) :rule and_pos)": false,
        }
    }
}

#[test]
fn test_and_neg_rule() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun r () Bool)
            (declare-fun s () Bool)
        ",
        "Simple working examples" {
            "(step t1 (cl (and p q) (not p) (not q)) :rule and_neg)": true,
            "(step t1 (cl (and p q r s) (not p) (not q) (not r) (not s)) :rule and_neg)": true,
        }
        "First term in clause is not of the correct form" {
            "(step t1 (cl (or p q r) (not p) (not q) (not r)) :rule and_neg)": false,
        }
        "Remaining terms in clause are not of the correct form" {
            "(step t1 (cl (and p q) p (not q)) :rule and_neg)": false,
        }
        "Number of remaining terms is incorrect" {
            "(step t1 (cl (and p q r) (not p) (not q) (not r) (not s)) :rule and_neg)": false,
            "(step t1 (cl (and p q r) (not p) (not q)) :rule and_neg)": false,
        }
        "Terms don't match" {
            "(step t1 (cl (and p q r) (not p) (not q) (not s)) :rule and_neg)": false,
            "(step t1 (cl (and p q r s) (not p) (not r) (not q) (not s)) :rule and_neg)": false,
        }
    }
}

#[test]
fn test_or_pos_rule() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun r () Bool)
            (declare-fun s () Bool)
        ",
        "Simple working examples" {
            "(step t1 (cl (not (or p q)) p q) :rule or_pos)": true,
            "(step t1 (cl (not (or p q r s)) p q r s) :rule or_pos)": true,
        }
        "First term in clause is not of the correct form" {
            "(step t1 (cl (or p q r) p q r) :rule or_pos)": false,
            "(step t1 (cl (not (and p q r)) p q r) :rule or_pos)": false,
        }
        "Number of remaining terms is incorrect" {
            "(step t1 (cl (not (or p q r)) p q) :rule or_pos)": false,
            "(step t1 (cl (not (or p q r)) p q r s) :rule or_pos)": false,
        }
        "Terms don't match" {
            "(step t1 (cl (not (or p q r)) p q s) :rule or_pos)": false,
            "(step t1 (cl (not (or p q r s)) p r q s) :rule or_pos)": false,
        }
    }
}

#[test]
fn test_or_neg_rule() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun r () Bool)
            (declare-fun s () Bool)
        ",
        "Simple working examples" {
            "(step t1 (cl (or p q r) (not r)) :rule or_neg)": true,
        }
        "First term in clause is not of the correct form" {
            "(step t1 (cl (and p q r) (not r)) :rule or_neg)": false,
            "(step t1 (cl (not (or p q r)) (not r)) :rule or_neg)": false,
        }
        "Second term is not in \"or\" term" {
            "(step t1 (cl (or p q r) (not s)) :rule or_neg)": false,
            "(step t1 (cl (or p (not q) r) (not q)) :rule or_neg)": false,

        }
    }
}

#[test]
fn test_equiv_pos1_rule() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
        ",
        "Simple working examples" {
            "(step t1 (cl (not (= p q)) p (not q)) :rule equiv_pos1)": true,
            "(step t1 (cl (not (= p (not q))) p (not (not q))) :rule equiv_pos1)": true,
            "(step t1 (cl (not (= (not p) q)) (not p) (not q)) :rule equiv_pos1)": true,
        }
        "Number of terms in clause != 3" {
            "(step t1 (cl (not (= p q)) p) :rule equiv_pos1)": false,
            "(step t1 (cl (not (= p q)) p (not q) q) :rule equiv_pos1)": false,
        }
        "Term in clause is not of the correct form" {
            "(step t1 (cl (= p q) p (not q)) :rule equiv_pos1)": false,
            "(step t1 (cl (and p q) p (not q)) :rule equiv_pos1)": false,
            "(step t1 (cl (not (= p q)) p q) :rule equiv_pos1)": false,
        }
        "Terms don't match" {
            "(step t1 (cl (not (= p q)) q (not q)) :rule equiv_pos1)": false,
            "(step t1 (cl (not (= p q)) p (not p)) :rule equiv_pos1)": false,
            "(step t1 (cl (not (= (not p) q)) p (not q)) :rule equiv_pos1)": false,
        }
    }
}

#[test]
fn test_equiv_pos2_rule() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
        ",
        "Simple working examples" {
            "(step t1 (cl (not (= p q)) (not p) q) :rule equiv_pos2)": true,
            "(step t1 (cl (not (= (not p) q)) (not (not p)) q) :rule equiv_pos2)": true,
            "(step t1 (cl (not (= p (not q))) (not p) (not q)) :rule equiv_pos2)": true,
        }
        "Number of terms in clause != 3" {
            "(step t1 (cl (not (= p q)) (not p)) :rule equiv_pos2)": false,
            "(step t1 (cl (not (= p q)) (not p) q q) :rule equiv_pos2)": false,
        }
        "Term in clause is not of the correct form" {
            "(step t1 (cl (= p q) (not p) q) :rule equiv_pos2)": false,
            "(step t1 (cl (and p q) (not p) q) :rule equiv_pos2)": false,
            "(step t1 (cl (not (= p q)) p q) :rule equiv_pos2)": false,
        }
        "Terms don't match" {
            "(step t1 (cl (not (= p q)) (not q) q) :rule equiv_pos2)": false,
            "(step t1 (cl (not (= p q)) (not p) p) :rule equiv_pos2)": false,
            "(step t1 (cl (not (= p (not q))) (not p) q) :rule equiv_pos2)": false,
        }
    }
}

#[test]
fn test_eq_reflexive_rule() {
    test_cases! {
        definitions = "
            (declare-fun a () Int)
            (declare-fun b () Int)
            (declare-fun f (Int Int) Int)
        ",
        "Simple working examples" {
            "(step t1 (cl (= a a)) :rule eq_reflexive)": true,
            "(step t1 (cl (= false false)) :rule eq_reflexive)": true,
            "(step t1 (cl (= (f a b) (f a b))) :rule eq_reflexive)": true,
            "(step t1 (cl (= (+ b a) (+ b a))) :rule eq_reflexive)": true,
        }
        "Number of terms in clause != 1" {
            "(step t1 (cl) :rule eq_reflexive)": false,
            "(step t1 (cl (= a a) (= b b)) :rule eq_reflexive)": false,
        }
        "Term is not an equality" {
            "(step t1 (cl (not (= b b))) :rule eq_reflexive)": false,
            "(step t1 (cl (and (= a a) (= b b))) :rule eq_reflexive)": false,
        }
        "Terms in equality aren't equal" {
            "(step t1 (cl (= a b)) :rule eq_reflexive)": false,
            "(step t1 (cl (= (f a b) (f b a))) :rule eq_reflexive)": false,
            "(step t1 (cl (= (+ a b) (+ b a))) :rule eq_reflexive)": false,
        }

    }
}

#[test]
fn test_eq_transitive_rule() {
    test_cases! {
        definitions = "
            (declare-sort T 0)
            (declare-fun a () T)
            (declare-fun b () T)
            (declare-fun c () T)
            (declare-fun d () T)
            (declare-fun e () T)
        ",

        "Simple working examples" {
            "(step t1 (cl (not (= a b)) (not (= b c)) (= a c)) :rule eq_transitive)": true,

            "(step t1 (cl (not (= a b)) (not (= b c)) (not (= c d)) (= a d))
                :rule eq_transitive)": true,

            "(step t1 (cl (not (= a a)) (not (= a a)) (= a a)) :rule eq_transitive)": true,
        }
        "Inequality terms in different orders" {
            "(step t1 (cl (not (= a b)) (not (= c b)) (not (= c d)) (= d a))
                :rule eq_transitive)": true,

            "(step t1 (cl (not (= b a)) (not (= c b)) (not (= d c)) (= a d))
                :rule eq_transitive)": true,
        }
        "Clause term is not an inequality" {
            "(step t1 (cl (= a b) (not (= b c)) (= a c)) :rule eq_transitive)": false,

            "(step t1 (cl (not (= a b)) (= b c) (= a c)) :rule eq_transitive)": false,
        }
        "Final term is not an equality" {
            "(step t1 (cl (not (= a b)) (not (= b c)) (not (= a c))) :rule eq_transitive)": false,
        }
        "Clause is too small" {
            "(step t1 (cl (not (= a b)) (= a b)) :rule eq_transitive)": false,
        }
        "Clause terms in different orders" {
            "(step t1 (cl (not (= a b)) (not (= c d)) (not (= b c)) (= a d))
                :rule eq_transitive)": true,

            "(step t1 (cl (not (= c d)) (not (= b c)) (not (= a b)) (= a d))
                :rule eq_transitive)": true,
        }
        "Clause doesn't form transitive chain" {
            "(step t1 (cl (not (= a b)) (not (= c d)) (= a d)) :rule eq_transitive)": false,

            "(step t1 (cl (not (= a b)) (not (= b b)) (not (= c d)) (= a d))
                :rule eq_transitive)": false,

            "(step t1 (cl (not (= a b)) (not (= b c)) (not (= c d)) (= a e))
                :rule eq_transitive)": false,

            "(step t1 (cl (not (= a b)) (not (= b e)) (not (= b c)) (= a c))
                :rule eq_transitive)": false,
        }
    }
}

#[test]
fn test_eq_congruent_rule() {
    test_cases! {
        definitions = "
            (declare-fun a () Int)
            (declare-fun b () Int)
            (declare-fun c () Int)
            (declare-fun x () Int)
            (declare-fun y () Int)
            (declare-fun z () Int)
            (declare-fun f (Int Int) Int)
            (declare-fun g (Int Int) Int)
            (declare-fun f-1 (Int) Int)
            (declare-fun f-3 (Int Int Int) Int)
        ",

        "Simple working examples" {
            "(step t1 (cl (not (= a b)) (= (f-1 a) (f-1 b))) :rule eq_congruent)": true,

            "(step t1 (cl (not (= a x)) (not (= b y)) (not (= c z))
                      (= (f-3 a b c) (f-3 x y z))) :rule eq_congruent)": true,

            "(step t1 (cl (not (= a x)) (not (= b y)) (not (= c z))
                      (= (* a b c) (* x y z))) :rule eq_congruent)": true,
        }
        "t_i and u_i are possibly flipped" {
            "(step t1 (cl (not (= b a)) (= (f-1 a) (f-1 b))) :rule eq_congruent)": true,

            "(step t1 (cl (not (= x a)) (not (= b y)) (not (= z c))
                      (= (f-3 a b c) (f-3 x y z))) :rule eq_congruent)": true,

            "(step t1 (cl (not (= a x)) (not (= b y)) (= (f x y) (f a b)))
                :rule eq_congruent)": true,
        }
        "Clause term is not an inequality" {
            "(step t1 (cl (not (= a x)) (= b y) (= (f a b) (f x y))) :rule eq_congruent)": false,
        }
        "Final term is not an equality of applications" {
            "(step t1 (cl (not (= a x)) (not (= b y)) (= (+ a b) (f x y)))
                :rule eq_congruent)": false,
        }
        "Functions are not the same" {
            "(step t1 (cl (not (= a x)) (not (= b y)) (= (f a b) (g x y)))
                :rule eq_congruent)": false,

            "(step t1 (cl (not (= a x)) (not (= b y)) (not (= c z))
                      (= (* a b c) (+ x y z))) :rule eq_congruent)": false,
        }
        "Number of function arguments is not the same as the number of inequalities" {
            "(step t1 (cl (not (= a x)) (not (= b y)) (= (f-3 a b c) (f-3 x y z)))
                :rule eq_congruent)": false,

            "(step t1 (cl (not (= a x)) (not (= b y)) (= (+ a b) (+ x y z)))
                :rule eq_congruent)": false,
        }
        "Terms don't match" {
            "(step t1 (cl (not (= a x)) (not (= b y)) (= (f b a) (f x y)))
                :rule eq_congruent)": false,

            "(step t1 (cl (not (= a x)) (not (= b y)) (= (f a b) (f c z)))
                :rule eq_congruent)": false,
        }
    }
}

#[test]
fn test_eq_congruent_pred_rule() {
    test_cases! {
        definitions = "
            (declare-fun a () Bool)
            (declare-fun b () Bool)
            (declare-fun c () Bool)
            (declare-fun x () Bool)
            (declare-fun y () Bool)
            (declare-fun z () Bool)
            (declare-fun p (Bool Bool) Bool)
            (declare-fun q (Bool Bool) Bool)
            (declare-fun p-1 (Bool) Bool)
            (declare-fun p-3 (Bool Bool Bool) Bool)
        ",

        "Simple working examples" {
            "(step t1 (cl (not (= a b)) (not (p-1 a)) (p-1 b)) :rule eq_congruent_pred)": true,

            "(step t1 (cl (not (= a x)) (not (= b y)) (not (= c z))
                      (not (p-3 a b c)) (p-3 x y z)) :rule eq_congruent_pred)": true,

            "(step t1 (cl (not (= a x)) (not (= b y)) (not (= c z))
                      (not (and a b c)) (and x y z)) :rule eq_congruent_pred)": true,
        }
        "t_i and u_i are possibly flipped" {
            "(step t1 (cl (not (= b a)) (not (p-1 a)) (p-1 b)) :rule eq_congruent_pred)": true,

            "(step t1 (cl (not (= x a)) (not (= b y)) (not (= z c))
                      (not (p-3 a b c)) (p-3 x y z)) :rule eq_congruent_pred)": true,

            "(step t1 (cl (not (= a x)) (not (= b y)) (not (p x y)) (p a b))
                :rule eq_congruent_pred)": true,
        }
        "Clause term is not an inequality" {
            "(step t1 (cl (not (= a x)) (= b y) (not (p a b)) (p x y))
                :rule eq_congruent_pred)": false,
        }
        "Final two terms are in the wrong order" {
            "(step t1 (cl (not (= a x)) (not (= b y)) (p a b) (not (p x y)))
                :rule eq_congruent_pred)": false,
        }
        "Functions are not the same" {
            "(step t1 (cl (not (= a x)) (not (= b y)) (not (p a b)) (q x y))
                :rule eq_congruent_pred)": false,

            "(step t1 (cl (not (= a x)) (not (= b y)) (not (= c z))
                      (not (or a b c)) (and x y z)) :rule eq_congruent_pred)": false,
        }
        "Number of function arguments is not the same as the number of inequalities" {
            "(step t1 (cl (not (= a x)) (not (= b y)) (not (p-3 a b c)) (p-3 x y z))
                :rule eq_congruent_pred)": false,

            "(step t1 (cl (not (= a x)) (not (= b y)) (not (and a b)) (and x y z))
                :rule eq_congruent_pred)": false,
        }
        "Terms don't match" {
            "(step t1 (cl (not (= a x)) (not (= b y)) (not (p b a)) (p x y))
                :rule eq_congruent_pred)": false,

            "(step t1 (cl (not (= a x)) (not (= b y)) (not (p a b)) (p c z))
                :rule eq_congruent_pred)": false,
        }
    }
}

#[test]
fn test_distinct_elim_rule() {
    test_cases! {
        definitions = "
            (declare-sort T 0)
            (declare-fun a () T)
            (declare-fun b () T)
            (declare-fun c () T)
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun r () Bool)
        ",

        "Simple working examples" {
            "(step t1 (cl (= (distinct a b) (not (= a b)))) :rule distinct_elim)": true,

            "(step t1 (cl (= (distinct a b c) (and
                (not (= a b))
                (not (= a c))
                (not (= b c))
            ))) :rule distinct_elim)": true,
        }
        "Inequality terms in different orders" {
            "(step t1 (cl (= (distinct a b) (not (= b a)))) :rule distinct_elim)": true,

            "(step t1 (cl (= (distinct a b c) (and
                (not (= b a))
                (not (= a c))
                (not (= c b))
            ))) :rule distinct_elim)": true,
        }
        "Conjunction terms in wrong order" {
            "(step t1 (cl (= (distinct a b c) (and
                (not (= b c))
                (not (= a b))
                (not (= a c))
            ))) :rule distinct_elim)": false,
        }
        "\"distinct\" on more than two booleans should be \"false\"" {
            "(step t1 (cl (= (distinct p q r) false)) :rule distinct_elim)": true,

            "(step t1 (cl (= (distinct p q r) (and
                (not (= p q))
                (not (= p r))
                (not (= q r))
            ))) :rule distinct_elim)": false,
        }
    }
}

#[test]
fn test_la_rw_eq_rule() {
    test_cases! {
        definitions = "
            (declare-fun a () Int)
            (declare-fun b () Int)
            (declare-fun x () Real)
            (declare-fun y () Real)
        ",
        "Simple working examples" {
            "(step t1 (cl (= (= a b) (and (<= a b) (<= b a)))) :rule la_rw_eq)": true,
            "(step t1 (cl (= (= x y) (and (<= x y) (<= y x)))) :rule la_rw_eq)": true,
        }
        "Clause term is not of the correct form" {
            "(step t1 (cl (= (= b a) (and (<= a b) (<= b a)))) :rule la_rw_eq)": false,
            "(step t1 (cl (= (= x y) (and (<= x y) (<= x y)))) :rule la_rw_eq)": false,
        }
    }
}

#[test]
fn test_la_generic_rule() {
    test_cases! {
        definitions = "
            (declare-fun a () Real)
            (declare-fun b () Real)
            (declare-fun c () Real)
        ",
        "Simple working examples" {
            "(step t1 (cl (> a 0.0) (<= a 0.0)) :rule la_generic :args (1.0 1.0))": true,
            "(step t1 (cl (>= a 0.0) (< a 0.0)) :rule la_generic :args (1.0 1.0))": true,
            "(step t1 (cl (<= 0.0 0.0)) :rule la_generic :args (1.0))": true,

            "(step t1 (cl (< (+ a b) 1.0) (> (+ a b) 0.0))
                :rule la_generic :args (1.0 (- 1.0)))": true,

            "(step t1 (cl (<= (+ a (- b a)) b)) :rule la_generic :args (1.0))": true,

            "(step t1 (cl (not (<= (- a b) (- c 1.0))) (<= (+ 1.0 (- a c)) b))
                :rule la_generic :args (1.0 1.0))": true,
        }
        "Empty clause" {
            "(step t1 (cl) :rule la_generic)": false,
        }
        "Wrong number of arguments" {
            "(step t1 (cl (>= a 0.0) (< a 0.0)) :rule la_generic :args (1.0 1.0 1.0))": false,
        }
        "Invalid argument term" {
            "(step t1 (cl (>= a 0.0) (< a 0.0)) :rule la_generic :args (1.0 b))": false,
        }
        "Clause term is not of the correct form" {
            "(step t1 (cl (ite (= a b) false true)) :rule la_generic :args (1.0))": false,
            "(step t1 (cl (= a 0.0) (< a 0.0)) :rule la_generic :args (1.0 1.0))": false,
        }
        "Negation of disequalities is satisfiable" {
            "(step t1 (cl (< 0.0 0.0)) :rule la_generic :args (1.0))": false,

            "(step t1 (cl (< (+ a b) 1.0) (> (+ a b c) 0.0))
                :rule la_generic :args (1.0 (- 1.0)))": false,
        }
    }
}

#[test]
fn test_la_disequality_rule() {
    test_cases! {
        definitions = "
            (declare-fun a () Int)
            (declare-fun b () Int)
            (declare-fun x () Real)
            (declare-fun y () Real)
        ",
        "Simple working examples" {
            "(step t1 (cl (or (= a b) (not (<= a b)) (not (<= b a)))) :rule la_disequality)": true,
            "(step t1 (cl (or (= x y) (not (<= x y)) (not (<= y x)))) :rule la_disequality)": true,
        }
        "Clause term is not of the correct form" {
            "(step t1 (cl (or (= b a) (not (<= a b)) (not (<= b a)))) :rule la_disequality)": false,
            "(step t1 (cl (or (= x y) (not (<= y x)) (not (<= y x)))) :rule la_disequality)": false,
        }
    }
}

#[test]
fn test_resolution_rule() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun r () Bool)
        ",

        "Simple working examples" {
            "(assume h1 (not p))
            (assume h2 (or p q))
            (step t3 (cl p q) :rule or :premises (h2))
            (step t4 (cl q) :rule resolution :premises (h1 t3))": true,

            "(assume h1 (not p))
            (assume h2 (not q))
            (assume h3 (not r))
            (assume h4 (or p q r))
            (step t5 (cl p q r) :rule or :premises (h4))
            (step t6 (cl) :rule resolution :premises (h1 h2 h3 t5))": true,

            "(assume h1 (not p))
            (assume h2 q)
            (assume h3 (or p (not q)))
            (step t4 (cl p (not q)) :rule or :premises (h3))
            (step t5 (cl) :rule resolution :premises (h1 h2 t4))": true,
        }
        "Missing term in final clause" {
            "(assume h1 (not p))
            (assume h2 (or p q r))
            (step t3 (cl p q r) :rule or :premises (h2))
            (step t4 (cl q) :rule resolution :premises (h1 t3))": false,
        }
        "Extra term in final clause" {
            "(assume h1 (not p))
            (assume h2 (or p q r))
            (step t3 (cl p q r) :rule or :premises (h2))
            (step t4 (cl p q r) :rule resolution :premises (h1 t3))": false,
        }
        "Term appears in final clause with wrong polarity" {
            "(assume h1 (not p))
            (assume h2 (or p q r))
            (step t3 (cl p q r) :rule or :premises (h2))
            (step t4 (cl (not q) r) :rule resolution :premises (h1 t3))": false,
        }
        "Duplicate term in final clause" {
            "(assume h1 (or q (not p)))
            (assume h2 (or p q r))
            (step t3 (cl q (not p)) :rule or :premises (h1))
            (step t4 (cl p q r) :rule or :premises (h2))
            (step t5 (cl q q r) :rule resolution :premises (t3 t4))": true,
        }
        "Terms with leading negations" {
            "(assume h1 (not p))
            (assume h2 (not (not p)))
            (assume h3 (not (not (not p))))
            (assume h4 (not (not (not (not p)))))
            (step t5 (cl) :rule resolution :premises (h1 h2))
            (step t6 (cl) :rule resolution :premises (h2 h3))
            (step t7 (cl (not p) (not (not (not p)))) :rule resolution :premises (h1 h3))
            (step t8 (cl (not p) (not (not (not (not p)))))
                :rule resolution :premises (h1 h4))": true,
        }
        "Must use correct pivots" {
            "(assume h1 (or (not q) (not (not p)) (not p)))
            (assume h2 (or (not (not (not p))) p))
            (step t3 (cl (not q) (not (not p)) (not p)) :rule or :premises (h1))
            (step t4 (cl (not (not (not p))) p) :rule or :premises (h2))
            (step t5 (cl (not q) p (not p)) :rule resolution :premises (t3 t4))": true,

            "(assume h1 (or (not q) (not (not p)) (not p)))
            (assume h2 (or (not (not (not p))) p))
            (step t3 (cl (not q) (not (not p)) (not p)) :rule or :premises (h1))
            (step t4 (cl (not (not (not p))) p) :rule or :premises (h2))
            (step t5 (cl (not q) (not (not (not p))) (not (not p)))
                :rule resolution :premises (t3 t4))": true,

            "(assume h1 (or (not q) (not (not p)) (not p)))
            (assume h2 (or (not (not (not p))) p))
            (step t3 (cl (not q) (not (not p)) (not p)) :rule or :premises (h1))
            (step t4 (cl (not (not (not p))) p) :rule or :premises (h2))
            (step t5 (cl (not q) p (not p) (not (not (not p))) (not (not p)))
                :rule resolution :premises (t3 t4))": true,
        }
    }
}

#[test]
fn test_cong_rule() {
    test_cases! {
        definitions = "
            (declare-sort T 0)
            (declare-fun a () T)
            (declare-fun b () T)
            (declare-fun c () T)
            (declare-fun d () T)
            (declare-fun f (T Bool T) T)
            (declare-fun g (T Bool T) T)
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun r () Bool)
            (declare-fun s () Bool)
            (declare-fun x () Real)
            (declare-fun y () Real)
        ",
        "Simple working examples" {
            "(assume h1 (= a b))
            (assume h2 (= c d))
            (step t3 (cl (= (f b false c) (f a false d))) :rule cong :premises (h1 h2))": true,

            "(assume h1 (= p q))
            (assume h2 (= r s))
            (step t3 (cl (= (and p false s) (and q false r))) :rule cong :premises (h1 h2))": true,
        }
        "Functions or operators don't match" {
            "(assume h1 (= a b))
            (assume h2 (= c d))
            (step t3 (cl (= (f b false c) (g a false d))) :rule cong :premises (h1 h2))": false,

            "(assume h1 (= p q))
            (assume h2 (= r s))
            (step t3 (cl (= (and p false s) (or q false r))) :rule cong :premises (h1 h2))": false,
        }
        "No premises were given" {
            "(step t1 (cl (= (f a true c) (f a true c))) :rule cong)": false,
        }
        "Wrong number of premises" {
            "(assume h1 (= a b))
            (assume h2 (= p q))
            (step t3 (cl (= (f a p c) (f b q d))) :rule cong :premises (h1 h2))": false,

            "(assume h1 (= a b))
            (assume h2 (= p q))
            (assume h3 (= c d))
            (assume h4 (= r s))
            (step t5 (cl (= (f a p c) (f b q d))) :rule cong :premises (h1 h2 h3 h4))": false,
        }
        "Premise doesn't match expected terms" {
            "(assume h1 (= a b))
            (assume h2 (= r s))
            (assume h3 (= c d))
            (step t4 (cl (= (f a p c) (f b q d))) :rule cong :premises (h1 h2 h3))": false,

            "(assume h1 (= a b))
            (assume h2 (= c d))
            (assume h3 (= p q))
            (step t4 (cl (= (f a p c) (f b q d))) :rule cong :premises (h1 h2 h3))": false,
        }
        "Should prefer consuming premise than relying on reflexivity" {
            "(assume h1 (= false false))
            (assume h2 (= r s))
            (step t3 (cl (= (and false false s) (and false false r))) :rule cong :premises (h1 h2))": true,

            "(assume h1 (= (- 1.0) (- 1.0)))
            (step t2 (cl (= (< x (- 1.0)) (< x (- 1.0)))) :rule cong :premises (h1))": true,
        }
        "Argument order may be flipped if operator is \"=\"" {
            "(assume h1 (= x y))
            (step t2 (cl (= (= 0.0 x) (= y 0.0))) :rule cong :premises (h1))": true,

            "(assume h1 (= x y))
            (step t2 (cl (= (= x 0.0) (= 0.0 y))) :rule cong :premises (h1))": true,

            "(assume h1 (= a b)) (assume h2 (= c d))
            (step t3 (cl (= (= c a) (= b d))) :rule cong :premises (h1 h2))": true,

            "(assume h1 (= a b)) (assume h2 (= c d))
            (step t3 (cl (= (= a c) (= d b))) :rule cong :premises (h1 h2))": true,

            "(assume h1 (= a b)) (assume h2 (= c d))
            (step t3 (cl (= (= c a) (= d b))) :rule cong :premises (h1 h2))": true,
        }
    }
}

#[test]
fn test_and_rule() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun r () Bool)
            (declare-fun s () Bool)
        ",
        "Simple working examples" {
            "(assume h1 (and p q))
            (step t2 (cl q) :rule and :premises (h1))": true,

            "(assume h1 (and p q r s))
            (step t2 (cl p) :rule and :premises (h1))": true,

            "(assume h1 (and p q r s))
            (step t2 (cl s) :rule and :premises (h1))": true,
        }
        "Number of premises != 1" {
            "(step t1 (cl p) :rule and)": false,

            "(assume h1 (and p q))
            (assume h2 (and r s))
            (step t2 (cl r) :rule and :premises (h1 h2))": false,
        }
        "Premise clause has more than one term" {
            "(assume h1 (or (and p q) (and r s)))
            (step t2 (cl (and p q) (and r s)) :rule or :premises (h1))
            (step t3 (cl p) :rule and :premises (t2))": false,
        }
        "Conclusion clause does not have exactly one term" {
            "(assume h1 (and p q r s))
            (step t2 (cl q s) :rule and :premises (h1))": false,

            "(assume h1 (and p q))
            (step t2 (cl) :rule and :premises (h1))": false,
        }
        "Premise is not an \"and\" operation" {
            "(assume h1 (or p q r s))
            (step t2 (cl r) :rule and :premises (h1))": false,
        }
        "Conclusion term is not in premise" {
            "(assume h1 (and p q r))
            (step t2 (cl s) :rule and :premises (h1))": false,
        }
    }
}

#[test]
fn test_or_rule() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun r () Bool)
            (declare-fun s () Bool)
        ",

        "Simple working examples" {
            "(assume h1 (or p q))
            (step t2 (cl p q) :rule or :premises (h1))": true,

            "(assume h1 (or p q r s))
            (step t2 (cl p q r s) :rule or :premises (h1))": true,
        }
        "Number of premises != 1" {
            "(step t1 (cl p q r) :rule or)": false,

            "(assume h1 (or p q))
            (assume h2 (or q r))
            (step t3 (cl p q r) :rule or :premises (h1 h2))": false,
        }
        "Premise clause has more than one term" {
            "(assume h1 (or p (or q r)))
            (step t2 (cl p (or q r)) :rule or :premises (h1))
            (step t3 (cl p q) :rule or :premises (t2))": false,
        }
        "Premise is not an \"or\" operation" {
            "(assume h1 (and p q))
            (step t2 (cl p q) :rule or :premises (h1))": false,
        }
        "Premise and clause contents are different" {
            "(assume h1 (or p q))
            (step t2 (cl r s) :rule or :premises (h1))": false,

            "(assume h1 (or p q r))
            (step t2 (cl p q) :rule or :premises (h1))": false,

            "(assume h1 (or q p))
            (step t2 (cl p q) :rule or :premises (h1))": false,
        }
    }
}

#[test]
fn test_implies() {
    test_cases! {
        definitions = "
            (declare-fun a () Bool)
            (declare-fun b () Bool)
        ",
        "Simple working examples" {
            "(assume h1 (=> a b))
            (step t2 (cl (not a) b) :rule implies :premises (h1))": true,

            "(assume h1 (=> (not a) b))
            (step t2 (cl (not (not a)) b) :rule implies :premises (h1))": true,
        }
        "Premise term is not an \"implies\" term" {
            "(assume h1 (= a b))
            (step t2 (cl (not a) b) :rule implies :premises (h1))": false,
        }
        "Conclusion clause is of the wrong form" {
            "(assume h1 (=> a b))
            (step t2 (cl b (not a)) :rule implies :premises (h1))": false,

            "(assume h1 (=> a b))
            (step t2 (cl a (not b)) :rule implies :premises (h1))": false,

            "(assume h1 (=> (not a) b))
            (step t2 (cl a b) :rule implies :premises (h1))": false,
        }
    }
}

#[test]
fn test_ite1_rule() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun a () Bool)
            (declare-fun b () Bool)
        ",
        "Simple working examples" {
            "(assume h1 (ite p a b))
            (step t2 (cl p b) :rule ite1 :premises (h1))": true,
        }
        "Premise term is not an \"ite\" term" {
            "(assume h1 (or p a b))
            (step t2 (cl p b) :rule ite1 :premises (h1))": false,
        }
        "Conclusion clause is of the wrong form" {
            "(assume h1 (ite p a b))
            (step t2 (cl b p) :rule ite1 :premises (h1))": false,

            "(assume h1 (ite p a b))
            (step t2 (cl p a) :rule ite1 :premises (h1))": false,

            "(assume h1 (ite p a b))
            (step t2 (cl p) :rule ite1 :premises (h1))": false,

            "(assume h1 (ite p a b))
            (step t2 (cl p a b) :rule ite1 :premises (h1))": false,
        }
    }
}

#[test]
fn test_ite2_rule() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun a () Bool)
            (declare-fun b () Bool)
        ",
        "Simple working examples" {
            "(assume h1 (ite p a b))
            (step t2 (cl (not p) a) :rule ite2 :premises (h1))": true,
        }
        "Premise term is not an \"ite\" term" {
            "(assume h1 (or p a b))
            (step t2 (cl (not p) a) :rule ite2 :premises (h1))": false,
        }
        "Conclusion clause is of the wrong form" {
            "(assume h1 (ite p a b))
            (step t2 (cl a (not p)) :rule ite2 :premises (h1))": false,

            "(assume h1 (ite (not p) a b))
            (step t2 (cl p a) :rule ite2 :premises (h1))": false,

            "(assume h1 (ite p a b))
            (step t2 (cl (not p) b) :rule ite2 :premises (h1))": false,

            "(assume h1 (ite p a b))
            (step t2 (cl (not p)) :rule ite2 :premises (h1))": false,

            "(assume h1 (ite p a b))
            (step t2 (cl (not p) a b) :rule ite2 :premises (h1))": false,
        }
    }
}

#[test]
fn test_ite_intro_rule() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun a () Bool)
            (declare-fun b () Bool)
            (declare-fun c () Bool)
            (declare-fun d () Bool)
        ",
        "Simple working examples" {
            "(step t1 (cl (=
                (ite p a b)
                (and (ite p a b) (ite p (= a (ite p a b)) (= b (ite p a b))))
            )) :rule ite_intro)": true,

            "(step t1 (cl (=
                (not (ite p a b))
                (and (not (ite p a b)) (ite p (= a (ite p a b)) (= b (ite p a b))))
            )) :rule ite_intro)": true,
        }
        "Multiple \"ite\" subterms" {
            "(step t1 (cl (=
                (or (ite p a b) (ite q c d))
                (and
                    (or (ite p a b) (ite q c d))
                    (ite p (= a (ite p a b)) (= b (ite p a b)))
                    (ite q (= c (ite q c d)) (= d (ite q c d)))
                )
            )) :rule ite_intro)": true,

            "(step t1 (cl (=
                (or (ite p a b) (and (ite q c d) (ite (not p) b (not d))))
                (and
                    (or (ite p a b) (and (ite q c d) (ite (not p) b (not d))))
                    (ite p (= a (ite p a b)) (= b (ite p a b)))
                    (ite q (= c (ite q c d)) (= d (ite q c d)))
                    (ite (not p) (= b (ite (not p) b (not d))) (= (not d) (ite (not p) b (not d))))
                )
            )) :rule ite_intro)": true,
        }
        "Clause term is not an equality" {
            "(step t1 (cl) :rule ite_intro)": false,
            "(step t1 (cl (not (= p q))) :rule ite_intro)": false,
        }
        "Conjunction is not an \"and\" term" {
            "(step t1 (cl (=
                (ite p a b)
                (or (ite p a b) (ite p (= a (ite p a b)) (= b (ite p a b))))
            )) :rule ite_intro)": false,
        }
        "First term in conjunction is not root term" {
            "(step t1 (cl (=
                (ite p a b)
                (and q (ite p (= a (ite p a b)) (= b (ite p a b))))
            )) :rule ite_intro)": false,
        }
        "Conjunction has the wrong number of terms" {
            "(step t1 (cl (=
                (or (ite p a b) (ite q c d))
                (and
                    (or (ite p a b) (ite q c d))
                    (ite p (= a (ite p a b)) (= b (ite p a b)))
                )
            )) :rule ite_intro)": false,

            "(step t1 (cl (=
                (or (ite p a b) (ite q c d))
                (and
                    (or (ite p a b) (ite q c d))
                    (ite p (= a (ite p a b)) (= b (ite p a b)))
                    (ite q (= c (ite q c d)) (= d (ite q c d)))
                    p
                )
            )) :rule ite_intro)": false,
        }
        "Right side may equal root term" {
            "(step t1 (cl (= (or a b) (or a b))) :rule ite_intro)": true,
            "(step t1 (cl (= (ite p a b) (ite p a b))) :rule ite_intro)": true,
            "(step t1 (cl (=
                (and (ite p a b) (or (ite q c d) (ite (not p) b (not d))))
                (and (ite p a b) (or (ite q c d) (ite (not p) b (not d))))
            )) :rule ite_intro)": true,
        }
    }
}

#[test]
fn test_contraction_rule() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun r () Bool)
            (declare-fun s () Bool)
        ",
        "Simple working examples" {
            "(assume h1 (or p q q r s s))
            (step t2 (cl p q q r s s) :rule or :premises (h1))
            (step t3 (cl p q r s) :rule contraction :premises (t2))": true,

            "(assume h1 (or p p p q q r s s s))
            (step t2 (cl p p p q q r s s s) :rule or :premises (h1))
            (step t3 (cl p q r s) :rule contraction :premises (t2))": true,

            "(assume h1 (or p q r s))
            (step t2 (cl p q r s) :rule or :premises (h1))
            (step t3 (cl p q r s) :rule contraction :premises (t2))": true,
        }
        "Number of premises != 1" {
            "(step t1 (cl p q) :rule contraction)": false,

            "(assume h1 q)
            (assume h2 p)
            (step t3 (cl p q) :rule contraction :premises (h1 h2))": false,
        }
        "Premise is not a \"step\" command" {
            "(assume h1 q)
            (step t2 (cl q) :rule contraction :premises (h1))": false,
        }
        "Encountered wrong term" {
            "(assume h1 (or p p q))
            (step t2 (cl p p q) :rule or :premises (h1))
            (step t3 (cl p r) :rule contraction :premises (t2))": false,
        }
        "Terms are not in correct order" {
            "(assume h1 (or p q q r))
            (step t2 (cl p q q r) :rule or :premises (h1))
            (step t3 (cl p r q) :rule contraction :premises (t2))": false,
        }
        "Conclusion is missing terms" {
            "(assume h1 (or p q q r))
            (step t2 (cl p q q r) :rule or :premises (h1))
            (step t3 (cl p r) :rule contraction :premises (t2))": false,

            "(assume h1 (or p p q r))
            (step t2 (cl p p q r) :rule or :premises (h1))
            (step t3 (cl p q) :rule contraction :premises (t2))": false,
        }
        "Conclusion has extra term at the end" {
            "(assume h1 (or p p q))
            (step t2 (cl p p q) :rule or :premises (h1))
            (step t3 (cl p q r s) :rule contraction :premises (t2))": false,
        }
    }
}

#[test]
fn test_bool_simplify_rule() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun r () Bool)
        ",
        "Transformation #1" {
            "(step t1 (cl (=
                (not (=> p q)) (and p (not q))
            )) :rule bool_simplify)": true,

            "(step t1 (cl (=
                (not (=> p q)) (and (not q) p)
            )) :rule bool_simplify)": false,

            "(step t1 (cl (=
                (not (=> p (not q))) (and p q)
            )) :rule bool_simplify)": false,
        }
        "Transformation #2" {
            "(step t1 (cl (=
                (not (or p q)) (and (not p) (not q))
            )) :rule bool_simplify)": true,

            "(step t1 (cl (=
                (not (or (not p) (not q))) (and p q)
            )) :rule bool_simplify)": false,
        }
        "Transformation #3" {
            "(step t1 (cl (=
                (not (and p q)) (or (not p) (not q))
            )) :rule bool_simplify)": true,

            "(step t1 (cl (=
                (not (and (not p) (not q))) (or p q)
            )) :rule bool_simplify)": false,
        }
        "Transformation #4" {
            "(step t1 (cl (=
                (=> p (=> q r)) (=> (and p q) r)
            )) :rule bool_simplify)": true,

            "(step t1 (cl (=
                (=> p (=> q r)) (=> (and q p) r)
            )) :rule bool_simplify)": false,
        }
        "Transformation #5" {
            "(step t1 (cl (=
                (=> (=> p q) q) (or p q)
            )) :rule bool_simplify)": true,

            "(step t1 (cl (=
                (=> (=> p q) r) (or p q)
            )) :rule bool_simplify)": false,
        }
        "Transformation #6" {
            "(step t1 (cl (=
                (and p (=> p q)) (and p q)
            )) :rule bool_simplify)": true,

            "(step t1 (cl (=
                (and p (=> r q)) (and p q)
            )) :rule bool_simplify)": false,
        }
        "Transformation #7" {
            "(step t1 (cl (=
                (and (=> p q) p) (and p q)
            )) :rule bool_simplify)": true,

            "(step t1 (cl (=
                (and (=> p q) r) (and p q)
            )) :rule bool_simplify)": false,
        }
        // TODO: Add tests that combine more than one transformation
    }
}

#[test]
fn test_prod_simplify_rule() {
    test_cases! {
        definitions = "
            (declare-fun i () Int)
            (declare-fun j () Int)
            (declare-fun k () Int)
            (declare-fun x () Real)
            (declare-fun y () Real)
            (declare-fun z () Real)
        ",
        "Transformation #1" {
            "(step t1 (cl (= (* 2 3 5 7) 210)) :rule prod_simplify)": true,
            "(step t1 (cl (= 0.555 (* 1.5 3.7 0.1))) :rule prod_simplify)": true,
            "(step t1 (cl (= (* 1 1 1) 1)) :rule prod_simplify)": true,

            "(step t1 (cl (= (* 1 2 4) 6)) :rule prod_simplify)": false,
            "(step t1 (cl (= (* 1.0 2.0 1.0) 4.0)) :rule prod_simplify)": false,
        }
        "Transformation #2" {
            "(step t1 (cl (= (* 2 3 0 7) 0)) :rule prod_simplify)": true,
            "(step t1 (cl (= (* 1.5 3.7 0.0) 0.0)) :rule prod_simplify)": true,
            "(step t1 (cl (= 0 (* i 2 k 3 0 j))) :rule prod_simplify)": true,
            "(step t1 (cl (= (* i j 0 k) 0)) :rule prod_simplify)": true,
            "(step t1 (cl (= (* x y 1.0 2.0 z 0.0 z) 0.0)) :rule prod_simplify)": true,

            "(step t1 (cl (= (* 2 4 0 3) 24)) :rule prod_simplify)": false,
            "(step t1 (cl (= (* 1 1 2 3) 0)) :rule prod_simplify)": false,
            "(step t1 (cl (= (* i j 0 k) (* i j k))) :rule prod_simplify)": false,
        }
        "Transformation #3" {
            "(step t1 (cl (= (* 30 i k j) (* i 2 k 3 5 j))) :rule prod_simplify)": true,
            "(step t1 (cl (= (* i k 6 j) (* 6 i k j))) :rule prod_simplify)": true,
            "(step t1 (cl (= (* 6.0 x y z z) (* x y 1.0 2.0 z 3.0 z))) :rule prod_simplify)": true,
            "(step t1 (cl (= (* x y 2.0 z z) (* 2.0 x y z z))) :rule prod_simplify)": true,

            "(step t1 (cl (= (* i 2 k 3 5 j) (* 60 i k j))) :rule prod_simplify)": false,
            "(step t1 (cl (= (* i k 6 j) (* i k 6 j))) :rule prod_simplify)": false,
            "(step t1 (cl (= (* x y 1.0 2.0 z 3.0 z) (* 4.0 x y z z))) :rule prod_simplify)": false,
            "(step t1 (cl (= (* x y 1.0 2.0 z 3.0 z) (* x y z z))) :rule prod_simplify)": false,
        }
        "Transformation #4" {
            "(step t1 (cl (= (* i k 1 j) (* i k j))) :rule prod_simplify)": true,
            "(step t1 (cl (= (* i 1 1 k 1 j) (* i k j))) :rule prod_simplify)": true,
            "(step t1 (cl (= (* x y z z) (* x y 1.0 z z))) :rule prod_simplify)": true,
            "(step t1 (cl (= (* x y 5.0 1.0 z 0.2 z) (* x y z z))) :rule prod_simplify)": true,

            "(step t1 (cl (= (* i k 1 j) (* 1 i k j))) :rule prod_simplify)": false,
            "(step t1 (cl (= (* x y 5.0 1.0 z 0.2 z) (* 1.0 x y z z))) :rule prod_simplify)": false,
        }
        "Clause is of the wrong form" {
            "(step t1 (cl (= (* i 1 1) i)) :rule prod_simplify)": false,
            "(step t1 (cl (= (* y 0.1 10.0) y)) :rule prod_simplify)": false,
        }
    }
}

#[test]
fn test_nary_elim_rule() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun r () Bool)
            (declare-fun s () Bool)
            (declare-fun a () Int)
            (declare-fun b () Int)
            (declare-fun c () Int)
            (declare-fun d () Int)
        ",
        "Chainable operators" {
            "(step t1 (cl (= (= a b c d) (and (= a b) (= b c) (= c d)))) :rule nary_elim)": true,
            "(step t1 (cl (= (= a b) (and (= a b)))) :rule nary_elim)": true,
            "(step t1 (cl (= (= a b c) (and (= b c) (= a b)))) :rule nary_elim)": false,
            "(step t1 (cl (= (= a b c d) (and (= a b) (= c d)))) :rule nary_elim)": false,
        }
        "Left associative operators" {
            "(step t1 (cl (= (+ a b c d) (+ (+ (+ a b) c) d))) :rule nary_elim)": true,
            "(step t1 (cl (= (* a b) (* a b))) :rule nary_elim)": true,
            "(step t1 (cl (= (- a b c d) (- a (- b (- c d))))) :rule nary_elim)": false,
            "(step t1 (cl (= (+ a b c d) (+ (+ (+ d c) b) a))) :rule nary_elim)": false,
        }
        "Right associative operators" {
            "(step t1 (cl (= (=> p q r s) (=> p (=> q (=> r s))))) :rule nary_elim)": true,
            "(step t1 (cl (= (=> p q) (=> p q))) :rule nary_elim)": true,
            "(step t1 (cl (= (=> p q r s) (=> (=> (=> p q) r) s))) :rule nary_elim)": false,
        }
        "Clause term is not of the correct form" {
            "(step t1 (cl (= (or p q r s) (or (or (or p q) r) s))) :rule nary_elim)": false,
            "(step t1 (cl (= (- a) (- a))) :rule nary_elim)": false,
            "(step t1 (cl (= (=> p (=> q (=> r s))) (=> p q r s))) :rule nary_elim)": false,
        }
    }
}
