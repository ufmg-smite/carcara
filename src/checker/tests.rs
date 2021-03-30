#![cfg(test)]

use super::*;

fn run_tests(definitions: &str, cases: &[(&str, bool)]) {
    use crate::parser::parse_problem_proof;
    use std::io::Cursor;

    for (proof, expected) in cases {
        // This parses the definitions again for every case, which is not ideal
        let parsed = parse_problem_proof(Cursor::new(definitions), Cursor::new(proof)).unwrap();
        assert_eq!(*expected, ProofChecker::new(parsed).check())
    }
}

#[test]
fn test_or_rule() {
    let definitions = "
        (declare-fun p () Bool)
        (declare-fun q () Bool)
        (declare-fun r () Bool)
        (declare-fun s () Bool)
    ";

    let cases = [
        // Simple working examples
        (
            "(assume h1 (or p q))
            (step t2 (cl p q) :rule or :premises (h1))",
            true,
        ),
        (
            "(assume h1 (or p q r s))
            (step t2 (cl p q r s) :rule or :premises (h1))",
            true,
        ),
        // Number of premises != 1
        ("(step t1 (cl p q r) :rule or)", false),
        (
            "(assume h1 (or p q))
            (assume h2 (or q r))
            (step t3 (cl p q r) :rule or :premises (h1 h2))",
            false,
        ),
        // Premise clause has more than one term
        (
            "(assume h1 (or p (or q r)))
            (step t2 (cl p (or q r)) :rule or :premises (h1))
            (step t3 (cl p q) :rule or :premises (t2))",
            false,
        ),
        // Premise is not an "or" operation
        (
            "(assume h1 (and p q))
            (step t2 (cl p q) :rule or :premises (h1))",
            false,
        ),
        // Premise and clause contents are different
        (
            "(assume h1 (or p q))
            (step t2 (cl r s) :rule or :premises (h1))",
            false,
        ),
        (
            "(assume h1 (or p q r))
            (step t2 (cl p q) :rule or :premises (h1))",
            false,
        ),
        (
            "(assume h1 (or q p))
            (step t2 (cl p q) :rule or :premises (h1))",
            false,
        ),
    ];
    run_tests(definitions, &cases);
}

#[test]
fn test_eq_congruent_rule() {
    let definitions = "
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
    ";

    let cases = [
        // Simple working examples
        (
            "(step t1 (cl (not (= a b)) (= (f-1 a) (f-1 b))) :rule eq_congruent)",
            true,
        ),
        (
            "(step t1 (cl (not (= a x)) (not (= b y)) (not (= c z))
                        (= (f-3 a b c) (f-3 x y z))) :rule eq_congruent)
            ",
            true,
        ),
        // Clause term is not an inequality
        (
            "(step t1 (cl (not (= a x)) (= b y) (= (f a b) (f x y))) :rule eq_congruent)",
            false,
        ),
        // Final term is not an equality of applications
        (
            "(step t1 (cl (not (= a x)) (not (= b y)) (= (+ a b) (f x y))) :rule eq_congruent)",
            false,
        ),
        // Functions are not the same
        (
            "(step t1 (cl (not (= a x)) (not (= b y)) (= (f a b) (g x y))) :rule eq_congruent)",
            false,
        ),
        // Number of function arguments is not the same as the number of inequalities
        (
            "(step t1 (cl (not (= a x)) (not (= b y)) (= (f-3 a b c) (f-3 x y z)))
                :rule eq_congruent)",
            false,
        ),
        // Terms don't match
        (
            "(step t1 (cl (not (= a x)) (not (= b y)) (= (f x y) (f a b))) :rule eq_congruent)",
            false,
        ),
        (
            "(step t1 (cl (not (= a x)) (not (= b y)) (= (f b a) (f x y))) :rule eq_congruent)",
            false,
        ),
        (
            "(step t1 (cl (not (= a x)) (not (= b y)) (= (f a b) (f c z))) :rule eq_congruent)",
            false,
        ),
    ];
    run_tests(definitions, &cases);
}

#[test]
fn test_resolution_rule() {
    let definitions = "
        (declare-fun p () Bool)
        (declare-fun q () Bool)
        (declare-fun r () Bool)
    ";
    let cases = [
        // Simple working examples
        (
            "(assume h1 (not p))
            (assume h2 (or p q))
            (step t3 (cl p q) :rule or :premises (h2))
            (step t4 (cl q) :rule resolution :premises (h1 t3))",
            true,
        ),
        (
            "(assume h1 (not p))
            (assume h2 (not q))
            (assume h3 (not r))
            (assume h4 (or p q r))
            (step t5 (cl p q r) :rule or :premises (h4))
            (step t6 (cl) :rule resolution :premises (h1 h2 h3 t5))",
            true,
        ),
        (
            "(assume h1 (not p))
            (assume h2 q)
            (assume h3 (or p (not q)))
            (step t4 (cl p (not q)) :rule or :premises (h3))
            (step t5 (cl) :rule resolution :premises (h1 h2 t4))",
            true,
        ),
        // Missing term in final clause
        (
            "(assume h1 (not p))
            (assume h2 (or p q r))
            (step t3 (cl p q r) :rule or :premises (h2))
            (step t4 (cl q) :rule resolution :premises (h1 t3))",
            false,
        ),
        // Extra term in final clause
        (
            "(assume h1 (not p))
            (assume h2 (or p q r))
            (step t3 (cl p q r) :rule or :premises (h2))
            (step t4 (cl p q r) :rule resolution :premises (h1 t3))",
            false,
        ),
        // Term appears in final clause with wrong polarity
        (
            "(assume h1 (not p))
            (assume h2 (or p q r))
            (step t3 (cl p q r) :rule or :premises (h2))
            (step t4 (cl (not q) r) :rule resolution :premises (h1 t3))",
            false,
        ),
        // Duplicate term in final clause
        (
            "(assume h1 (not p))
            (assume h2 (or p q r))
            (step t3 (cl p q r) :rule or :premises (h2))
            (step t4 (cl q q r) :rule resolution :premises (h1 t3))",
            false,
        ),
        // Terms with leading negations
        (
            "(assume h1 (not p))
            (assume h2 (not (not p)))
            (assume h3 (not (not (not p))))
            (assume h4 (not (not (not (not p)))))
            (step t5 (cl) :rule resolution :premises (h1 h2))
            (step t6 (cl) :rule resolution :premises (h2 h3))
            (step t7 (cl (not p) (not (not (not p)))) :rule resolution :premises (h1 h3))
            (step t8 (cl (not p) (not (not (not (not p))))) :rule resolution :premises (h1 h4))",
            true,
        ),
    ];
    run_tests(definitions, &cases);
}
