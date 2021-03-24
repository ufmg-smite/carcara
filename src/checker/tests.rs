#![cfg(test)]

use super::*;

use crate::parser::tests::*;

fn parse_and_check(input: &str) -> bool {
    ProofChecker::new(parse_proof(input)).check()
}

#[test]
fn test_match_op() {
    let true_term = parse_term("true");
    let false_term = parse_term("false");
    let term = parse_term("(= (= (not false) (= true false)) (not true))");
    assert_eq!(
        match_op!((= (= (not a) (= b c)) (not d)) = &term),
        Some(((&false_term, (&true_term, &false_term)), &true_term)),
    );
}

#[test]
fn test_or_rule() {
    // Simple working examples
    let proof = "
        (declare-fun p () Bool)
        (declare-fun q () Bool)
        (assume h1 (or p q))
        (step t2 (cl p q) :rule or :premises (h1))
    ";
    assert_eq!(parse_and_check(proof), true);

    let proof = "
        (declare-fun p () Bool)
        (declare-fun q () Bool)
        (declare-fun r () Bool)
        (declare-fun s () Bool)
        (assume h1 (or p q r s))
        (step t2 (cl p q r s) :rule or :premises (h1))
    ";
    assert_eq!(parse_and_check(proof), true);

    // Number of premises != 1
    let proof = "
        (declare-fun p () Bool)
        (declare-fun q () Bool)
        (declare-fun r () Bool)
        (assume h1 (or p q))
        (assume h2 (or q r))
        (step t2 (cl p q r) :rule or :premises (h1 h2))
    ";
    assert_eq!(parse_and_check(proof), false);

    // Premise clause has more than one term
    let proof = "
        (declare-fun p () Bool)
        (declare-fun q () Bool)
        (declare-fun r () Bool)
        (assume h1 (or p (or q r)))
        (step t1 (cl p (or q r)) :rule or :premises (h1))
        (step t2 (cl p q) :rule or :premises (t1))
    ";
    assert_eq!(parse_and_check(proof), false);

    // Premise is not an "or" operation
    let proof = "
        (declare-fun p () Bool)
        (declare-fun q () Bool)
        (assume h1 (and p q))
        (step t2 (cl p q) :rule or :premises (h1))
    ";
    assert_eq!(parse_and_check(proof), false);

    // Premise and clause contents are different
    let proof = "
        (declare-fun p () Bool)
        (declare-fun q () Bool)
        (declare-fun r () Bool)
        (declare-fun s () Bool)
        (assume h1 (or p q))
        (step t2 (cl r s) :rule or :premises (h1))
    ";
    assert_eq!(parse_and_check(proof), false);

    let proof = "
        (declare-fun p () Bool)
        (declare-fun q () Bool)
        (declare-fun r () Bool)
        (assume h1 (or p q r))
        (step t2 (cl p q) :rule or :premises (h1))
    ";
    assert_eq!(parse_and_check(proof), false);

    let proof = "
        (declare-fun p () Bool)
        (declare-fun q () Bool)
        (assume h1 (or q p))
        (step t2 (cl p q) :rule or :premises (h1))
    ";
    assert_eq!(parse_and_check(proof), false);
}

#[test]
fn test_eq_congruent_rule() {
    // Simple working examples
    let proof = "
        (declare-fun a () Int) (declare-fun b () Int)
        (declare-fun f (Int) Int)
        (step t1 (cl (not (= a b)) (= (f a) (f b))) :rule eq_congruent)
    ";
    assert_eq!(parse_and_check(proof), true);

    let proof = "
        (declare-fun a () Int) (declare-fun b () Int) (declare-fun c () Int)
        (declare-fun x () Int) (declare-fun y () Int) (declare-fun z () Int)
        (declare-fun f (Int Int Int) Int)
        (step t1 (cl (not (= a x)) (not (= b y)) (not (= c z))
                     (= (f a b c) (f x y z))) :rule eq_congruent)
    ";
    assert_eq!(parse_and_check(proof), true);

    // Clause term is not an inequality
    let proof = "
        (declare-fun a () Int) (declare-fun b () Int)
        (declare-fun x () Int) (declare-fun y () Int)
        (declare-fun f (Int Int) Int)
        (step t1 (cl (not (= a x)) (= b y) (= (f a b) (f x y))) :rule eq_congruent)
    ";
    assert_eq!(parse_and_check(proof), false);

    // Final term is not an equality of applications
    let proof = "
        (declare-fun a () Int) (declare-fun b () Int)
        (declare-fun x () Int) (declare-fun y () Int)
        (declare-fun f (Int Int) Int)
        (step t1 (cl (not (= a x)) (not (= b y)) (= (+ a b) (f x y))) :rule eq_congruent)
    ";
    assert_eq!(parse_and_check(proof), false);

    // Functions are not the same
    let proof = "
        (declare-fun a () Int) (declare-fun b () Int)
        (declare-fun x () Int) (declare-fun y () Int)
        (declare-fun f (Int Int) Int)
        (declare-fun g (Int Int) Int)
        (step t1 (cl (not (= a x)) (not (= b y)) (= (f a b) (g x y))) :rule eq_congruent)
    ";
    assert_eq!(parse_and_check(proof), false);

    // Number of function arguments is not the same as the number of inequalities
    let proof = "
        (declare-fun a () Int) (declare-fun b () Int) (declare-fun c () Int)
        (declare-fun x () Int) (declare-fun y () Int) (declare-fun z () Int)
        (declare-fun f (Int Int Int) Int)
        (step t1 (cl (not (= a x)) (not (= b y)) (= (f a b c) (f x y z))) :rule eq_congruent)
    ";
    assert_eq!(parse_and_check(proof), false);

    // Terms don't match
    let proof = "
        (declare-fun a () Int) (declare-fun b () Int)
        (declare-fun x () Int) (declare-fun y () Int)
        (declare-fun f (Int Int) Int)
        (step t1 (cl (not (= a x)) (not (= b y)) (= (f x y) (f a b))) :rule eq_congruent)
    ";
    assert_eq!(parse_and_check(proof), false);

    let proof = "
        (declare-fun a () Int) (declare-fun b () Int)
        (declare-fun x () Int) (declare-fun y () Int)
        (declare-fun f (Int Int) Int)
        (step t1 (cl (not (= a x)) (not (= b y)) (= (f b a) (f x y))) :rule eq_congruent)
    ";
    assert_eq!(parse_and_check(proof), false);

    let proof = "
        (declare-fun a () Int) (declare-fun b () Int)
        (declare-fun x () Int) (declare-fun y () Int)
        (declare-fun i () Int) (declare-fun j () Int)
        (declare-fun f (Int Int) Int)
        (step t1 (cl (not (= a x)) (not (= b y)) (= (f a b) (f i j))) :rule eq_congruent)
    ";
    assert_eq!(parse_and_check(proof), false);
}

#[test]
fn test_resolution_rule() {
    // Simple working examples
    let proof = "
        (declare-fun p () Bool)
        (declare-fun q () Bool)
        (assume h1 (not p))
        (assume h2 (or p q))
        (step t3 (cl p q) :rule or :premises (h2))
        (step t5 (cl q) :rule resolution :premises (h1 t3))
    ";
    assert_eq!(parse_and_check(proof), true);

    let proof = "
        (declare-fun p () Bool)
        (declare-fun q () Bool)
        (declare-fun r () Bool)
        (assume h1 (not p))
        (assume h2 (not q))
        (assume h3 (not r))
        (assume h4 (or p q r))
        (step t5 (cl p q r) :rule or :premises (h4))
        (step t6 (cl) :rule resolution :premises (h1 h2 h3 t5))
    ";
    assert_eq!(parse_and_check(proof), true);

    let proof = "
        (declare-fun p () Bool)
        (declare-fun q () Bool)
        (declare-fun r () Bool)
        (assume h1 (not p))
        (assume h2 q)
        (assume h3 (or p (not q)))
        (step t4 (cl p (not q)) :rule or :premises (h3))
        (step t5 (cl) :rule resolution :premises (h1 h2 t4))
    ";
    assert_eq!(parse_and_check(proof), true);

    // Missing term in final clause
    let proof = "
        (declare-fun p () Bool)
        (declare-fun q () Bool)
        (declare-fun r () Bool)
        (assume h1 (not p))
        (assume h2 (or p q r))
        (step t3 (cl p q r) :rule or :premises (h2))
        (step t4 (cl q) :rule resolution :premises (h1 t3))
    ";
    assert_eq!(parse_and_check(proof), false);

    // Extra term in final clause
    let proof = "
        (declare-fun p () Bool)
        (declare-fun q () Bool)
        (declare-fun r () Bool)
        (assume h1 (not p))
        (assume h2 (or p q r))
        (step t3 (cl p q r) :rule or :premises (h2))
        (step t4 (cl p q r) :rule resolution :premises (h1 t3))
    ";
    assert_eq!(parse_and_check(proof), false);

    // Term appears in final clause with wrong polarity
    let proof = "
        (declare-fun p () Bool)
        (declare-fun q () Bool)
        (declare-fun r () Bool)
        (assume h1 (not p))
        (assume h2 (or p q r))
        (step t3 (cl p q r) :rule or :premises (h2))
        (step t4 (cl (not q) r) :rule resolution :premises (h1 t3))
    ";
    assert_eq!(parse_and_check(proof), false);

    // Duplicate term in final clause
    let proof = "
        (declare-fun p () Bool)
        (declare-fun q () Bool)
        (declare-fun r () Bool)
        (assume h1 (not p))
        (assume h2 (or p q r))
        (step t3 (cl p q r) :rule or :premises (h2))
        (step t4 (cl q q r) :rule resolution :premises (h1 t3))
    ";
    assert_eq!(parse_and_check(proof), false);
}
