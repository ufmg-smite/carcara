use super::*;
use crate::parser::tests::{parse_term, parse_term_with_definitions};

#[test]
fn test_subterms_no_duplicates() {
    fn run_tests(cases: &[&str]) {
        fn no_duplicates(slice: &[&Term]) -> bool {
            let mut seen = HashSet::new();
            slice.iter().all(|&t| seen.insert(t))
        }
        for s in cases {
            let term = parse_term(s);
            assert!(no_duplicates(&term.subterms()))
        }
    }
    run_tests(&[
        "(= 1 1)",
        "(ite false false false)",
        "(- (ite (not true) 2 3) (ite (not true) 2 3))",
        "(= (= 1 2) (not (= 1 2)))",
        "(+ (* 1 2) (- 2 (* 1 2)))",
    ]);
}

#[test]
fn test_subterms() {
    fn run_tests(definitions: &str, cases: &[&[&str]]) {
        for c in cases {
            let expected = c.iter().cloned();

            let root = parse_term_with_definitions(definitions, c[0]);
            let subterms = root.subterms();
            let as_strings: Vec<_> = subterms.iter().map(|&t| format!("{:?}", t)).collect();
            let got = as_strings.iter().map(String::as_str);

            assert!(expected.eq(got))
        }
    }
    run_tests(
        "(declare-fun f (Int Int) Int)
            (declare-fun a () Int)
            (declare-fun b () Int)
            (declare-fun c () Int)",
        &[
            &["(= 0 1)", "0", "1"],
            &["(f a b)", "f", "a", "b"],
            &[
                "(f (f a b) (f b c))",
                "f",
                "(f a b)",
                "a",
                "b",
                "(f b c)",
                "c",
            ],
            &[
                "(= (= 1 2) (not (= 1 2)))",
                "(= 1 2)",
                "1",
                "2",
                "(not (= 1 2))",
            ],
            &[
                "(ite (not false) (+ 2 (f 0 1)) (- (f a b) (f 0 1)))",
                "(not false)",
                "false",
                "(+ 2 (f 0 1))",
                "2",
                "(f 0 1)",
                "f",
                "0",
                "1",
                "(- (f a b) (f 0 1))",
                "(f a b)",
                "a",
                "b",
            ],
        ],
    )
}

#[test]
fn test_deep_eq() {
    fn run_tests(definitions: &str, cases: &[(&str, &str)], is_mod_reordering: bool) {
        for (a, b) in cases {
            let (a, b) = (
                parse_term_with_definitions(definitions, a),
                parse_term_with_definitions(definitions, b),
            );
            if is_mod_reordering {
                assert!(DeepEq::eq_modulo_reordering(&a, &b))
            } else {
                assert!(DeepEq::eq(&a, &b))
            }
        }
    }
    let definitions = "
            (declare-sort T 0)
            (declare-fun a () T)
            (declare-fun b () T)
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun x () Int)
            (declare-fun y () Int)
        ";
    run_tests(
        definitions,
        &[
            ("a", "a"),
            ("(+ x y)", "(+ x y)"),
            (
                "(ite (and (not p) q) (* x y) (- 0 y))",
                "(ite (and (not p) q) (* x y) (- 0 y))",
            ),
        ],
        false,
    );
    run_tests(
        definitions,
        &[
            ("(= a b)", "(= b a)"),
            ("(= p (= p (= p q)))", "(= p (= (= p q) p))"),
            (
                "(ite (= a b) (= x (+ x y)) (and p (not (= x y))))",
                "(ite (= b a) (= (+ x y) x) (and p (not (= y x))))",
            ),
        ],
        true,
    );
}
