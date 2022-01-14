use crate::parser::tests::{parse_term, TestParser};
use ahash::AHashSet;

#[test]
fn test_subterms_no_duplicates() {
    fn run_tests(cases: &[&str]) {
        for s in cases {
            let term = parse_term(s);
            let mut seen = AHashSet::new();
            assert!(term.subterms().all(|t| seen.insert(t)));
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
            let expected = c.iter().copied();

            let root = TestParser::new(definitions).parse_term(c[0]);
            let subterms = root.subterms();
            let as_strings: Vec<_> = subterms.map(|t| format!("{}", t)).collect();
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
            &["(exists ((x Int)) false)", "false"],
            &["(forall ((p Bool)) (= 0 1))", "(= 0 1)", "0", "1"],
            &["(choice ((y Real)) (= 0 1))", "(= 0 1)", "0", "1"],
            &[
                "(let ((p false) (q (= 0 1))) true)",
                "false",
                "(= 0 1)",
                "0",
                "1",
                "true",
            ],
            &["(lambda ((x Int) (y Int)) (+ 1 2))", "(+ 1 2)", "1", "2"],
        ],
    )
}

#[test]
fn test_free_vars() {
    fn run_tests(definitions: &str, cases: &[(&str, &[&str])]) {
        for &(term, expected) in cases {
            let mut parser = TestParser::new(definitions);
            let root = parser.parse_term(term);
            let expected = expected
                .iter()
                .map(|&s| s.to_string())
                .collect::<AHashSet<_>>();
            let mut pool = parser.term_pool();

            assert_eq!(&expected, pool.free_vars(&root))
        }
    }
    run_tests(
        "(declare-fun p () Bool)
        (declare-fun q () Bool)
        (declare-fun r () Bool)
        (declare-fun a () Int)
        (declare-fun b () Int)",
        &[
            ("(and p q r)", &["p", "q", "r"]),
            ("(= a b)", &["a", "b"]),
            ("(= b b)", &["b"]),
            ("(forall ((a Int) (b Int)) (= a b))", &[]),
            ("(forall ((a Int)) (= a b))", &["b"]),
            ("(forall ((a Int)) (forall ((b Int)) (= a b)))", &[]),
            ("(and (forall ((a Int)) (= a 0)) (= a 0))", &["a"]),
            ("(and (= a 0) (forall ((a Int)) (= a 0)))", &["a"]),
        ],
    )
}

#[test]
fn test_deep_eq() {
    enum TestType {
        Normal,
        ModReordering,
        AlphaEquiv,
    }

    fn run_tests(definitions: &str, cases: &[(&str, &str)], test_type: TestType) {
        for (a, b) in cases {
            let mut parser = TestParser::new(definitions);
            let (a, b) = (parser.parse_term(a), parser.parse_term(b));
            match test_type {
                TestType::Normal => assert_deep_eq!(&a, &b),
                TestType::ModReordering => assert_deep_eq_modulo_reordering!(&a, &b),
                TestType::AlphaEquiv => {
                    assert!(super::deep_eq::are_alpha_equivalent(&a, &b))
                }
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
        TestType::Normal,
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
        TestType::ModReordering,
    );
    run_tests(
        definitions,
        &[
            ("(= a b)", "(= b a)"),
            ("(forall ((p Bool)) p)", "(forall ((q Bool)) q)"),
            (
                "(forall ((x Int) (y Int)) (< x y))",
                "(forall ((y Int) (x Int)) (< y x))",
            ),
            (
                "(forall ((p Bool)) (forall ((q Bool)) p))",
                "(forall ((q Bool)) (forall ((p Bool)) q))",
            ),
            (
                "(choice ((x Int)) (forall ((y Int)) (exists ((z Int)) (= x y z))))",
                "(choice ((a Int)) (forall ((b Int)) (exists ((c Int)) (= a b c))))",
            ),
            (
                "(let ((x 0) (y (+ x 2)) (z (< x y))) (and z (= x y)))",
                "(let ((z 0) (x (+ z 2)) (y (< z x))) (and y (= z x)))",
            ),
        ],
        TestType::AlphaEquiv,
    );
}
