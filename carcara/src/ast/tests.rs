use crate::{
    ast::{TPool, TermPool},
    parser::tests::parse_terms,
};
use ahash::AHashSet;

#[test]
fn test_free_vars() {
    fn run_tests(definitions: &str, cases: &[(&str, &[&str])]) {
        for &(term, expected) in cases {
            let mut pool = TermPool::new();
            let [root] = parse_terms(&mut pool, definitions, [term]);
            let expected: AHashSet<_> = expected.iter().copied().collect();
            let got: AHashSet<_> = pool
                .free_vars(&root)
                .iter()
                .map(|t| t.as_var().unwrap())
                .collect();

            assert_eq!(expected, got);
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
    );
}

#[test]
fn test_polyeq() {
    enum TestType {
        Polyeq,
        AlphaEquiv,
    }

    fn run_tests(definitions: &str, cases: &[(&str, &str)], test_type: TestType) {
        let mut pool = TermPool::new();
        for (a, b) in cases {
            let [a, b] = parse_terms(&mut pool, definitions, [a, b]);
            let mut time = std::time::Duration::ZERO;
            match test_type {
                TestType::Polyeq => {
                    assert!(super::polyeq::polyeq(&a, &b, &mut time));
                }
                TestType::AlphaEquiv => {
                    assert!(super::polyeq::alpha_equiv(&a, &b, &mut time));
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
            ("(= a b)", "(= b a)"),
            ("(= p (= p (= p q)))", "(= p (= (= p q) p))"),
            (
                "(ite (= a b) (= x (+ x y)) (and p (not (= x y))))",
                "(ite (= b a) (= (+ x y) x) (and p (not (= y x))))",
            ),
        ],
        TestType::Polyeq,
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
