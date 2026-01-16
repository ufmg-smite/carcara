use crate::{
    ast::{node::ProofNodeForest, pool::PrimitivePool, Polyeq, TermPool},
    parser::tests::parse_terms,
};
use indexmap::IndexSet;

#[test]
fn test_free_vars() {
    fn run_tests(definitions: &str, cases: &[(&str, &[&str])]) {
        for &(term, expected) in cases {
            let mut pool = PrimitivePool::new();
            let [root] = parse_terms(&mut pool, definitions, [term]);
            let expected: IndexSet<_> = expected.iter().copied().collect();
            let set = pool.free_vars(&root);
            let got: IndexSet<_> = set.iter().map(|t| t.as_var().unwrap()).collect();

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
        ModReordering,
        AlphaEquiv,
        ModNary,
    }

    fn run_tests(definitions: &str, cases: &[(&str, &str)], test_type: TestType) {
        let mut pool = PrimitivePool::new();
        for (i, (a, b)) in cases.iter().enumerate() {
            let [a, b] = parse_terms(&mut pool, definitions, [a, b]);
            let mut comp = match test_type {
                TestType::ModReordering => Polyeq::new().mod_reordering(true),
                TestType::AlphaEquiv => Polyeq::new().mod_reordering(true).alpha_equiv(true),
                TestType::ModNary => Polyeq::new().mod_nary(true),
            };
            assert!(comp.eq(&a, &b), "test case #{i} failed: `{a}` != `{b}`");
        }
    }
    let definitions = "
            (declare-sort T 0)
            (declare-fun a () T)
            (declare-fun b () T)
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun r () Bool)
            (declare-fun s () Bool)
            (declare-fun t () Bool)
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
                "(let ((x 0)) (let ((y (+ x 2))) (let ((z (< x y))) (and z (= x y)))))",
                "(let ((z 0)) (let ((x (+ z 2))) (let ((y (< z x))) (and y (= z x)))))",
            ),
        ],
        TestType::AlphaEquiv,
    );
    run_tests(
        definitions,
        &[
            // Chainable
            ("(= p q r s)", "(and (= p q) (= q r) (= r s))"),
            ("(and (= p q) (= q r) (= r s))", "(= p q r s)"),
            // Left-associative
            ("(and (and (and p q) r) s)", "(and p q r s)"),
            ("(and p q r s)", "(and (and (and p q) r) s)"),
            ("(and (and (and p q) r) s t)", "(and (and (and p q r) s) t)"),
            // Right-associative
            ("(=> p (=> q (=> r s)))", "(=> p q r s)"),
            ("(=> p q r s)", "(=> p (=> q (=> r s)))"),
            ("(=> p q (=> r (=> s t)))", "(=> p (=> q (=> r s t)))"),
        ],
        TestType::ModNary,
    );
}

#[test]
fn test_node() {
    use crate::parser::tests::*;

    let original = "
        (assume h0 (= 0 0))
        (assume h1 (= 1 1))
        (assume h2 (= 2 2))
        (step t3 (cl true) :rule blah :premises (h0 h2))
        (step t4 (cl true) :rule blah)
        (anchor :step t5)
            (assume t5.h1 (= 3 3))
            (step t5.t2 (cl true) :rule blah :premises (t4))
            (step t5.t3 (cl true) :rule blah)
            (step t5.t4 (cl true) :rule blah)
            (step t5 (cl true) :rule blah :premises (t5.t2) :discharge (t5.h1))
        (step t6 (cl) :rule blah :premises (t3 t5))
    ";
    let mut pool = PrimitivePool::new();
    let original = parse_proof(&mut pool, original);

    let node = ProofNodeForest::from_commands(original.commands.clone());
    let got = node.into_commands();
    assert_eq!(original.commands, got);
}
