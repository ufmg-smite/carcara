use carcara::{checker::*, parser};

fn run_test(problem: &str, proof: &str, expected_result: bool) {
    let (problem, proof, _, mut pool) = parser::parse_instance(
        problem.as_bytes(),
        proof.as_bytes(),
        None,
        parser::Config::default(),
    )
    .unwrap();

    let got = ProofChecker::new(&mut pool, Config::new()).check(&problem, &proof);

    assert_eq!(got.is_ok(), expected_result);
}

#[test]
fn test_reached_empty_clause() {
    run_test("(declare-const x Int)", "(step t1 (cl) :rule hole)", true);
    run_test(
        "",
        "(anchor :step t0)
                  (step t0.t1 (cl) :rule hole)
                  (step t0 (cl false) :rule subproof)",
        false,
    );
    run_test(
        "",
        "(anchor :step t0)
                  (step t0.t1 (cl) :rule hole)
                  (step t0 (cl false) :rule subproof)
                  (step t1 (cl) :rule hole)",
        true,
    );
}
