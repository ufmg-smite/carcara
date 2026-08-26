use carcara::{
    ast::{Proof, ProofCommand, ProofNodeForest},
    checker::{self, *},
    elaborator, parser,
};

fn run_test(problem: &str, proof: &str, expected_result: bool) {
    let (problem, proof, rare_rules, mut pool) =
        parser::parse_instance(problem, proof, None, parser::Config::default()).unwrap();

    let got = ProofChecker::new(&mut pool, &rare_rules, Config::new()).check(&problem, &proof);

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

#[test]
fn test_elaborates_drup() {
    let problem = "
        (declare-const a Bool)
        (declare-const b Bool)
        (declare-const c Bool)
        (declare-const d Bool)
        (declare-const e Bool)
        (assert (or a c))
        (assert (or a (not c) d))
        (assert (or (not d) e))
        (assert (or (not d) (not e)))
        (assert (not a))
        (assert (not b))
    ";
    let proof = "
        (assume a0 (or a c))
        (assume a1 (or a (not c) d))
        (assume a2 (or (not d) e))
        (assume a3 (or (not d) (not e)))
        (assume a4 (not a))
        (assume a5 (not b))
        (step t0 (cl a c) :rule or :premises (a0))
        (step t1 (cl a (not c) d) :rule or :premises (a1))
        (step t2 (cl (not d) e) :rule or :premises (a2))
        (step t3 (cl (not d) (not e)) :rule or :premises (a3))
        (step t4 (cl a b) :rule drup :premises (t0 t1 t2 t3) :args ((cl a b)))
        (step t5 (cl) :rule drup :premises (t4 a4 a5) :args ((cl)))
    ";

    let (problem, proof, rare_rules, mut pool) =
        parser::parse_instance(problem, proof, None, parser::Config::default()).unwrap();
    ProofChecker::new(&mut pool, &rare_rules, Config::new())
        .check(&problem, &proof)
        .unwrap();

    let nodes = ProofNodeForest::from_commands(proof.commands);
    let elaborator_config = elaborator::Config {
        lia_solver: None,
        uncrowd_rotation: false,
        hole_solver: None,
        sat_ref_tools: None,
    };
    let elaborated = elaborator::Elaborator::new(&mut pool, &problem, elaborator_config)
        .elaborate(nodes, vec![elaborator::ElaborationPass::Local])
        .unwrap();
    let proof = Proof {
        commands: elaborated.into_commands(),
        ..proof
    };

    assert!(proof
        .iter()
        .all(|command| !matches!(command, ProofCommand::Step(step) if step.rule == "drup")));
    let checker_config = checker::Config {
        elaborated: true,
        ..checker::Config::new()
    };
    ProofChecker::new(&mut pool, &rare_rules, checker_config)
        .check(&problem, &proof)
        .unwrap();
}
