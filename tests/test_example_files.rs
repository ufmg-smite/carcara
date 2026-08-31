use carcara::*;
use std::path::{Path, PathBuf};

fn run_parallel_checker_test(
    _problem_path: &Path,
    _proof_path: &Path,
    _config: (parser::Config, checker::Config),
    _num_threads: usize,
) -> CarcaraResult<()> {
    Ok(()) // TODO
}

fn run_test(
    problem_path: &Path,
    proof_path: &Path,
    config: (parser::Config, checker::Config),
) -> CarcaraResult<()> {
    let (problem, proof, rare_rules, mut pool) = parser::parse_instance(
        parser::Source::file(problem_path, &mut String::new())?,
        parser::Source::file(proof_path, &mut String::new())?,
        None,
        config.0,
    )?;

    // First, we check the proof normally
    checker::ProofChecker::new(&mut pool, &rare_rules, config.1.clone()).check(&problem, &proof)?;

    // Then we elaborate it
    let elab_config = elaborator::Config::new().uncrowd_rotation(true);
    let node = ast::ProofNodeForest::from_commands(proof.commands.clone());
    let elaborated_node = elaborator::Elaborator::new(&mut pool, &problem, elab_config.clone())
        .elaborate_with_default_pipeline(node, &proof.filename)?;
    let elaborated = ast::Proof {
        constant_definitions: proof.constant_definitions.clone(),
        commands: elaborated_node.into_commands(),
        filename: "<elaborated proof>".into(),
    };

    // After that, we check the elaborated proof to make sure it is valid
    checker::ProofChecker::new(&mut pool, &rare_rules, config.1.clone().elaborated(true))
        .check(&problem, &elaborated)?;

    // Finally, we elaborate the already elaborated proof, to make sure the elaboration is
    // idempotent
    let elaborated_twice = elaborator::Elaborator::new(&mut pool, &problem, elab_config)
        .elaborate_with_default_pipeline(elaborated_node, &elaborated.filename)?;
    assert!(
        elaborated.commands == elaborated_twice.into_commands(),
        "elaboration was not idempotent!"
    );

    // We also test the parallel checker, with different values for the number of threads
    run_parallel_checker_test(problem_path, proof_path, config.clone(), 1)?;
    run_parallel_checker_test(problem_path, proof_path, config.clone(), 4)?;
    run_parallel_checker_test(problem_path, proof_path, config, 16)?;

    Ok(())
}

fn test_file(proof_path: &str) {
    let config = if proof_path.ends_with(".cvc5.alethe") {
        let parsing = parser::Config::new().expand_lets(true);
        let checking = checker::Config::new().allowed_rules(["all_simplify", "rare_rewrite"]);
        (parsing, checking)
    } else {
        (parser::Config::new(), checker::Config::new())
    };

    let proof_path = PathBuf::from(proof_path);
    let problem_path = {
        let mut path = proof_path.clone();
        while path.extension().unwrap() != "smt_in" && path.extension().unwrap() != "smt2" {
            path.set_extension("");
        }
        path
    };
    if let Err(e) = run_test(&problem_path, &proof_path, config) {
        // Error messages are sometimes pretty big, so printing them fully can be very bad for
        // performance
        let short_message = match e {
            Error::Io { .. } => "IO error".to_owned(),
            Error::Parser(_, (line, column), _) => format!("parser error at {}:{}", line, column),
            Error::Checker { rule, step, .. } => format!("checker error at '{}' ({})", step, rule),
            Error::DoesNotReachEmptyClause { .. } => format!("{}", e), // This one is already pretty short
            Error::Elaborator { rule, step, .. } => {
                format!("elaborator error at '{}' ({})", step, rule)
            }
        };
        panic!(
            "\"{}\" returned error: {}",
            &proof_path.to_str().unwrap(),
            short_message
        )
    }
}

#[test_generator::from_dir(path = "benchmarks/small")]
#[allow(dead_code)]
fn small(proof_path: &str) {
    test_file(proof_path)
}

#[test_generator::from_dir(path = "benchmarks/full", ignore)]
#[allow(dead_code)]
fn full(proof_path: &str) {
    test_file(proof_path)
}
