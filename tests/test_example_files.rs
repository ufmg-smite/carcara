use carcara::*;
use std::{
    io::Write,
    path::{Path, PathBuf},
    process::Command,
};

type TestConfig = (parser::Config, checker::Config);

fn run_parallel_checker_test(
    problem_path: &Path,
    proof_path: &Path,
    config: TestConfig,
    num_threads: usize,
) -> CarcaraResult<()> {
    use std::sync::Arc;

    let (problem, proof, rare_rules, pool) = parser::parse_instance(
        parser::Source::file(problem_path, &mut String::new())?,
        parser::Source::file(proof_path, &mut String::new())?,
        None,
        config.0,
    )?;

    let (scheduler, schedule_context_usage) = checker::Scheduler::new(num_threads, &proof);
    let mut checker = checker::ParallelProofChecker::new(
        Arc::new(pool),
        config.1,
        &problem.prelude,
        &schedule_context_usage,
        128 * 1024 * 1024,
        rare_rules,
    );
    checker.check(&problem, &proof, &scheduler)?;
    Ok(())
}

fn run_test(problem_path: &Path, proof_path: &Path, config: TestConfig) -> CarcaraResult<()> {
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

/// Directory of the Lambdapi package that holds the Alethe library. Generated proofs are written
/// there so that their `require open lambdapi.Alethe` resolves through `lambdapi.pkg`.
const LAMBDAPI_PACKAGE_DIR: &str = "lambdapi-stdlib";

/// Elaborates the proof, translates it to Lambdapi and checks the result with the `lambdapi`
/// binary. The generated `.lp` file is kept next to the library when the check fails, so it can
/// be inspected by hand.
fn run_translation(
    problem_path: &Path,
    proof_path: &Path,
    config: TestConfig,
) -> CarcaraResult<()> {
    use translation::lambdapi::printer::PrettyPrint;

    let (problem, proof, _, mut pool) = parser::parse_instance(
        parser::Source::file(problem_path, &mut String::new())?,
        parser::Source::file(proof_path, &mut String::new())?,
        None,
        config.0,
    )?;

    let elab_config = elaborator::Config::new().uncrowd_rotation(true);
    let node = ast::ProofNodeForest::from_commands(proof.commands.clone());
    let elaborated_node = elaborator::Elaborator::new(&mut pool, &problem, elab_config)
        .elaborate_with_default_pipeline(node, &proof.filename)?;
    let elaborated = ast::Proof {
        constant_definitions: proof.constant_definitions.clone(),
        commands: elaborated_node.into_commands(),
        filename: proof.filename.clone(),
    };

    let translation_config = translation::lambdapi::Config { no_elab: false, why3: false };
    let lambdapi_proof = translation::lambdapi::produce_lambdapi_proof(
        problem.prelude,
        elaborated,
        pool,
        translation_config,
    )
    .unwrap_or_else(|e| {
        panic!(
            "translation of \"{}\" failed: {:?}",
            proof_path.display(),
            e
        )
    });

    // Lambdapi derives the module name from the file name, so it must be a plain identifier.
    let module_name: String = proof_path
        .file_name()
        .unwrap()
        .to_str()
        .unwrap()
        .chars()
        .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
        .collect();
    let lp_path = PathBuf::from(LAMBDAPI_PACKAGE_DIR).join(format!("{}.lp", module_name));

    {
        let file = std::fs::File::create(&lp_path).expect("cannot create Lambdapi file");
        let mut writer = std::io::BufWriter::new(file);
        lambdapi_proof
            .render(&mut writer)
            .expect("cannot write Lambdapi proof");
        writer.flush().expect("cannot flush Lambdapi proof");
    }

    let status = Command::new("lambdapi")
        .args(["check", "-v", "0", "-w", "--timeout=300"])
        .arg(&lp_path)
        .status()
        .expect("failed to run `lambdapi`; is it on PATH?");

    assert!(
        status.success(),
        "`lambdapi check` failed on \"{}\" (kept for inspection)",
        lp_path.display()
    );
    std::fs::remove_file(&lp_path).expect("cannot remove Lambdapi file");

    Ok(())
}

fn test_file<F>(proof_path: &str, runner: F)
where
    F: FnOnce(&Path, &Path, TestConfig) -> CarcaraResult<()>,
{
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
        while !matches!(
            path.extension().unwrap().to_str().unwrap(),
            "smt" | "smt2" | "smt_in"
        ) {
            path.set_extension("");
        }
        path
    };
    if let Err(e) = runner(&problem_path, &proof_path, config) {
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
    test_file(proof_path, run_test)
}

#[test_generator::from_dir(path = "benchmarks/full", ignore)]
#[allow(dead_code)]
fn full(proof_path: &str) {
    test_file(proof_path, run_test)
}

/// TLAPS proof obligations (cvc5 Alethe proofs), translated to Lambdapi and checked with
/// `lambdapi`. Requires `lambdapi` on PATH and the Lambdapi library built (`make -C
/// lambdapi-stdlib`).
#[test_generator::from_dir(path = "benchmarks/tlaps")]
#[allow(dead_code)]
fn tlaps(proof_path: &str) {
    test_file(proof_path, run_translation)
}
