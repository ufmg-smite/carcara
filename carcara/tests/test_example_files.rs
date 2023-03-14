use carcara::*;
use std::{
    fs, io,
    path::{Path, PathBuf},
};

fn get_truncated_message(e: &Error) -> String {
    const ERROR_MESSAGE_LIMIT: usize = 350;
    const TRUNCATION_MESSAGE: &str = "... (long message truncated)";
    const TRUNCATION_LEN: usize = TRUNCATION_MESSAGE.as_bytes().len();

    let mut error_message = format!("{}", e);

    if error_message.len() > ERROR_MESSAGE_LIMIT + TRUNCATION_LEN {
        error_message.truncate(ERROR_MESSAGE_LIMIT);
        error_message.push_str(TRUNCATION_MESSAGE);
    }
    error_message
}

fn run_test(problem_path: &Path, proof_path: &Path) -> CarcaraResult<()> {
    fn test_config<'a>() -> checker::Config<'a> {
        checker::Config {
            strict: false,
            skip_unknown_rules: true,
            is_running_test: false,
            statistics: None,
            check_lia_using_cvc5: false,
        }
    }

    let (prelude, proof, mut pool) = parser::parse_instance(
        io::BufReader::new(fs::File::open(problem_path)?),
        io::BufReader::new(fs::File::open(proof_path)?),
        true,
        false,
        false,
    )?;

    // First, we check the proof normally
    checker::ProofChecker::new(&mut pool, test_config(), prelude.clone()).check(&proof)?;

    // Then, we check it while elaborating the proof
    let mut checker = checker::ProofChecker::new(&mut pool, test_config(), prelude.clone());
    let elaborated = checker.check_and_elaborate(proof)?;

    // After that, we check the elaborated proof normally, to make sure it is valid
    checker::ProofChecker::new(&mut pool, test_config(), prelude.clone()).check(&elaborated)?;

    // Finally, we elaborate the already elaborated proof, to make sure the elaboration step is
    // idempotent
    let mut checker = checker::ProofChecker::new(&mut pool, test_config(), prelude);
    let elaborated_twice = checker.check_and_elaborate(elaborated.clone())?;
    assert_eq!(elaborated.commands, elaborated_twice.commands);

    Ok(())
}

fn test_file(proof_path: &str) {
    let proof_path = PathBuf::from(format!("../{}", proof_path));
    let problem_path = {
        let mut path = proof_path.clone();
        while path.extension().unwrap() != "smt_in" && path.extension().unwrap() != "smt2" {
            path.set_extension("");
        }
        path
    };
    if let Err(e) = run_test(&problem_path, &proof_path) {
        panic!(
            "\"{}\" returned error: {}",
            &proof_path.to_str().unwrap(),
            get_truncated_message(&e),
        )
    }
}

#[test_generator::from_dir("benchmarks/small")]
#[allow(dead_code)]
fn small(proof_path: &str) {
    test_file(proof_path)
}

#[test_generator::from_dir("benchmarks/full", ignore)]
#[allow(dead_code)]
fn full(proof_path: &str) {
    test_file(proof_path)
}
