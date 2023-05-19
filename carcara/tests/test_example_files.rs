use carcara::{benchmarking::OnlineBenchmarkResults, checker::CheckerStatistics, *};
use std::{
    fs, io,
    path::{Path, PathBuf},
};

fn run_test(problem_path: &Path, proof_path: &Path) -> CarcaraResult<()> {
    use checker::Config;

    let (prelude, proof, mut pool) = parser::parse_instance(
        io::BufReader::new(fs::File::open(problem_path)?),
        io::BufReader::new(fs::File::open(proof_path)?),
        true,
        false,
        false,
    )?;

    // First, we check the proof normally
    checker::ProofChecker::new(&mut pool, Config::new(), prelude.clone()).check(
        &proof,
        &mut None::<CheckerStatistics<OnlineBenchmarkResults>>,
    )?;

    // Then, we check it while elaborating the proof
    let mut checker = checker::ProofChecker::new(&mut pool, Config::new(), prelude.clone());
    let (_, elaborated) = checker.check_and_elaborate(
        proof,
        &mut None::<CheckerStatistics<OnlineBenchmarkResults>>,
    )?;

    // After that, we check the elaborated proof normally, to make sure it is valid
    checker::ProofChecker::new(&mut pool, Config::new().strict(true), prelude.clone()).check(
        &elaborated,
        &mut None::<CheckerStatistics<OnlineBenchmarkResults>>,
    )?;

    // Finally, we elaborate the already elaborated proof, to make sure the elaboration step is
    // idempotent
    let mut checker = checker::ProofChecker::new(&mut pool, Config::new().strict(true), prelude);
    let (_, elaborated_twice) = checker.check_and_elaborate(
        elaborated.clone(),
        &mut None::<CheckerStatistics<OnlineBenchmarkResults>>,
    )?;
    assert!(
        elaborated.commands == elaborated_twice.commands,
        "elaboration was not idempotent!"
    );

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
        // Error messages are sometimes pretty big, so printing them fully can be very bad for
        // performance
        let short_message = match e {
            Error::Io(_) => "IO error".to_owned(),
            Error::Parser(_, (line, column)) => format!("parser error at {}:{}", line, column),
            Error::Checker { rule, step, .. } => format!("checker error at '{}' ({})", step, rule),
            Error::DoesNotReachEmptyClause => format!("{}", e), // This one is already pretty short
        };
        panic!(
            "\"{}\" returned error: {}",
            &proof_path.to_str().unwrap(),
            short_message
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
