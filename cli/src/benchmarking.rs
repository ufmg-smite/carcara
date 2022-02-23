use alethe_proof_checker::{
    benchmarking::{CollectResults, OnlineBenchmarkResults, RunMeasurement},
    checker,
    parser::parse_instance,
};
use rayon::prelude::*;
use std::{
    fs::File,
    io::BufReader,
    path::PathBuf,
    time::{Duration, Instant},
};

fn run_instance(
    (problem_file, proof_file): &(PathBuf, PathBuf),
    num_runs: usize,
    apply_function_defs: bool,
    reconstruct: bool,
) -> Result<OnlineBenchmarkResults, alethe_proof_checker::Error> {
    let mut result = OnlineBenchmarkResults::new();
    let proof_file_name = proof_file.to_str().unwrap();

    for i in 0..num_runs {
        let total = Instant::now();

        let parsing = Instant::now();
        let (proof, mut pool) = parse_instance(
            BufReader::new(File::open(problem_file)?),
            BufReader::new(File::open(proof_file)?),
            apply_function_defs,
        )?;
        let parsing = parsing.elapsed();

        let mut reconstruction = Duration::ZERO;
        let mut deep_eq = Duration::ZERO;
        let mut assume = Duration::ZERO;

        let config = checker::Config {
            skip_unknown_rules: false,
            is_running_test: false,
            statistics: Some(checker::CheckerStatistics {
                file_name: proof_file_name,
                reconstruction_time: &mut reconstruction,
                deep_eq_time: &mut deep_eq,
                assume_time: &mut assume,
                results: &mut result,
            }),
        };
        let mut checker = checker::ProofChecker::new(&mut pool, config);

        let checking = Instant::now();
        if reconstruct {
            checker.check_and_reconstruct(proof)?;
        } else {
            checker.check(&proof)?;
        }
        let checking = checking.elapsed();

        let total = total.elapsed();

        result.add_run_measurement(
            &(proof_file_name.to_string(), i),
            RunMeasurement {
                parsing,
                checking,
                reconstruction,
                total,
                deep_eq,
                assume,
            },
        );
    }
    Ok(result)
}

pub fn run_benchmark(
    instances: &[(PathBuf, PathBuf)],
    num_runs: usize,
    num_jobs: usize,
    apply_function_defs: bool,
    reconstruct: bool,
) -> OnlineBenchmarkResults {
    // Configure rayon to use the right number of threads and to reserve enough stack space for
    // them
    rayon::ThreadPoolBuilder::new()
        .num_threads(num_jobs)
        .stack_size(64 * 1024 * 1024) // Some test examples need up to 64 MiB of stack size
        .build_global()
        .unwrap();

    let result = instances
        .par_iter()
        .map(|instance| {
            run_instance(instance, num_runs, apply_function_defs, reconstruct).unwrap_or_else(|e| {
                log::error!(
                    "encountered error in instance {}: {}",
                    instance.1.to_str().unwrap(),
                    e
                );
                OnlineBenchmarkResults::new()
            })
        })
        .reduce(OnlineBenchmarkResults::new, OnlineBenchmarkResults::combine);

    result
}
