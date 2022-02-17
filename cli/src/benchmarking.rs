use alethe_proof_checker::{
    benchmarking::{Metrics, OnlineBenchmarkResults},
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
        let total_time = Instant::now();

        let parsing_time = Instant::now();
        let (proof, mut pool) = parse_instance(
            BufReader::new(File::open(problem_file)?),
            BufReader::new(File::open(proof_file)?),
            apply_function_defs,
        )?;
        let parsing_time = parsing_time.elapsed();

        let mut reconstruction_time = Duration::ZERO;
        let mut deep_eq_time = Duration::ZERO;
        let mut assume_time = Duration::ZERO;

        let config = checker::Config {
            skip_unknown_rules: false,
            is_running_test: false,
            statistics: Some(checker::CheckerStatistics {
                file_name: proof_file_name,
                reconstruction_time: &mut reconstruction_time,
                deep_eq_time: &mut deep_eq_time,
                assume_time: &mut assume_time,
                results: &mut result,
            }),
        };
        let mut checker = checker::ProofChecker::new(&mut pool, config);

        let checking_time = Instant::now();
        if reconstruct {
            checker.check_and_reconstruct(proof)?;
        } else {
            checker.check(&proof)?;
        }
        let checking_time = checking_time.elapsed();

        let total_time = total_time.elapsed();

        let run_id = (proof_file_name.to_string(), i);
        result.parsing.add_sample(&run_id, parsing_time);
        result.checking.add_sample(&run_id, checking_time);
        result
            .reconstructing
            .add_sample(&run_id, reconstruction_time);
        result
            .total_accounted_for
            .add_sample(&run_id, parsing_time + checking_time);
        result.total.add_sample(&run_id, total_time);

        result.deep_eq_time.add_sample(&run_id, deep_eq_time);
        result.assume_time.add_sample(&run_id, assume_time);

        let deep_eq_ratio = deep_eq_time.as_secs_f64() / checking_time.as_secs_f64();
        let assume_ratio = assume_time.as_secs_f64() / checking_time.as_secs_f64();
        result.deep_eq_time_ratio.add_sample(&run_id, deep_eq_ratio);
        result.assume_time_ratio.add_sample(&run_id, assume_ratio);
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
