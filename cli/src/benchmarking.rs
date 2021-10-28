use alethe_proof_checker::{benchmarking::BenchmarkResults, checker, parser::parse_instance};
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
) -> Result<BenchmarkResults, alethe_proof_checker::Error> {
    let mut result = BenchmarkResults::new();
    let proof_file_name = proof_file.to_str().unwrap();

    for i in 0..num_runs {
        let total_time = Instant::now();
        let parsing_time = Instant::now();
        let (proof, pool) = parse_instance(
            BufReader::new(File::open(problem_file)?),
            BufReader::new(File::open(proof_file)?),
        )?;
        let parsing_time = parsing_time.elapsed();

        let mut checking_time = Duration::ZERO;
        let config = checker::Config {
            skip_unknown_rules: false,
            is_running_test: false,
            statistics: Some(checker::CheckerStatistics {
                file_name: proof_file_name,
                checking_time: &mut checking_time,
                step_time: &mut result.step_time,
                step_time_by_file: &mut result.step_time_by_file,
                step_time_by_rule: &mut result.step_time_by_rule,
            }),
        };
        let _ = checker::ProofChecker::new(pool, config).check(&proof)?;
        let total_time = total_time.elapsed();

        let run_id = (proof_file_name.to_string(), i);
        result.parsing.add(&run_id, parsing_time);
        result.checking.add(&run_id, checking_time);
        result
            .parsing_checking
            .add(&run_id, parsing_time + checking_time);
        result.total.add(&run_id, total_time);
    }
    Ok(result)
}

pub fn run_benchmark(
    instances: &[(PathBuf, PathBuf)],
    num_runs: usize,
    num_jobs: usize,
) -> Result<BenchmarkResults, alethe_proof_checker::Error> {
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
            run_instance(instance, num_runs).unwrap_or_else(|e| {
                log::error!(
                    "encountered error in instance {}: {:?}",
                    instance.1.to_str().unwrap(),
                    e
                );
                BenchmarkResults::new()
            })
        })
        .reduce(BenchmarkResults::new, BenchmarkResults::combine);

    Ok(result)
}
