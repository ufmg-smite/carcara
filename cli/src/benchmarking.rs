use alethe_proof_checker::{benchmarking::BenchmarkResults, checker, parser::parse_instance};
use std::{
    fs::File,
    io::BufReader,
    path::PathBuf,
    time::{Duration, Instant},
};

pub fn run_benchmark(
    instances: &[(PathBuf, PathBuf)],
    num_runs: usize,
) -> Result<BenchmarkResults, alethe_proof_checker::Error> {
    let mut result = BenchmarkResults::new();
    let mut finished_runs = 0;
    let total_runs = instances.len() * num_runs;

    for (problem_file, proof_file) in instances {
        let proof_file_name = proof_file.to_str().unwrap();

        for i in 0..num_runs {
            print!("[{} / {}]\r", finished_runs, total_runs);

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
                allow_test_rule: false,
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
            finished_runs += 1;
        }
    }
    Ok(result)
}
