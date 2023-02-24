use carcara::{
    benchmarking::{CollectResults, CsvBenchmarkResults, RunMeasurement},
    checker,
    parser::parse_instance,
    CarcaraOptions,
};
use crossbeam::queue::ArrayQueue;
use std::{
    fs::File,
    io::{self, BufReader},
    path::{Path, PathBuf},
    time::{Duration, Instant},
};

#[derive(Debug, Clone, Copy)]
struct JobDescriptor<'a> {
    problem_file: &'a Path,
    proof_file: &'a Path,
    run_index: usize,
}

fn run_job<T: CollectResults + Default>(
    results: &mut T,
    job: JobDescriptor,
    &CarcaraOptions {
        apply_function_defs,
        expand_lets,
        allow_int_real_subtyping,
        check_lia_using_cvc5,
        strict,
        skip_unknown_rules,
        num_cores: _,
    }: &CarcaraOptions,
    elaborate: bool,
) -> Result<(), carcara::Error> {
    let proof_file_name = job.proof_file.to_str().unwrap();

    let total = Instant::now();

    let parsing = Instant::now();
    let (prelude, proof, mut pool) = parse_instance(
        BufReader::new(File::open(job.problem_file)?),
        BufReader::new(File::open(job.proof_file)?),
        apply_function_defs,
        expand_lets,
        allow_int_real_subtyping,
    )?;
    let parsing = parsing.elapsed();

    let mut elaboration = Duration::ZERO;
    let mut deep_eq = Duration::ZERO;
    let mut assume = Duration::ZERO;
    let mut assume_core = Duration::ZERO;

    let config = checker::Config {
        strict,
        skip_unknown_rules,
        is_running_test: false,
        statistics: Some(checker::CheckerStatistics {
            file_name: proof_file_name,
            elaboration_time: &mut elaboration,
            deep_eq_time: &mut deep_eq,
            assume_time: &mut assume,
            assume_core_time: &mut assume_core,
            results,
        }),
        check_lia_using_cvc5,
    };
    let mut checker = checker::ProofChecker::new(&mut pool, config, prelude);

    let checking = Instant::now();

    // If any errors are encountered when checking a proof, we return from this function and do not
    // record the `RunMeasurement`. However, the data for each individual step is recorded as they
    // are checked, so any steps that were run before the error will be recorded.
    if elaborate {
        checker.check_and_elaborate(proof)?;
    } else {
        checker.check(&proof)?;
    }
    let checking = checking.elapsed();

    let total = total.elapsed();

    results.add_run_measurement(
        &(proof_file_name.to_string(), job.run_index),
        RunMeasurement {
            parsing,
            checking,
            elaboration,
            total,
            deep_eq,
            assume,
            assume_core,
        },
    );
    Ok(())
}

fn worker_thread<T: CollectResults + Default>(
    jobs_queue: &ArrayQueue<JobDescriptor>,
    options: &CarcaraOptions,
    elaborate: bool,
) -> T {
    let mut results = T::default();

    while let Some(job) = jobs_queue.pop() {
        let result = run_job(&mut results, job, options, elaborate);
        if let Err(e) = &result {
            log::error!("encountered error in file '{}'", job.proof_file.display());
            results.register_error(e);
        }
    }

    results
}

pub fn run_benchmark<T: CollectResults + Default + Send>(
    instances: &[(PathBuf, PathBuf)],
    num_runs: usize,
    num_threads: usize,
    options: &CarcaraOptions,
    elaborate: bool,
) -> T {
    const STACK_SIZE: usize = 128 * 1024 * 1024;

    let jobs_queue = ArrayQueue::new(instances.len() * num_runs);
    for run_index in 0..num_runs {
        for (problem, proof) in instances {
            let job = JobDescriptor {
                problem_file: problem,
                proof_file: proof,
                run_index,
            };
            jobs_queue.push(job).unwrap();
        }
    }

    crossbeam::scope(|s| {
        let jobs_queue = &jobs_queue; // So we don't try to move the queue into the thread closure

        // We of course need to `collect` here to ensure we spawn all threads before starting to
        // `join` them
        #[allow(clippy::needless_collect)]
        let workers: Vec<_> = (0..num_threads)
            .map(|_| {
                s.builder()
                    .stack_size(STACK_SIZE)
                    .spawn(move |_| worker_thread::<T>(jobs_queue, options, elaborate))
                    .unwrap()
            })
            .collect();

        workers
            .into_iter()
            .map(|w| w.join().unwrap())
            .reduce(T::combine)
            .unwrap()
    })
    .unwrap()
}

pub fn run_csv_benchmark(
    instances: &[(PathBuf, PathBuf)],
    num_runs: usize,
    num_threads: usize,
    options: &CarcaraOptions,
    elaborate: bool,
    runs_dest: &mut dyn io::Write,
    by_rule_dest: &mut dyn io::Write,
) -> io::Result<()> {
    let result: CsvBenchmarkResults =
        run_benchmark(instances, num_runs, num_threads, options, elaborate);
    println!(
        "{} errors encountered during benchmark",
        result.num_errors()
    );
    result.write_csv(runs_dest, by_rule_dest)
}
