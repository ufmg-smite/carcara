use carcara::{benchmarking::CollectStats, checker, elaborator, parser};
use crossbeam_queue::ArrayQueue;
use std::{
    num::NonZero,
    path::{Path, PathBuf},
    thread,
    time::Instant,
};

#[derive(Debug, Clone, Copy)]
struct JobDescriptor<'a> {
    problem_file: &'a Path,
    proof_file: &'a Path,
    run_index: usize,
}

#[derive(Debug, Default)]
pub struct BenchResult<S> {
    pub num_errors: usize,
    pub is_holey: bool,
    pub stats: S,
}

impl<S: CollectStats> BenchResult<S> {
    fn combine(a: Self, b: Self) -> Self {
        Self {
            num_errors: a.num_errors + b.num_errors,
            is_holey: a.is_holey || b.is_holey,
            stats: S::combine(a.stats, b.stats),
        }
    }

    pub fn print_status(&self) {
        println!("{} errors encountered during benchmark", self.num_errors);
        if self.num_errors > 0 {
            println!("invalid");
        } else if self.is_holey {
            println!("holey");
        } else {
            println!("valid");
        }
    }
}

fn run_job<S: CollectStats>(
    results: &mut S,
    job: JobDescriptor,
    parser_config: parser::Config,
    checker_config: checker::Config,
    elaborator_config: Option<(elaborator::Config, Vec<elaborator::ElaborationPass>)>,
) -> Result<carcara::Status, carcara::Error> {
    let mut run = carcara::benchmarking::RunStats::new();

    // Parsing
    let input = carcara::Input {
        problem: parser::Source::file(job.problem_file)?,
        proof: parser::Source::file(job.proof_file)?,
        rare_rules: None,
    };
    let parsing_time = Instant::now();
    let (problem, proof, rules, mut pool) = parser::parse(input, parser_config)?;
    run.parsing = parsing_time.elapsed();

    // Checking
    let mut checker = checker::Checker::new(&mut pool, &rules, checker_config);
    let (checking_status, checking) = checker.check_with_stats(&problem, &proof, results)?;
    run.checking = checking;

    // Elaborating
    if let Some((elab_config, pipeline)) = elaborator_config {
        let node = carcara::ast::ProofNodeForest::from_commands(proof.commands);
        let (_, times) = elaborator::Elaborator::new(&mut pool, &problem, elab_config)
            .elaborate_with_stats(node, &proof.filename, pipeline)?;
        run.elaboration = times;
    }

    results.add_run_measurement(&(job.proof_file.to_path_buf(), job.run_index), run);
    Ok(checking_status)
}

fn worker_thread<S: CollectStats + Default>(
    jobs_queue: &ArrayQueue<JobDescriptor>,
    parser_config: parser::Config,
    checker_config: checker::Config,
    elaborator_config: Option<(elaborator::Config, Vec<elaborator::ElaborationPass>)>,
) -> BenchResult<S> {
    let mut res = BenchResult {
        num_errors: 0,
        is_holey: false,
        stats: S::default(),
    };

    while let Some(job) = jobs_queue.pop() {
        let result = run_job(
            &mut res.stats,
            job,
            parser_config,
            checker_config.clone(),
            elaborator_config.clone(),
        );
        match result {
            Ok(carcara::Status::Holey) => res.is_holey = true,
            Err(_) => {
                log::error!("encountered error in file '{}'", job.proof_file.display());
                res.num_errors += 1;
            }
            _ => (),
        }
    }

    res
}

pub fn run_benchmark<S: CollectStats + Default + Send>(
    instances: &[(PathBuf, PathBuf)],
    num_runs: NonZero<usize>,
    num_jobs: NonZero<usize>,
    parser_config: parser::Config,
    checker_config: checker::Config,
    elaborator_config: Option<(elaborator::Config, Vec<elaborator::ElaborationPass>)>,
) -> BenchResult<S> {
    const STACK_SIZE: usize = 128 * 1024 * 1024;

    let jobs_queue = ArrayQueue::new(instances.len() * num_runs.get());
    for run_index in 0..num_runs.get() {
        for (problem, proof) in instances {
            let job = JobDescriptor {
                problem_file: problem,
                proof_file: proof,
                run_index,
            };
            jobs_queue.push(job).unwrap();
        }
    }

    thread::scope(|s| {
        let jobs_queue = &jobs_queue; // So we don't try to move the queue into the thread closure

        // We of course need to `collect` here to ensure we spawn all threads before starting to
        // `join` them
        #[allow(clippy::needless_collect)]
        let workers: Vec<_> = (0..num_jobs.get())
            .map(|_| {
                let checker_config = checker_config.clone();
                let elaborator_config = elaborator_config.clone();
                thread::Builder::new()
                    .stack_size(STACK_SIZE)
                    .spawn_scoped(s, move || {
                        worker_thread(jobs_queue, parser_config, checker_config, elaborator_config)
                    })
                    .unwrap()
            })
            .collect();

        workers
            .into_iter()
            .map(|w| w.join().unwrap())
            .reduce(BenchResult::combine)
            .unwrap()
    })
}
