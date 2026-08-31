use crate::{
    CarcaraResult, Error, Status,
    ast::{Problem, Proof, pool::Pool, rare_rules::Rules},
    benchmarking::{CollectResults, OnlineBenchmarkResults},
    checker::{Checker, CheckerStatistics, Config},
};
use crossbeam_queue::ArrayQueue;
use std::{
    sync::{
        Arc,
        atomic::{AtomicBool, Ordering},
    },
    thread,
    time::Duration,
};

/// A parallel proof checker for Alethe.
///
/// This checker splits the proof's top-level commands among a number of worker threads, such that
/// commands inside the same subproof are checked by the same worker thread. Each thread has a local
/// `Pool`, with the global pool as a parent, and a local context. The work is split dinamically
/// using a work queue.
pub struct ParallelChecker<'c> {
    global_pool: Arc<Pool>,
    config: Config,
    rare_rules: &'c Rules,
}

impl<'c> ParallelChecker<'c> {
    /// Constructs a new `ParallelChecker` with a given pool, set of rare rules, and `Config`.
    pub fn new(pool: Arc<Pool>, rare_rules: &'c Rules, config: Config) -> Self {
        Self {
            global_pool: pool,
            config,
            rare_rules,
        }
    }

    /// Checks that `proof` is a valid proof for the given problem.
    ///
    /// Returns `Ok` if the proof is valid, with the proof status.
    pub fn check(
        &mut self,
        problem: &Problem,
        proof: &Proof,
        num_threads: usize,
        stack_size: usize,
    ) -> CarcaraResult<Status> {
        let null_stats = None::<&mut CheckerStatistics<OnlineBenchmarkResults>>;
        self.check_impl(problem, proof, num_threads, stack_size, null_stats)
    }

    /// Checks that `proof` is a valid proof for the given problem, collecting benchmarking
    /// statistics into `stats`.
    pub fn check_with_stats<CR: CollectResults + Send + Default>(
        &mut self,
        problem: &Problem,
        proof: &Proof,
        num_threads: usize,
        stack_size: usize,
        stats: &mut CheckerStatistics<CR>,
    ) -> CarcaraResult<Status> {
        self.check_impl(problem, proof, num_threads, stack_size, Some(stats))
    }

    fn check_impl<CR: CollectResults + Send + Default>(
        &mut self,
        problem: &Problem,
        proof: &Proof,
        num_threads: usize,
        stack_size: usize,
        stats: Option<&mut CheckerStatistics<CR>>,
    ) -> CarcaraResult<Status> {
        let num_threads = num_threads.min(proof.commands.len()).max(1);
        let work_queue = ArrayQueue::new(proof.commands.len());
        for pos in 0..proof.commands.len() {
            work_queue.push(pos).unwrap();
        }

        // Used to tell other threads to abort prematurely when a worker thread finds an error
        let abort = &AtomicBool::new(false);

        let combined_result = thread::scope(|s| {
            let work_queue = &work_queue;
            let use_stats = stats.is_some();
            let global_pool = &self.global_pool;
            let rare_rules = self.rare_rules;
            let config = &self.config;

            let workers: Vec<_> = (0..num_threads)
                .map(|i| {
                    thread::Builder::new()
                        .name(format!("worker-{i}"))
                        .stack_size(stack_size)
                        .spawn_scoped(s, move || {
                            let mut local_pool = Pool::with_parent(global_pool.clone());
                            let local_checker =
                                Checker::new(&mut local_pool, rare_rules, config.clone());
                            worker_thread::<CR>(
                                local_checker,
                                problem,
                                proof,
                                work_queue,
                                abort,
                                use_stats,
                            )
                        })
                        .unwrap()
                })
                .collect();

            workers
                .into_iter()
                .map(|w| w.join().unwrap())
                .reduce(|a, b| Ok(WorkerResult::combine(a?, b?)))
                .unwrap()
        })?;

        let combined_stats = combined_result.stats;
        if let Some(stats) = stats
            && let Some(combined_stats) = combined_stats
        {
            let file_name = stats.file_name;
            *stats = combined_stats;
            stats.file_name = file_name;
        }
        if combined_result.reached_empty_clause {
            Ok(combined_result.status)
        } else {
            Err(Error::DoesNotReachEmptyClause { file: proof.filename.clone() })
        }
    }
}

struct WorkerResult<R: CollectResults + Send + Default> {
    status: Status,
    reached_empty_clause: bool,
    stats: Option<CheckerStatistics<'static, R>>,
}

impl<R: CollectResults + Send + Default> WorkerResult<R> {
    fn combine(a: Self, b: Self) -> Self {
        Self {
            status: if a.status == Status::Holey || b.status == Status::Holey {
                Status::Holey
            } else {
                Status::Valid
            },
            reached_empty_clause: a.reached_empty_clause || b.reached_empty_clause,
            stats: combine_stats(a.stats, b.stats),
        }
    }
}

fn combine_stats<R: CollectResults + Send + Default>(
    a: Option<CheckerStatistics<'static, R>>,
    b: Option<CheckerStatistics<'static, R>>,
) -> Option<CheckerStatistics<'static, R>> {
    let mut a = a?;
    let b = b?;
    a.polyeq_time += b.polyeq_time;
    a.assume_time += b.assume_time;
    a.assume_core_time += b.assume_core_time;
    a.results = CollectResults::combine(a.results, b.results);
    Some(a)
}

fn worker_thread<R: CollectResults + Send + Default>(
    mut local_checker: Checker,
    problem: &Problem,
    proof: &Proof,
    work_queue: &ArrayQueue<usize>,
    abort: &AtomicBool,
    collect_stats: bool,
) -> CarcaraResult<WorkerResult<R>> {
    let mut local_stats = if collect_stats {
        Some(CheckerStatistics {
            file_name: "",
            polyeq_time: Duration::ZERO,
            assume_time: Duration::ZERO,
            assume_core_time: Duration::ZERO,
            results: R::default(),
        })
    } else {
        None
    };
    while let Some(index) = work_queue.pop() {
        if abort.load(Ordering::Relaxed) {
            break;
        }
        let result = local_checker.check_commands(
            problem,
            &proof.filename,
            &proof.commands[..index + 1],
            index,
            local_stats.as_mut(),
        );
        if result.is_err() {
            abort.store(true, Ordering::Relaxed);
            result?;
        }
    }

    Ok(WorkerResult {
        status: if local_checker.is_holey {
            Status::Holey
        } else {
            Status::Valid
        },
        reached_empty_clause: local_checker.reached_empty_clause,
        stats: local_stats,
    })
}
