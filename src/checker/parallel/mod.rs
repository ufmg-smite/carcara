use crate::{
    CarcaraResult, Status,
    ast::{Problem, Proof, pool::Pool, rare_rules::Rules},
    benchmarking::{CollectResults, OnlineBenchmarkResults},
    checker::{CheckerStatistics, Config},
};
use std::sync::Arc;

/// A parallel proof checker for Alethe.
#[allow(unused)]
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
        _problem: &Problem,
        _proof: &Proof,
        _num_threads: usize,
        _stack_size: usize,
        _stats: Option<&mut CheckerStatistics<CR>>,
    ) -> CarcaraResult<Status> {
        todo!()
    }
}
