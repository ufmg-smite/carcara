#![deny(clippy::disallowed_methods)]
#![deny(clippy::self_named_module_files)]
#![deny(clippy::undocumented_unsafe_blocks)]
#![warn(clippy::branches_sharing_code)]
#![warn(clippy::cloned_instead_of_copied)]
#![warn(clippy::copy_iterator)]
#![warn(clippy::dbg_macro)]
#![warn(clippy::doc_markdown)]
#![warn(clippy::equatable_if_let)]
#![warn(clippy::explicit_into_iter_loop)]
#![warn(clippy::explicit_iter_loop)]
#![warn(clippy::from_iter_instead_of_collect)]
#![warn(clippy::get_unwrap)]
#![warn(clippy::if_not_else)]
#![warn(clippy::implicit_clone)]
#![warn(clippy::inconsistent_struct_constructor)]
#![warn(clippy::index_refutable_slice)]
#![warn(clippy::inefficient_to_string)]
#![warn(clippy::items_after_statements)]
#![warn(clippy::large_types_passed_by_value)]
#![warn(clippy::manual_assert)]
#![warn(clippy::manual_ok_or)]
#![warn(clippy::map_unwrap_or)]
#![warn(clippy::match_wildcard_for_single_variants)]
#![warn(clippy::mixed_read_write_in_expression)]
#![warn(clippy::multiple_crate_versions)]
#![warn(clippy::redundant_closure_for_method_calls)]
#![warn(clippy::redundant_pub_crate)]
#![warn(clippy::semicolon_if_nothing_returned)]
#![warn(clippy::str_to_string)]
#![warn(clippy::string_to_string)]
#![warn(clippy::trivially_copy_pass_by_ref)]
#![warn(clippy::unnecessary_wraps)]
#![warn(clippy::unnested_or_patterns)]
#![warn(clippy::unused_self)]

#[macro_use]
pub mod ast;
pub mod benchmarking;
pub mod checker;
pub mod elaborator;
pub mod parser;
mod utils;

use crate::benchmarking::{CollectResults, OnlineBenchmarkResults, RunMeasurement};
use checker::{error::CheckerError, CheckerStatistics};
use parser::{ParserError, Position};
use std::io;
use std::time::{Duration, Instant};
use thiserror::Error;

pub type CarcaraResult<T> = Result<T, Error>;

/// The options that control how Carcara parses, checks and elaborates a proof.
#[derive(Default)]
pub struct CarcaraOptions {
    /// If `true`, Carcara will automatically expand function definitions introduced by `define-fun`
    /// commands in the SMT problem. If `false`, those `define-fun`s are instead interpreted as a
    /// function declaration and an `assert` command that defines the function as equal to its body
    /// (or to a lambda term, if it contains arguments). Note that function definitions in the proof
    /// are always expanded.
    pub apply_function_defs: bool,

    /// If `true`, Carcara will eliminate `let` bindings from terms during parsing. This is done by
    /// replacing any occurence of a variable bound in the `let` binding with its corresponding
    /// value.
    pub expand_lets: bool,

    /// If `true`, this relaxes the type checking rules in Carcara to allow `Int`-`Real` subtyping.
    /// That is, terms of sort `Int` will be allowed in arithmetic operations where a `Real` term
    /// was expected. Note that this only applies to predefined operators --- passing an `Int` term
    /// to a function that expects a `Real` will still be an error.
    pub allow_int_real_subtyping: bool,

    /// If `Some`, enables the checking/elaboration of `lia_generic` steps using an external solver.
    /// When checking a proof, this means calling the solver to solve the linear integer arithmetic
    /// problem, checking the proof, and discarding it. When elaborating, the proof will instead be
    /// inserted in the place of the `lia_generic` step. See [`LiaGenericOptions`] for more details.
    pub lia_options: Option<LiaGenericOptions>,

    /// Enables "strict" checking of some rules.
    ///
    /// Currently, if enabled, the following rules are affected:
    /// - `assume` and `refl`: implicit reordering of equalities is not allowed
    /// - `resolution` and `th_resolution`: the pivots must be provided as arguments
    ///
    /// In general, the invariant we aim for is that, if you are checking a proof that was
    /// elaborated by Carcara, you can safely enable this option (and possibly get a performance
    /// benefit).
    pub strict: bool,

    /// If `true`, Carcara will skip any rules that it does not recognize, and will consider them as
    /// holes. Normally, using an unknown rule is considered an error.
    pub skip_unknown_rules: bool,

    /// If `true`, Carcará will log the check and elaboration statistics of any
    /// `check` or `check_and_elaborate` run. If `false` no statistics are logged.
    pub stats: bool,
}

/// The options that control how `lia_generic` steps are checked/elaborated using an external
/// solver.
#[derive(Debug, Clone)]
pub struct LiaGenericOptions {
    /// The external solver path. The solver should be a binary that can read SMT-LIB from stdin and
    /// output an Alethe proof to stdout.
    pub solver: Box<str>,

    /// The arguments to pass to the solver.
    pub arguments: Vec<Box<str>>,
}

impl CarcaraOptions {
    /// Constructs a new `CarcaraOptions` with all options set to `false`.
    pub fn new() -> Self {
        Self::default()
    }
}

fn wrap_parser_error_message(e: &ParserError, pos: &Position) -> String {
    // For unclosed subproof errors, we don't print the position
    if matches!(e, ParserError::UnclosedSubproof(_)) {
        format!("parser error: {}", e)
    } else {
        format!("parser error: {} (on line {}, column {})", e, pos.0, pos.1)
    }
}

#[derive(Debug, Error)]
pub enum Error {
    #[error("IO error: {0}")]
    Io(#[from] io::Error),

    #[error("{}", wrap_parser_error_message(.0, .1))]
    Parser(ParserError, Position),

    #[error("checking failed on step '{step}' with rule '{rule}': {inner}")]
    Checker {
        inner: CheckerError,
        rule: String,
        step: String,
    },

    // While this is a kind of checking error, it does not happen in a specific step like all other
    // checker errors, so we model it as a different variant
    #[error("checker error: proof does not conclude empty clause")]
    DoesNotReachEmptyClause,
}

pub fn check<T: io::BufRead>(problem: T, proof: T, options: CarcaraOptions) -> Result<bool, Error> {
    let mut run_measures: RunMeasurement = RunMeasurement::default();

    // Parsing
    let total = Instant::now();
    let (prelude, proof, mut pool) = parser::parse_instance(
        problem,
        proof,
        options.apply_function_defs,
        options.expand_lets,
        options.allow_int_real_subtyping,
    )?;
    run_measures.parsing = total.elapsed();

    let config = checker::Config::new()
        .strict(options.strict)
        .skip_unknown_rules(options.skip_unknown_rules)
        .lia_options(options.lia_options);

    // Checking
    let checking = Instant::now();
    let mut checker = checker::ProofChecker::new(&mut pool, config, &prelude);
    if options.stats {
        let mut checker_stats = CheckerStatistics {
            file_name: "this",
            elaboration_time: Duration::ZERO,
            polyeq_time: Duration::ZERO,
            assume_time: Duration::ZERO,
            assume_core_time: Duration::ZERO,
            results: OnlineBenchmarkResults::new(),
        };
        let res = checker.check_with_stats(&proof, &mut checker_stats);

        run_measures.checking = checking.elapsed();
        run_measures.total = total.elapsed();

        checker_stats.results.add_run_measurement(
            &("this".to_owned(), 0),
            RunMeasurement {
                parsing: run_measures.parsing,
                checking: run_measures.checking,
                elaboration: checker_stats.elaboration_time,
                scheduling: run_measures.scheduling,
                total: run_measures.total,
                polyeq: checker_stats.polyeq_time,
                assume: checker_stats.assume_time,
                assume_core: checker_stats.assume_core_time,
            },
        );
        // Print the statistics
        checker_stats.results.print(false);

        res
    } else {
        checker.check(&proof)
    }
}

pub fn check_parallel<T: io::BufRead>(
    problem: T,
    proof: T,
    options: CarcaraOptions,
    num_threads: usize,
    stack_size: usize,
) -> Result<bool, Error> {
    use crate::checker::Scheduler;
    use std::sync::Arc;
    let mut run_measures: RunMeasurement = RunMeasurement::default();

    // Parsing
    let total = Instant::now();
    let (prelude, proof, pool) = parser::parse_instance(
        problem,
        proof,
        options.apply_function_defs,
        options.expand_lets,
        options.allow_int_real_subtyping,
    )?;
    run_measures.parsing = total.elapsed();

    let config = checker::Config::new()
        .strict(options.strict)
        .skip_unknown_rules(options.skip_unknown_rules)
        .lia_options(options.lia_options);

    // Checking
    let checking = Instant::now();
    let (scheduler, schedule_context_usage) = Scheduler::new(num_threads, &proof);
    run_measures.scheduling = checking.elapsed();
    let mut checker = checker::ParallelProofChecker::new(
        Arc::new(pool),
        config,
        &prelude,
        &schedule_context_usage,
        stack_size,
    );

    if options.stats {
        let mut checker_stats = CheckerStatistics {
            file_name: "this",
            elaboration_time: Duration::ZERO,
            polyeq_time: Duration::ZERO,
            assume_time: Duration::ZERO,
            assume_core_time: Duration::ZERO,
            results: OnlineBenchmarkResults::new(),
        };
        let res = checker.check_with_stats(&proof, &scheduler, &mut checker_stats);

        run_measures.checking = checking.elapsed();
        run_measures.total = total.elapsed();

        checker_stats.results.add_run_measurement(
            &("this".to_owned(), 0),
            RunMeasurement {
                parsing: run_measures.parsing,
                checking: run_measures.checking,
                elaboration: checker_stats.elaboration_time,
                scheduling: run_measures.scheduling,
                total: run_measures.total,
                polyeq: checker_stats.polyeq_time,
                assume: checker_stats.assume_time,
                assume_core: checker_stats.assume_core_time,
            },
        );
        // Print the statistics
        checker_stats.results.print(false);

        res
    } else {
        checker.check(&proof, &scheduler)
    }
}

pub fn check_and_elaborate<T: io::BufRead>(
    problem: T,
    proof: T,
    options: CarcaraOptions,
) -> Result<(bool, ast::Proof), Error> {
    let mut run_measures: RunMeasurement = RunMeasurement::default();

    // Parsing
    let total = Instant::now();
    let (prelude, proof, mut pool) = parser::parse_instance(
        problem,
        proof,
        options.apply_function_defs,
        options.expand_lets,
        options.allow_int_real_subtyping,
    )?;
    run_measures.parsing = total.elapsed();

    let config = checker::Config::new()
        .strict(options.strict)
        .skip_unknown_rules(options.skip_unknown_rules)
        .lia_options(options.lia_options);

    // Checking
    let checking = Instant::now();
    let mut checker = checker::ProofChecker::new(&mut pool, config, &prelude);
    if options.stats {
        let mut checker_stats = CheckerStatistics {
            file_name: "this",
            elaboration_time: Duration::ZERO,
            polyeq_time: Duration::ZERO,
            assume_time: Duration::ZERO,
            assume_core_time: Duration::ZERO,
            results: OnlineBenchmarkResults::new(),
        };

        let res = checker.check_and_elaborate_with_stats(proof, &mut checker_stats);
        run_measures.checking = checking.elapsed();
        run_measures.total = total.elapsed();

        checker_stats.results.add_run_measurement(
            &("this".to_owned(), 0),
            RunMeasurement {
                parsing: run_measures.parsing,
                checking: run_measures.checking,
                elaboration: checker_stats.elaboration_time,
                scheduling: run_measures.scheduling,
                total: run_measures.total,
                polyeq: checker_stats.polyeq_time,
                assume: checker_stats.assume_time,
                assume_core: checker_stats.assume_core_time,
            },
        );
        // Print the statistics
        checker_stats.results.print(false);

        res
    } else {
        checker.check_and_elaborate(proof)
    }
}
