//!  Carcara is an independent proof checker and elaborator for SMT proofs in the [Alethe
//! format](https://verit.gitlabpages.uliege.be/alethe/specification.pdf), with a focus on
//! performance and usability. It can efficiently check Alethe proofs even in the presence of
//! coarse-grained steps, and reports detailed error messages in the case that the proof is invalid.
//! Besides checking, Carcara is capable of _elaborating_ proofs, by adding omitted detail and
//! breaking down hard-to-check steps into multiple simpler steps.
//!
//! This project was developed in the SMITE research group, at Universidade Federal de
//! Minas Gerais (UFMG). A research paper describing Carcara has been [published at TACAS
//! 2023](https://link.springer.com/chapter/10.1007/978-3-031-30823-9_19).

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
#![warn(clippy::redundant_closure_for_method_calls)]
#![warn(clippy::redundant_pub_crate)]
#![warn(clippy::semicolon_if_nothing_returned)]
#![warn(clippy::str_to_string)]
#![warn(clippy::trivially_copy_pass_by_ref)]
#![warn(clippy::unnecessary_wraps)]
#![warn(clippy::unnested_or_patterns)]
#![warn(clippy::unused_self)]

pub mod ast;
pub mod automata;
pub mod benchmarking;
pub mod checker;
mod drup;
pub mod elaborator;
pub mod external;
pub mod parser;
mod rare;
mod resolution;
pub mod slice;
pub mod translation;
mod utils;

use benchmarking::{CollectResults, OnlineBenchmarkResults, RunMeasurement};
use checker::{CheckerStatistics, error::CheckerError};
use elaborator::ElaborationPass;
use elaborator::error::ElaborationError;
use parser::{ParserError, Position};
use std::io;
use std::path::PathBuf;
use std::time::{Duration, Instant};
use thiserror::Error;

/// A type alias for a `Result` whose error type is a Carcara error.
pub type CarcaraResult<T> = Result<T, Error>;

/// Options for validating trusted theory-rewrite holes using RARE and egglog.
pub use checker::RunEgglogOptions;

/// The result of a checking a proof, if no errors were found. Can be either "valid" or "holey"
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Status {
    Valid,
    Holey,
}

impl std::fmt::Display for Status {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            Status::Valid => "valid",
            Status::Holey => "holey",
        };
        write!(f, "{}", s)
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

/// The error type for Carcara operations.
#[derive(Debug, Error)]
pub enum Error {
    /// An IO error.
    #[error("IO error: {inner}")]
    Io {
        /// The underlying IO error.
        inner: io::Error,

        /// The file where the error occurred.
        file: PathBuf,
    },

    /// A parsing error, with the position in the input where it occurred and the source file path.
    #[error("{}", wrap_parser_error_message(.0, .1))]
    Parser(ParserError, Position, PathBuf),

    /// An error while checking a proof, indicating the step where it occurred.
    #[error("checking failed on step '{step}' with rule '{rule}': {inner}")]
    Checker {
        /// The underlying checking error.
        inner: Box<CheckerError>,

        /// The rule that was being checked when the error occurred.
        rule: Box<str>,

        /// The id of the step in which the error occurred.
        step: Box<str>,

        /// The proof file path.
        file: PathBuf,
    },

    // While this is a kind of checking error, it does not happen in a specific step like all other
    // checker errors, so we model it as a different variant
    /// The proof being checked did not conclude the empty clause.
    #[error("checker error: proof does not conclude empty clause")]
    DoesNotReachEmptyClause {
        /// The proof file path.
        file: PathBuf,
    },

    /// An error while elaborating a proof, indicating the step where it occurred.
    #[error("elaboration failed on step '{step}' with rule '{rule}': {inner}")]
    Elaborator {
        /// The underlying elaboration error.
        inner: Box<ElaborationError>,

        /// The rule that was being elaborated when the error occurred.
        rule: Box<str>,

        /// The ID of the step in which the error occurred.
        step: Box<str>,

        /// The elaboration pass where the error occurred.
        pass: ElaborationPass,

        /// The proof file path.
        file: PathBuf,
    },
}

/// Parses and checks an Alethe proof against an SMT-LIB problem.
///
/// The `Result` returned is `Ok` if the proof did not have errors, and contains the proof status.
/// The `problem` and `proof` strings are the SMT-LIB problem and the Alethe proof to check. If
/// `rules` is `Some`, it should contain a set of Rare rewrite rules to be used when checking.
///
/// If `collect_stats` is true, benchmarking statistics will be collected and printed.
pub fn check<'s>(
    problem: parser::Source<'s>,
    proof: parser::Source<'s>,
    rules: Option<parser::Source<'s>>,
    parser_config: parser::Config,
    checker_config: checker::Config,
    collect_stats: bool,
) -> Result<Status, Error> {
    let mut run_measures: RunMeasurement = RunMeasurement::default();

    // Parsing
    let total = Instant::now();
    let (problem, proof, rules, mut pool) =
        parser::parse_instance(problem, proof, rules, parser_config)?;
    run_measures.parsing = total.elapsed();

    // Checking
    let checking = Instant::now();
    let mut checker = checker::ProofChecker::new(&mut pool, &rules, checker_config);
    if collect_stats {
        let mut checker_stats = CheckerStatistics {
            file_name: "this",
            polyeq_time: Duration::ZERO,
            assume_time: Duration::ZERO,
            assume_core_time: Duration::ZERO,
            results: OnlineBenchmarkResults::new(),
        };
        let res = checker.check_with_stats(&problem, &proof, &mut checker_stats);

        run_measures.checking = checking.elapsed();
        run_measures.total = total.elapsed();

        checker_stats.results.add_run_measurement(
            &("this".to_owned(), 0),
            RunMeasurement {
                parsing: run_measures.parsing,
                checking: run_measures.checking,
                elaboration: run_measures.elaboration,
                scheduling: run_measures.scheduling,
                total: run_measures.total,
                polyeq: checker_stats.polyeq_time,
                assume: checker_stats.assume_time,
                assume_core: checker_stats.assume_core_time,
                elaboration_pipeline: Vec::new(),
            },
        );
        // Print the statistics
        checker_stats.results.print(false);

        res
    } else {
        checker.check(&problem, &proof)
    }
}

/// Parses and checks an Alethe proof against an SMT-LIB problem, checking steps in parallel.
///
/// This is similar to [`check`], but the proof steps are checked concurrently using `num_threads`
/// threads. The `stack_size` argument sets the stack size of the worker threads.
#[allow(clippy::too_many_arguments)]
pub fn check_parallel<'s>(
    problem: parser::Source<'s>,
    proof: parser::Source<'s>,
    rules: Option<parser::Source<'s>>,
    parser_config: parser::Config,
    checker_config: checker::Config,
    collect_stats: bool,
    num_threads: usize,
    stack_size: usize,
) -> Result<Status, Error> {
    use crate::checker::Scheduler;
    use std::sync::Arc;
    let mut run_measures: RunMeasurement = RunMeasurement::default();

    let total = Instant::now();
    let (problem, proof, rules, pool) =
        parser::parse_instance(problem, proof, rules, parser_config)?;
    run_measures.parsing = total.elapsed();

    // Checking
    let checking = Instant::now();
    let (scheduler, schedule_context_usage) = Scheduler::new(num_threads, &proof);
    run_measures.scheduling = checking.elapsed();
    let mut checker = checker::ParallelProofChecker::new(
        Arc::new(pool),
        checker_config,
        &problem.prelude,
        &schedule_context_usage,
        stack_size,
        rules,
    );

    if collect_stats {
        let mut checker_stats = CheckerStatistics {
            file_name: "this",
            polyeq_time: Duration::ZERO,
            assume_time: Duration::ZERO,
            assume_core_time: Duration::ZERO,
            results: OnlineBenchmarkResults::new(),
        };
        let res = checker.check_with_stats(&problem, &proof, &scheduler, &mut checker_stats);

        run_measures.checking = checking.elapsed();
        run_measures.total = total.elapsed();

        checker_stats.results.add_run_measurement(
            &("this".to_owned(), 0),
            RunMeasurement {
                parsing: run_measures.parsing,
                checking: run_measures.checking,
                elaboration: run_measures.elaboration,
                scheduling: run_measures.scheduling,
                total: run_measures.total,
                polyeq: checker_stats.polyeq_time,
                assume: checker_stats.assume_time,
                assume_core: checker_stats.assume_core_time,
                elaboration_pipeline: Vec::new(),
            },
        );
        // Print the statistics
        checker_stats.results.print(false);

        res
    } else {
        checker.check(&problem, &proof, &scheduler)
    }
}

/// Parses, checks, and elaborates an Alethe proof against an SMT-LIB problem.
///
/// This is similar to [`check`], but additionally elaborates the proof after checking it. The
/// `pipeline` argument determines the elaboration passes to apply, in order. On success, this
/// returns the proof holiness status, the parsed problem, the elaborated proof, and the term pool
/// used.
#[allow(clippy::too_many_arguments)]
pub fn check_and_elaborate<'s>(
    problem: parser::Source<'s>,
    proof: parser::Source<'s>,
    rules: Option<parser::Source<'s>>,
    parser_config: parser::Config,
    checker_config: checker::Config,
    elaborator_config: elaborator::Config,
    pipeline: Vec<elaborator::ElaborationPass>,
    collect_stats: bool,
) -> Result<(Status, ast::Problem, ast::Proof, ast::pool::PrimitivePool), Error> {
    let mut run: RunMeasurement = RunMeasurement::default();

    // Parsing (Complete rare rules)
    let total = Instant::now();
    let (problem, proof, rules, mut pool) =
        parser::parse_instance(problem, proof, rules, parser_config)?;
    run.parsing = total.elapsed();

    let mut stats = OnlineBenchmarkResults::new();

    // Checking
    let checking = Instant::now();
    let mut checker = checker::ProofChecker::new(&mut pool, &rules, checker_config);
    let checking_status = if collect_stats {
        let mut checker_stats = CheckerStatistics {
            file_name: "this",
            polyeq_time: Duration::ZERO,
            assume_time: Duration::ZERO,
            assume_core_time: Duration::ZERO,
            results: std::mem::take(&mut stats),
        };

        let res = checker.check_with_stats(&problem, &proof, &mut checker_stats);
        run.checking = checking.elapsed();
        run.polyeq = checker_stats.polyeq_time;
        run.assume = checker_stats.assume_time;
        run.assume_core = checker_stats.assume_core_time;

        stats = checker_stats.results;
        res
    } else {
        checker.check(&problem, &proof)
    }?;

    // Elaborating
    let elaboration = Instant::now();

    let node = ast::ProofNodeForest::from_commands(proof.commands);
    let (elaborated, pipeline_durations) = elaborator::Elaborator::new(
        &mut pool,
        &problem,
        elaborator_config,
    )
    .elaborate_with_stats(node, &proof.filename, pipeline)?;
    let elaborated = ast::Proof {
        commands: elaborated.into_commands(),
        ..proof
    };

    if collect_stats {
        run.elaboration = elaboration.elapsed();
        run.total = total.elapsed();
        run.elaboration_pipeline = pipeline_durations;

        stats.add_run_measurement(&("this".to_owned(), 0), run);

        stats.print(false);
    }

    Ok((checking_status, problem, elaborated, pool))
}

/// Generates an SMT-LIB problem for each `lia_generic` step in a proof.
///
/// Each returned pair contains the ID of a `lia_generic` step and an SMT-LIB problem that
/// corresponds to the negation of that step's conclusion clause.
pub fn generate_lia_smt_instances<'s>(
    problem: parser::Source<'s>,
    proof: parser::Source<'s>,
    rules: Option<parser::Source<'s>>,
    config: parser::Config,
    use_sharing: bool,
) -> Result<Vec<(String, String)>, Error> {
    use std::fmt::Write;
    let (problem, proof, _, mut pool) = parser::parse_instance(problem, proof, rules, config)?;

    let mut iter = proof.iter();
    let mut result = Vec::new();
    while let Some(command) = iter.next() {
        if let ast::ProofCommand::Step(step) = command
            && step.rule == "lia_generic"
        {
            if iter.depth() > 0 {
                log::error!("generating SMT instance for step inside subproof is not supported");
                continue;
            }

            let mut problem_string = String::new();
            write!(&mut problem_string, "{}", problem.prelude).unwrap();

            let mut bytes = Vec::new();
            ast::printer::write_clause_smt_problem(
                &mut pool,
                &problem.prelude,
                &mut bytes,
                &step.clause,
                use_sharing,
            )
            .unwrap();
            write!(&mut problem_string, "{}", String::from_utf8(bytes).unwrap()).unwrap();

            writeln!(&mut problem_string, "(check-sat)").unwrap();
            writeln!(&mut problem_string, "(exit)").unwrap();

            result.push((step.id.clone(), problem_string));
        }
    }
    Ok(result)
}
