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

use benchmarking::{CollectStats, RunStats};
use checker::error::CheckerError;
use elaborator::{ElaborationPass, error::ElaborationError};
use parser::{ParserError, Position};
use std::{io, num::NonZero, path::PathBuf, sync::Arc, time::Instant};
use thiserror::Error;

/// A type alias for a `Result` whose error type is a Carcara error.
pub type CarcaraResult<T> = Result<T, Error>;

/// An input to Carcara: an SMT-LIB problem instance, its associated Alethe proof, and an optional
/// set of Rare rules.
pub struct Input<'s> {
    pub problem: parser::Source<'s>,
    pub proof: parser::Source<'s>,
    pub rare_rules: Option<parser::Source<'s>>,
}

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
/// Benchmarking statistics collected while checking are recorded in `stats`. To not collect any
/// statistics, pass `&mut ()`.
pub fn check<'s, S: CollectStats>(
    input: Input<'s>,
    parser_config: parser::Config,
    checker_config: checker::Config,
    stats: &mut S,
) -> Result<Status, Error> {
    let (status, _, _, _) = check_and_elaborate(
        input,
        parser_config,
        checker_config,
        elaborator::Config::new(),
        Vec::new(),
        stats,
    )?;
    Ok(status)
}

/// Parses and checks an Alethe proof against an SMT-LIB problem, checking steps in parallel.
///
/// This is similar to [`check`], but the proof steps are checked concurrently using `num_threads`
/// threads. The `stack_size` argument, if given, sets the stack size of the worker threads;
/// otherwise, the platform's default stack size is used.
pub fn check_parallel<'s, S: CollectStats + Send + Default>(
    input: Input<'s>,
    parser_config: parser::Config,
    checker_config: checker::Config,
    num_threads: NonZero<usize>,
    stack_size: Option<usize>,
    stats: &mut S,
) -> Result<Status, Error> {
    let mut run: RunStats = RunStats::new();

    // Parsing
    let parsing_time = Instant::now();
    let (problem, proof, rules, pool) = parser::parse(input, parser_config)?;
    run.parsing = parsing_time.elapsed();

    // Checking
    let mut checker = checker::ParallelChecker::new(Arc::new(pool), &rules, checker_config);
    let (status, checking) =
        checker.check_with_stats(&problem, &proof, num_threads, stack_size, stats)?;
    run.checking = checking;

    stats.add_run_measurement(&(proof.filename.clone(), 0), run);
    Ok(status)
}

/// Parses, checks, and elaborates an Alethe proof against an SMT-LIB problem.
///
/// This is similar to [`check`], but additionally elaborates the proof after checking it. The
/// `pipeline` argument determines the elaboration passes to apply, in order. On success, this
/// returns the proof holiness status, the parsed problem, the elaborated proof, and the term pool
/// used.
pub fn check_and_elaborate<'s, S: CollectStats>(
    input: Input<'s>,
    parser_config: parser::Config,
    checker_config: checker::Config,
    elaborator_config: elaborator::Config,
    pipeline: Vec<elaborator::ElaborationPass>,
    stats: &mut S,
) -> Result<(Status, ast::Problem, ast::Proof, ast::pool::Pool), Error> {
    let mut run: RunStats = RunStats::new();

    // Parsing
    let parsing_time = Instant::now();
    let (problem, proof, rules, mut pool) = parser::parse(input, parser_config)?;
    run.parsing = parsing_time.elapsed();

    // Checking
    let mut checker = checker::Checker::new(&mut pool, &rules, checker_config);
    let (checking_status, checking) = checker.check_with_stats(&problem, &proof, stats)?;
    run.checking = checking;

    // Elaborating
    let proof = if !pipeline.is_empty() {
        let node = ast::ProofNodeForest::from_commands(proof.commands);
        let (elaborated, times) =
            elaborator::Elaborator::new(&mut pool, &problem, elaborator_config)
                .elaborate_with_stats(node, &proof.filename, pipeline)?;
        run.elaboration = times;
        ast::Proof {
            commands: elaborated.into_commands(),
            ..proof
        }
    } else {
        proof
    };

    stats.add_run_measurement(&(proof.filename.clone(), 0), run);
    Ok((checking_status, problem, proof, pool))
}

/// Generates an SMT-LIB problem for each `lia_generic` step in a proof.
///
/// Each returned pair contains the ID of a `lia_generic` step and an SMT-LIB problem that
/// corresponds to the negation of that step's conclusion clause.
pub fn generate_lia_smt_instances<'s>(
    input: Input<'s>,
    config: parser::Config,
    use_sharing: bool,
) -> Result<Vec<(String, String)>, Error> {
    use std::fmt::Write;
    let (problem, proof, _, _) = parser::parse(input, config)?;

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

            let options = ast::printer::DisplayOptions::new()
                .use_sharing(use_sharing)
                .sharing_prefix("p_".into())
                .smt_lib_strict(true);
            write!(
                &mut problem_string,
                "{}",
                ast::printer::display_clause_smt_problem(&step.clause, options)
            )
            .unwrap();
            writeln!(&mut problem_string, "(check-sat)").unwrap();
            writeln!(&mut problem_string, "(exit)").unwrap();

            result.push((step.id.clone(), problem_string));
        }
    }
    Ok(result)
}
