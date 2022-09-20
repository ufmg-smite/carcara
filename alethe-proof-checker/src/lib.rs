#![deny(clippy::disallowed_methods)]
#![deny(clippy::self_named_module_files)]
#![deny(clippy::undocumented_unsafe_blocks)]
#![warn(clippy::branches_sharing_code)]
#![warn(clippy::cloned_instead_of_copied)]
#![warn(clippy::copy_iterator)]
#![warn(clippy::dbg_macro)]
#![warn(clippy::doc_markdown)]
#![warn(clippy::equatable_if_let)]
#![warn(clippy::eval_order_dependence)]
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
pub mod parser;
mod utils;

use ast::ProofCommand;
use checker::error::CheckerError;
use parser::ParserError;
use parser::Position;
use std::io;
use thiserror::Error;

pub type AletheResult<T> = Result<T, Error>;

#[derive(Debug, Error)]
pub enum Error {
    #[error("IO error: {0}")]
    Io(#[from] io::Error),

    #[error("parser error: {0} (on line {}, column {})", (.1).0, (.1).1)]
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

pub fn check<T: io::BufRead>(
    problem: T,
    proof: T,
    apply_function_defs: bool,
    skip_unknown_rules: bool,
) -> Result<bool, Error> {
    let (_, proof, mut pool) = parser::parse_instance(problem, proof, apply_function_defs)?;

    let config = checker::Config {
        skip_unknown_rules,
        is_running_test: false,
        statistics: None,
    };
    checker::ProofChecker::new(&mut pool, config).check(&proof)
}

pub fn check_and_elaborate<T: io::BufRead>(
    problem: T,
    proof: T,
    apply_function_defs: bool,
    skip_unknown_rules: bool,
) -> Result<Vec<ProofCommand>, Error> {
    let (_, proof, mut pool) = parser::parse_instance(problem, proof, apply_function_defs)?;

    let config = checker::Config {
        skip_unknown_rules,
        is_running_test: false,
        statistics: None,
    };
    checker::ProofChecker::new(&mut pool, config)
        .check_and_elaborate(proof)
        .map(|p| p.commands)
}

pub fn generate_lia_smt_instances<T: io::BufRead>(
    problem: T,
    proof: T,
    apply_function_defs: bool,
) -> Result<Vec<(String, String)>, Error> {
    let (prelude, proof, _) = parser::parse_instance(problem, proof, apply_function_defs)?;
    checker::generate_lia_smt_instances(prelude, &proof)
}
