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
mod drup;
pub mod elaborator;
pub mod parser;
mod resolution;
mod utils;

use crate::ast::{ProofIter, Subproof};
use crate::benchmarking::{CollectResults, OnlineBenchmarkResults, RunMeasurement};
use ast::printer::proof_to_string;
use ast::{Operator, PrimitivePool, Problem, Proof, ProofCommand, ProofStep, Rc, Term, TermPool};
use checker::{error::CheckerError, CheckerStatistics};
use core::panic;
use parser::{ParserError, Position};
use std::collections::{HashMap, VecDeque};
use std::io;
use std::time::{Duration, Instant};
use thiserror::Error;

pub type CarcaraResult<T> = Result<T, Error>;

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

pub fn check<T: io::BufRead>(
    problem: T,
    proof: T,
    parser_config: parser::Config,
    checker_config: checker::Config,
    collect_stats: bool,
) -> Result<bool, Error> {
    let mut run_measures: RunMeasurement = RunMeasurement::default();

    // Parsing
    let total = Instant::now();
    let (problem, proof, mut pool) = parser::parse_instance(problem, proof, parser_config)?;
    run_measures.parsing = total.elapsed();

    // Checking
    let checking = Instant::now();
    let mut checker = checker::ProofChecker::new(&mut pool, checker_config);
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

pub fn check_parallel<T: io::BufRead>(
    problem: T,
    proof: T,
    parser_config: parser::Config,
    checker_config: checker::Config,
    collect_stats: bool,
    num_threads: usize,
    stack_size: usize,
) -> Result<bool, Error> {
    use crate::checker::Scheduler;
    use std::sync::Arc;
    let mut run_measures: RunMeasurement = RunMeasurement::default();

    // Parsing
    let total = Instant::now();
    let (problem, proof, pool) = parser::parse_instance(problem, proof, parser_config)?;
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

pub fn check_and_elaborate<T: io::BufRead>(
    problem: T,
    proof: T,
    parser_config: parser::Config,
    checker_config: checker::Config,
    elaborator_config: elaborator::Config,
    pipeline: Vec<elaborator::ElaborationStep>,
    collect_stats: bool,
) -> Result<(bool, ast::Problem, ast::Proof, ast::PrimitivePool), Error> {
    let mut run: RunMeasurement = RunMeasurement::default();

    // Parsing
    let total = Instant::now();
    let (problem, proof, mut pool) = parser::parse_instance(problem, proof, parser_config)?;
    run.parsing = total.elapsed();

    let mut stats = OnlineBenchmarkResults::new();

    // Checking
    let checking = Instant::now();
    let mut checker = checker::ProofChecker::new(&mut pool, checker_config);
    let checking_result = if collect_stats {
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

    let node = ast::ProofNode::from_commands(proof.commands);
    let (elaborated, pipeline_durations) =
        elaborator::Elaborator::new(&mut pool, &problem, elaborator_config)
            .elaborate_with_stats(&node, pipeline);
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

    Ok((checking_result, problem, elaborated, pool))
}

pub fn generate_lia_smt_instances<T: io::BufRead>(
    problem: T,
    proof: T,
    config: parser::Config,
    use_sharing: bool,
) -> Result<Vec<(String, String)>, Error> {
    use std::fmt::Write;
    let (problem, proof, mut pool) = parser::parse_instance(problem, proof, config)?;

    let mut iter = proof.iter();
    let mut result = Vec::new();
    while let Some(command) = iter.next() {
        if let ast::ProofCommand::Step(step) = command {
            if step.rule == "lia_generic" {
                if iter.depth() > 0 {
                    log::error!(
                        "generating SMT instance for step inside subproof is not supported"
                    );
                    continue;
                }

                let mut problem_string = String::new();
                write!(&mut problem_string, "{}", problem.prelude).unwrap();

                let mut bytes = Vec::new();
                ast::printer::write_lia_smt_instance(
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
    }
    Ok(result)
}

/// Extracts the step represented by a `ProofCommand`. For a `ProofCommand::Step`, it
/// is the underlying step. For a `ProofCommand::Subproof`, it is the the conclusion of the subproof.
fn extract_step(command: &ProofCommand) -> &ProofStep {
    match command {
        ProofCommand::Step(step) => step,
        ProofCommand::Subproof(sp) => {
            let last_command = sp.commands.last().unwrap();
            if let ProofCommand::Step(s) = last_command {
                s
            } else {
                panic!("Subproof does not end in step.") // We won't get here because there will already have been a parser error
            }
        }
        // This would only happen if one of the last two commands of a subproof were somehow an assume.
        // The last can't be because we would have gotten a parser error already.
        // However, the second to last could be since the parser would not give an error.
        ProofCommand::Assume { .. } => panic!("Tried to extract step from assume."),
    }
}

/// Produces a `ProofIter` to a command with a given id.
fn get_iter_to_command<'a>(proof: &'a Proof, id: &'a str) -> (ProofIter<'a>, &'a ProofCommand) {
    // Navigate to the command ending the subproof
    let mut proof_iter = proof.iter();
    while let Some(command) = proof_iter.next() {
        if command.id() == id {
            return (proof_iter, command);
        }
    }
    panic!("Invalid command to get proof iterator to.");
}


/// Produces a map containing the ids of the transitive premises of the input step and 
/// bools denoting whether we need the premises of those premises.
fn get_transitive_premises(
    proof: &Proof,
    step_id: String,
    max_distance: usize,
) -> HashMap<String, bool> {
    let mut queue: VecDeque<(String, usize)> = VecDeque::new();
    let mut map: HashMap<String, bool> = HashMap::new();

    queue.push_back((step_id, max_distance));
    while let Some((step_id, d)) = queue.pop_front() {
        // Get an iterator for each step we are handling to make sure we get the right premises.
        let (proof_iter, step) = get_iter_to_command(proof, &step_id);
        let need_premises = d != 0;
        match step {
            ProofCommand::Assume { .. } => {
                // Intentionally blank
            }
            ProofCommand::Step(proof_step) => {
                // Add the ids of the premises of the step we're processing to the map
                for premise in &proof_step.premises {
                    let premise = proof_iter.get_premise(*premise);
                    map.insert(premise.id().to_owned(), need_premises); // True if we need to retrieve premises, false otherwise
                    if need_premises {
                        queue.push_back((premise.id().to_owned(), d - 1));
                    }
                    
                }
                for premise in &proof_step.discharge {
                    let premise = proof_iter.get_premise(*premise);
                    map.insert(premise.id().to_owned(), need_premises); // True if we need to retrieve premises, false otherwise
                    if need_premises {
                        queue.push_back((premise.id().to_owned(), d - 1));
                    }
                    
                }
            }
            ProofCommand::Subproof(subproof) => {
                // Get assumes
                for command in &subproof.commands {
                    if command.is_assume() {
                        map.insert(command.id().to_owned(), false);
                    } else {
                        break;
                    }
                }

                // Get second to last step
                let penult = &subproof.commands[subproof.commands.len() - 2];
                map.insert(penult.id().to_owned(), need_premises);
                if need_premises {
                    queue.push_back((penult.id().to_owned(), d - 1));
                }
            }
        }
    }

    return map;
}

struct Frame {
    /// A map from the indices in the original subproof to the indices in the new one
    map: HashMap<(usize, usize), (usize, usize)>,
    /// The position we are at now in this subproof. It's the i of a (d, i) pair.
    current_position: usize,
    /// The commands of this subproof
    commands: Vec<ProofCommand>,
}

/// Gets the step to slice as well as everything directly associated with it, i.e., its premises and the subproofs it is in.
/// Returns a vector containing the step to slice inside a reconstructed subproof stack, preceded by any premises that are not inside a subproof.
pub fn sliced_step(
    proof: &Proof,
    id: &str,
    pool: &mut PrimitivePool,
    max_distance: usize,
) -> Option<Vec<ProofCommand>> {
    const ASSUME_FALSE_OFFSET: usize = 1;

    let mut iter = proof.iter();
    let mut from_step: Option<&ProofCommand> = None;
    let mut subproof_stack = Vec::new();

    // The constant string trust to be used in the args list for every trust step
    let trust = pool.add(Term::new_string("trust"));

    // Search for the proof step we are trying to slice out.
    while let Some(command) = iter.next() {
        /* Maintain a stack of subproofs we've encountered in order to reconstruct
        nested subproof context if the step we're slicing is in a subproof. */
        if let ProofCommand::Subproof(sp) = command {
            subproof_stack.push(sp);
        }
        if iter.is_end_step() {
            subproof_stack.pop();
        }

        // We have found the step we are trying to slice
        if command.id() == id {
            from_step = Some(command);
            break;
        }
    }

    let Some(from_step) = from_step else {
        return None;
    };
    let subproof_skeleton_ids: Vec<String> = match from_step {
        ProofCommand::Assume { .. } => return None,
        ProofCommand::Step(_) | ProofCommand::Subproof(_) => {
            let mut skeletons = Vec::new();
            for sp in subproof_stack {
                // Get assumes
                for command in &sp.commands {
                    if command.is_assume() {
                        skeletons.push(command.id().to_owned());
                    } else {
                        break;
                    }
                }
                // Get second to last step
                let penult = &sp.commands[sp.commands.len() - 2];
                skeletons.push(penult.id().to_owned());
                // Get last step
                let ult = &sp.commands[sp.commands.len() - 1];
                skeletons.push(ult.id().to_owned());
            }
            skeletons
        }
    };

    let mut to_keep = get_transitive_premises(proof, from_step.id().to_owned(), max_distance);
    for id in subproof_skeleton_ids {
        if !to_keep.contains_key(&id) {
            to_keep.insert(id, false);
        }
    }

    let mut copy_iter = proof.iter();

    // Maintain maps for each subproof we encounter. Keep track of stacks properly
    let mut stack: Vec<Frame> = vec![Frame {
        map: HashMap::new(),
        current_position: ASSUME_FALSE_OFFSET,
        commands: Vec::new(),
    }];

    while let Some(command) = copy_iter.next() {
        println!("{}", command.id());
        // Check if we want to copy this command
        if let Some(&need_premises) = to_keep.get(command.id()) {
            let stack_len = stack.len();
            match command {
                // If the command is an assume, copy it in the most straightforward ay.
                ProofCommand::Assume { .. } => {
                    stack[stack_len - 1].commands.push(command.clone());
                    stack[stack_len - 1].current_position += 1;
                }
                // If the command is a step, either copy it with its original rule and its premises and discharges determined using
                // this subproof's map or hole.
                ProofCommand::Step(proof_step) => {
                    let top_map = &stack[stack_len - 1].map;
                    let step = if need_premises {
                        let premises: Vec<(usize, usize)> = proof_step
                            .premises
                            .iter()
                            .map(|index| top_map[index])
                            .collect();
                        let discharge: Vec<(usize, usize)> = proof_step
                            .discharge
                            .iter()
                            .map(|index| top_map[index])
                            .collect();
                        ProofStep {
                            premises,
                            discharge,
                            ..proof_step.clone()
                        }
                    } else {
                        ProofStep {
                            id: command.id().to_owned(),
                            clause: command.clause().to_vec(),
                            rule: "hole".to_owned(),
                            premises: Vec::new(),
                            args: vec![trust.clone()],
                            discharge: Vec::new(), // The trust rule doesn't discharge any assumptions
                        }
                    };
                    stack[stack_len - 1].commands.push(ProofCommand::Step(step));
                    stack[stack_len - 1].current_position += 1;

                    if copy_iter.is_end_step() {
                        // Use split_at_mut to get non-overlapping mutable references
                        let (bottom, top) = stack.split_at_mut(stack_len - 1);
                        let subproof = bottom[stack_len - 2].commands.last_mut().unwrap();
                        if let ProofCommand::Subproof(subproof) = subproof {
                            for sp_command in &top[0].commands {
                                subproof.commands.push(sp_command.clone());
                            }
                        }
                        stack.pop();
                    }
                }
                ProofCommand::Subproof(subproof) => {
                    // If we need the premises of this subproof step, create a subproof command.
                    // Otherwise skip, we'll come across this id again but as a step, and that's when we'll create a holey step
                    if need_premises {
                        stack[stack_len - 1]
                            .commands
                            .push(ProofCommand::Subproof(Subproof {
                                commands: Vec::new(),
                                args: subproof.args.clone(),
                                context_id: subproof.context_id.clone(),
                            }));
                        stack[stack_len - 1].current_position += 1;
                        stack.push(Frame {
                            map: HashMap::new(),
                            current_position: 0,
                            commands: Vec::new(),
                        });
                    }
                }
            }
        }
    }

    Some(stack.last().unwrap().commands.clone())
}

/// Slices a step with its associated subproof structure and constructs a proof containing that step.
/// The beginning of the proof is an assumption of false that gets resolved with (not false) in the end.
pub fn slice(
    problem: &Problem,
    proof: &Proof,
    id: &str,
    pool: &mut PrimitivePool,
    max_distance: usize,
) -> Option<(Proof, String, String)> {
    use std::fmt::Write;

    if let Some(sliced_step_commands) = sliced_step(proof, id, pool, max_distance) {
        // The resolution premises are (cl false) and (cl (not false)).
        let mut resolution_premises: Vec<(usize, usize)> = Vec::new();
        let mut new_proof: Proof = Proof {
            constant_definitions: proof.constant_definitions.clone(),
            commands: Vec::new(),
        };
        let false_term: Rc<Term> = pool.add(Term::new_bool(false));
        new_proof.commands.push(ProofCommand::Assume {
            id: "slice_assume_false".to_owned(),
            term: false_term.clone(),
        });
        for c in &sliced_step_commands {
            new_proof.commands.push(c.clone());
        }

        new_proof.commands.push(ProofCommand::Step(ProofStep {
            id: "slice_not_false".to_owned(),
            clause: [pool.add(Term::Op(Operator::Not, [false_term.clone()].to_vec()))].to_vec(),
            rule: "false".to_owned(),
            premises: Vec::new(),
            args: Vec::new(),
            discharge: Vec::new(),
        }));

        resolution_premises.push((0, 0)); // False
        resolution_premises.push((0, new_proof.commands.len() - 1)); // Not false
        let resolution_step = ProofStep {
            id: "t.end".to_owned(),
            clause: Vec::new(),
            rule: "resolution".to_owned(),
            premises: resolution_premises,
            args: Vec::new(),
            discharge: Vec::new(),
        };
        new_proof.commands.push(ProofCommand::Step(resolution_step));

        let proof_string = proof_to_string(pool, &problem.prelude, &new_proof, false);

        // Create an assertion in the problem for each assumption in the proof.
        let mut asserts = Vec::new();

        for command in &new_proof.commands {
            match command {
                ProofCommand::Assume { term, .. } => asserts.push(term.clone()),
                _ => break,
            }
        }

        let mut problem_string = String::new();
        write!(&mut problem_string, "{}", &problem.prelude).unwrap();

        let mut bytes = Vec::new();
        let _ = ast::printer::write_asserts(pool, &problem.prelude, &mut bytes, &asserts, false);
        write!(&mut problem_string, "{}", String::from_utf8(bytes).unwrap()).unwrap();
        writeln!(&mut problem_string, "(check-sat)").unwrap();
        writeln!(&mut problem_string, "(exit)").unwrap();

        Some((new_proof, problem_string, proof_string))
    } else {
        None
    }
}
