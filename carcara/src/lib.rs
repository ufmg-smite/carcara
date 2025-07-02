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

use crate::ast::ProofIter;
use crate::benchmarking::{CollectResults, OnlineBenchmarkResults, RunMeasurement};
use ast::printer::proof_to_string;
use ast::{
    Operator, PrimitivePool, Problem, Proof, ProofCommand, ProofStep, Rc, Subproof, Term, TermPool,
};
use checker::{error::CheckerError, CheckerStatistics};
use core::panic;
use parser::{ParserError, Position};
use std::collections::{HashMap, HashSet, VecDeque};
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

/// Stores the location of a premise and optionally its links: premises and discharges.
#[derive(Eq, Hash, PartialEq, PartialOrd, Ord, Debug)]
struct Premise {
    /// The index of this premise in the original proof
    index: (usize, usize),
    /// The indices of the premieses and discharges of this premise in the original proof
    links: Option<Vec<(usize, usize)>>,
}

/// Produces a `ProofIter` to a command with a given id.
fn get_iter_to_command(proof: &Proof, id: String) -> ProofIter {
    // Navigate to the command ending the subproof
    let mut proof_iter = proof.iter();
    while let Some(command) = proof_iter.next() {
        if command.id() == id {
            break;
        }
    }
    proof_iter
}

fn get_subproof_links(subproof_location: (usize, usize), subproof_iter: ProofIter) -> Vec<(usize, usize)> {
    // A subproof's "premises" are its second to last step and assumes. \
    // Get premise's assumes. They're all at the same depth as the premise
    let mut links = Vec::new();
    for i in 0.. {
        if matches!(subproof_iter.get_premise((subproof_location.0, i)), &ProofCommand::Assume { .. }){
            links.push((subproof_location.0, i));
        } else {
            break;
        }
    }
    // Get second to last step of subproof
    links.push((subproof_location.0, subproof_location.1 - 1)); 

    links
}

/// Returns the premises of `step` to distance `max_distance` in sorted order.
fn get_transitive_premises(proof: &Proof, step: &ProofCommand, max_distance: usize) -> Vec<Premise> {
    // A queue to store proof steps whose links we need to add
    let mut queue: VecDeque<(&ProofCommand, usize)> = VecDeque::new();
    let mut transitive_premises: HashSet<Premise> = HashSet::new();
    let mut proof_iter = proof.iter(); 

    // get_premise only works of the iterator has been moved to the right part of the proof because the 
    // indices are relative, so we move the iterator to the input step
    while let Some(command) = proof_iter.next() {
        if command.id() == step.id() {
            break;
        }
    }
    
    queue.push_back((step, max_distance));
    while let Some((step, d)) = queue.pop_front() {
        match step {
            ProofCommand::Step(step) => {
                for premise in &step.premises {
            if d == 0 {
                transitive_premises.insert(Premise { index: *premise, links: None });
            } else {
                let premise_command = proof_iter.get_premise(*premise);
                let mut links :Vec<(usize, usize)> = Vec::new();
                match premise_command {
                    ProofCommand::Step(premise_step) => {
                        links.append(&mut premise_step.premises.clone());
                     }
                    ProofCommand::Subproof(premise_subproof) => {
                        // Navigate to the command ending the subproof
                        let mut subproof_iter = get_iter_to_command(proof, premise_command.id().to_owned());
                        links.append(&mut get_subproof_links(*premise, subproof_iter));
                    }
                    ProofCommand::Assume { .. } => {}
                }
                
                transitive_premises.insert(Premise {
                    index: *premise,
                    links: Some(links),
                });

                queue.push_back((premise_command, d - 1));
            }
        }
            },
            ProofCommand::Assume { .. } => {
                // Intentionally blank. Assumes don't have any premises for us to retrieve.
            },

            ProofCommand::Subproof(subproof) => {
                // TODO
            }
        }
        
    }

    let mut output: Vec<Premise> = transitive_premises.into_iter().collect();
    output.sort_unstable();
    output
    
    
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

    let mut commands: Vec<ProofCommand> = Vec::new();
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

    match from_step {
        None => None,
        Some(from_step) => {
            // Construct a stack of subproofs that just contains any added context from its corresponding
            // subproof in the original proof, any assumes in the subproof, the second-to-last step, and the conclusion.
            let mut new_subproofs: Vec<Subproof> = Vec::new();

            // The step we're slicing is a "subproof" when it's the last step of a subproof. However,
            // the last step of a subproof isn't really "inside" that subproof in the same sense
            // as the other steps. It doesn't rely on the anchor or assumptions,
            // so we shouldn't copy them.
            if let ProofCommand::Subproof(_) = from_step {
                subproof_stack.pop();
            }

            // Copy all the added context from the stack of open subproofs.
            for sp in &subproof_stack {
                new_subproofs.push(Subproof {
                    commands: Vec::new(),
                    args: sp.args.clone(),
                    context_id: sp.context_id,
                });
                let current_subproof = new_subproofs.last_mut().unwrap();
                // Add assumes and second to last step
                for command in &sp.commands {
                    if command.is_assume() {
                        current_subproof.commands.push(command.clone());
                    } else {
                        break;
                    }
                }
                let len = sp.commands.len();

                // Create the second-to-last (penultimate) step of the subproof using hole with trust args.
                let penult = &sp.commands[len - 2];
                let penult_step = extract_step(penult);
                let new_penult_step = ProofStep {
                    id: penult_step.id.clone(),
                    clause: penult_step.clause.clone(),
                    rule: "hole".to_owned(),
                    premises: Vec::new(),
                    args: vec![trust.clone()],
                    discharge: Vec::new(),
                };

                // Create the last step of the subproof using the same rule that originally closed the subproof.
                let ult = &sp.commands[len - 1];
                let ult_step = extract_step(ult);
                let new_ult_step = ProofStep {
                    id: ult_step.id.clone(),
                    clause: ult_step.clause.clone(),
                    rule: ult_step.rule.clone(),
                    premises: Vec::new(),
                    args: ult_step.args.clone(),
                    discharge: ult_step.discharge.clone(),
                };

                // Add the new versions of the last two steps to the subproof.
                current_subproof
                    .commands
                    .push(ProofCommand::Step(new_penult_step));
                current_subproof
                    .commands
                    .push(ProofCommand::Step(new_ult_step));
            }

            // Collect all premises of the step being sliced.
            let goal_command = match from_step {
                // In this case, we are slicing a normal step. We must create a new step with the same clause and rule, but with premises that are mapped to the new proof.
                ProofCommand::Step(step) => {
                    // In this version, this maps the indices of premises in the original proof to the indices of premises in the sliced proof
                    let mut premise_map: HashMap<(usize, usize), (usize, usize)> = HashMap::new();

                    let transitive_premises = get_transitive_premises(proof, from_step, max_distance);

                    // First, handle each premise that occurs outside of a subproof
                    for premise in &transitive_premises {
                        if premise.index.0 == 0 && !premise_map.contains_key(&premise.index) {
                            let premise_command = iter.get_premise(premise.index);
                            // Construct the new command based on whether the premise is an assume or an Alethe step
                            let new_command = match premise_command {
                                // If it's an assume, just copy it verbatim.
                                ProofCommand::Assume { id: _, term: _ } => premise_command.clone(),

                                ProofCommand::Step(step) => {
                                    ProofCommand::Step(if let Some(links) = &premise.links {
                                        let premises = links
                                            .iter()
                                            .map(|index| premise_map[index])
                                            .collect();
                                        ProofStep { premises, ..step.clone() }
                                    } else {
                                        ProofStep {
                                            id: premise_command.id().to_owned(),
                                            clause: premise_command.clause().to_vec(),
                                            rule: "hole".to_owned(),
                                            premises: Vec::new(),
                                            args: vec![trust.clone()],
                                            discharge: Vec::new(), // The trust rule doesn't discharge any assumptions
                                        }
                                    })
                                }

                                // If it's an Alethe step (represented by a Step or Subproof, )
                                ProofCommand::Subproof(_) => ProofCommand::Step(ProofStep {
                                    id: premise_command.id().to_owned(),
                                    clause: premise_command.clause().to_vec(),
                                    rule: "hole".to_owned(),
                                    premises: Vec::new(),
                                    args: vec![trust.clone()],
                                    discharge: Vec::new(), // The trust rule doesn't discharge any assumptions
                                }),
                            };
                            commands.push(new_command);
                            premise_map.insert(
                                premise.index,
                                (0, ASSUME_FALSE_OFFSET + commands.len() - 1),
                            );
                        // Index calculation
                        } else if premise.index.0 != 0 {
                            // Changed to else if to stop early breaking with repeated premise
                            break;
                        }
                    }

                    // Now we need to handle the premises that are in subproofs. We add them to the corresponding subproofs in the new proof and update the premise map accordingly
                    for premise in &transitive_premises {
                        if premise.index.0 == 0 {
                            continue;
                        }
                        let stack_depth = premise.index.0 - 1; // If depth 1 then index 0 in subproof stack

                        premise_map.entry(premise.index).or_insert_with(|| {
                            // Find premise id in current subproof
                            // If it is present, make premise index its location
                            // If it is absent, then add as trust step, and premise index should be wherever we add this
                            let premise_command = iter.get_premise(premise.index);
                            let premise_pos = new_subproofs[stack_depth]
                                .commands
                                .iter()
                                .position(|c| c.id() == premise_command.id());
                            if let Some(i) = premise_pos {
                                (premise.index.0, i)
                            } else {
                                let step = ProofStep {
                                    id: premise_command.id().to_owned(),
                                    clause: premise_command.clause().to_vec(),
                                    rule: "hole".to_owned(),
                                    premises: Vec::new(),
                                    args: vec![trust.clone()],
                                    discharge: Vec::new(),
                                };
                                // Add as trust step
                                let len = new_subproofs[stack_depth].commands.len();
                                new_subproofs[stack_depth]
                                    .commands
                                    .insert(len - 2, ProofCommand::Step(step));
                                // -1 then -2 because of last two steps
                                (
                                    premise.index.0,
                                    new_subproofs[stack_depth].commands.len() - 3,
                                )
                            }
                        });
                    }

                    // Now that we have created all the commands and know where they are, we can make a list of the indices of the premises in the new proof
                    let mut new_premises: Vec<(usize, usize)> = Vec::new();
                    for premise in &step.premises {
                        new_premises.push(premise_map[premise]);
                    }
                    /*  The step being sliced out gets a unique identifier. s stands for sliced.
                    This is to avoid naming conflicts when slicing the second to last step of a subproof.
                    For simplicity, we still copy the second to last step of a subproof even if the
                    step being sliced is the same.
                    */
                    let goal_step = ProofStep {
                        id: format!("s{}", step.id),
                        clause: step.clause.clone(),
                        rule: step.rule.clone(),
                        premises: new_premises,
                        args: step.args.clone(),
                        discharge: Vec::new(),
                    };

                    ProofCommand::Step(goal_step)
                }

                // In this case, we are slicing the last step of a subproof. We must create a new subproof with the same context, but with the second-to-last step using the trust rule and the last step using the same rule as before.
                ProofCommand::Subproof(sp) => {
                    // First, get the original last command of the subproof.
                    let last_command = sp.commands.last().unwrap();
                    let mut goal_command: Option<ProofCommand> = None;

                    // Collect all the assumes in the subproof.
                    let mut subproof_assumptions = Vec::new();

                    for command in &sp.commands {
                        if let ProofCommand::Assume { .. } = command {
                            subproof_assumptions.push(command.clone());
                        } else {
                            break; // Stop when we reach the first non-assume command
                        }
                    }

                    // Get the step from the last command.
                    if let ProofCommand::Step(closing_step) = last_command {
                        // Create a new subproof with the same context.
                        let mut new_subproof = Subproof {
                            args: sp.args.clone(),
                            commands: Vec::new(),
                            context_id: sp.context_id,
                        };

                        // Create the second-to-last step with the trust rule.
                        let penult = sp.commands[sp.commands.len() - 2].clone();
                        if let ProofCommand::Step(ps) = penult {
                            let new_penult = ProofCommand::Step(ProofStep {
                                id: ps.id.clone(),
                                clause: ps.clause.clone(),
                                rule: "hole".to_owned(),
                                premises: Vec::new(),
                                args: vec![trust.clone()],
                                discharge: Vec::new(),
                            });
                            // Add all of the assumptions.
                            for a in subproof_assumptions {
                                new_subproof.commands.push(a);
                            }
                            // Add the last two steps.
                            new_subproof.commands.push(new_penult);
                            new_subproof
                                .commands
                                .push(ProofCommand::Step(closing_step.clone()));

                            goal_command = Some(ProofCommand::Subproof(new_subproof));
                        }
                    }
                    goal_command.expect("Goal command never got set") // This should never happen
                }

                ProofCommand::Assume { .. } => return None, // Return none if the command being sliced exists but is not a step or a subproof
            };

            // Build up the subproof structure the sliced step is in, starting with the innermost subproof.
            if new_subproofs.is_empty() {
                commands.push(goal_command);
            } else {
                let last_commands = &mut new_subproofs.last_mut().unwrap().commands;
                let len = last_commands.len();
                last_commands.insert(len - 2, goal_command);

                let mut iter = new_subproofs.into_iter().rev();
                let mut outer = iter.next();
                for mut subproof in iter {
                    let len = subproof.commands.len();
                    subproof
                        .commands
                        .insert(len - 2, ProofCommand::Subproof(outer.unwrap()));
                    outer = Some(subproof);
                }

                commands.push(ProofCommand::Subproof(outer.unwrap()));
            }
            Some(commands)
        }
    }
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
