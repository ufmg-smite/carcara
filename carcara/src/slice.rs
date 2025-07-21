//! Backend of the slice command.
use std::collections::{HashMap, VecDeque};

use crate::ast::{
    printer::proof_to_string, PrimitivePool, Problem, Proof, ProofCommand, ProofIter, ProofStep,
    Rc, Subproof, Term, TermPool,
};

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

/// Stores the string IDs of a step's :premises
#[derive(Debug)]
struct PremiseIds {
    premises: Vec<String>,
}

/// Produces (1) a map containing all the ids of the transitive premises of the input step and
/// bools denoting whether we need the premises of those premises and (2) a map that the IDs associates IDs of
/// the transitive premises with the IDs of their premises.
fn get_transitive_premises(
    proof: &Proof,
    step_id: String,
    max_distance: usize,
) -> (HashMap<String, bool>, HashMap<String, PremiseIds>) {
    // Items to process in BFS
    let mut queue: VecDeque<(String, usize)> = VecDeque::new();

    // Output
    let mut id_to_keep_premises: HashMap<String, bool> = HashMap::new();
    let mut id_to_premise_ids: HashMap<String, PremiseIds> = HashMap::new();

    queue.push_back((step_id, max_distance + 1)); // Different use of distance than in interface. Here it is the number of steps to include after this one
    while let Some((step_id, d)) = queue.pop_front() {
        // Get an iterator for each step we are handling to make sure we get the right premises.
        let (proof_iter, step) = get_iter_to_command(proof, &step_id);
        let not_last = d != 0;
        // We should always default to needing premises if there's a conflict between what's already in the map and what would be added.
        let keep_premises = not_last || *id_to_keep_premises.get(step.id()).unwrap_or(&false);
        match step {
            ProofCommand::Assume { .. } => {
                // Assumes have no premises to be kept
                id_to_keep_premises.insert(step.id().to_owned(), false);
                id_to_premise_ids.insert(step.id().to_owned(), PremiseIds { premises: Vec::new() });
            }
            ProofCommand::Step(proof_step) => {
                // Steps have premises we may or may not need to keep
                id_to_keep_premises.insert(step.id().to_owned(), keep_premises);
                if not_last {
                    let mut premise_entries: Vec<String> = Vec::new();
                    // Add the premises to the queue to be processed and store ids of premises
                    for premise in &proof_step.premises {
                        let premise = proof_iter.get_premise(*premise);
                        queue.push_back((premise.id().to_owned(), d - 1));
                        premise_entries.push(premise.id().to_owned());
                    }
                    for premise in &proof_step.discharge {
                        let premise = proof_iter.get_premise(*premise);
                        queue.push_back((premise.id().to_owned(), d - 1));
                    }
                    id_to_premise_ids.insert(step_id, PremiseIds { premises: premise_entries });
                }
            }
            ProofCommand::Subproof(subproof) => {
                id_to_keep_premises.insert(step.id().to_owned(), keep_premises);
                if not_last {
                    for command in &subproof.commands {
                        // Keep all assumptions of the subproof
                        if command.is_assume() {
                            queue.push_back((command.id().to_owned(), 0));
                        } else {
                            break;
                        }
                    }

                    // Keep second to last step
                    let penult = &subproof.commands[subproof.commands.len() - 2];
                    queue.push_back((penult.id().to_owned(), d - 1));

                    // We need to insert the subproof into the map so that we know to copy it when slicing
                    id_to_premise_ids
                        .insert(step.id().to_owned(), PremiseIds { premises: Vec::new() });

                    // The last step has the same ID as subproof command, which we've already said we're keeping,
                    // and no premises, so we don't need to handle it separately.
                }
            }
        }
    }

    (id_to_keep_premises, id_to_premise_ids)
}

#[derive(Debug)]
struct Frame {
    /// The position we are at now in this subproof. It's the i of a (d, i) pair.
    current_position: usize,
    /// The commands of this subproof
    commands: Vec<ProofCommand>,
}

/// Returns a vector of proof commands representing the step to slice with its subproof context, if it exists, its transitive premises, and a special end step.
fn get_slice_body(
    proof: &Proof,
    id: &str,
    pool: &mut PrimitivePool,
    max_distance: usize,
) -> Option<Vec<ProofCommand>> {
    // The constant string trust to be used in the args list for every trust step
    let trust: Rc<Term> = pool.add(Term::new_string("trust"));

    // An iterator to help us find the step we are trying to slice.
    let mut iter = proof.iter();
    // The step we are trying to slice out.
    let mut from_step: Option<&ProofCommand> = None;
    // The stack of subproofs the step we're trying to slice is in.
    let mut subproof_stack = Vec::new();

    // Search for the proof step we are trying to slice out.
    while let Some(command) = iter.next() {
        // Maintain a stack of subproofs we've encountered in order to reconstruct
        // nested subproof context if the step we're slicing is in a subproof.
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

    let from_step = from_step?;

    let (mut to_keep, mut id_to_premise_ids) =
        get_transitive_premises(proof, from_step.id().to_owned(), max_distance);

    // A map of IDs to their positions in the new proof.
    let mut id_to_index: HashMap<String, (usize, usize)> = HashMap::new();

    match from_step {
        ProofCommand::Assume { .. } => return None, // We can't slice an assume
        // Make a note to keep context of the step we're slicing.
        ProofCommand::Step(_) | ProofCommand::Subproof(_) => {
            for sp in subproof_stack {
                let sp_id = sp.commands.last().unwrap().id();
                id_to_premise_ids.insert(sp_id.to_owned(), PremiseIds { premises: Vec::new() });
                // Get assumes
                for command in &sp.commands {
                    if command.is_assume() {
                        to_keep.insert(command.id().to_owned(), false);
                    } else {
                        break;
                    }
                }
                // Get second to last step
                let penult = &sp.commands[sp.commands.len() - 2];
                if !to_keep.contains_key(penult.id()) {
                    to_keep.insert(penult.id().to_owned(), false);
                }

                // Get last step
                let ult = &sp.commands[sp.commands.len() - 1];
                to_keep.insert(ult.id().to_owned(), true); // We always need the "premises" of the last step of a subproof
            }
        }
    };

    // Maintain a stack of frames, each representing a subproof context we are currently in.
    let mut stack: Vec<Frame> = vec![Frame {
        current_position: 0,
        commands: Vec::new(),
    }];

    // Go through each command in the proof and copy it if we need to keep it.
    let mut copy_iter = proof.iter();

    let mut have_seen_target: bool = false;

    let mut child: Option<(usize, usize)> = None;
    while let Some(command) = copy_iter.next() {
        // Check if we want to copy this command
        if let Some(&need_premises) = to_keep.get(command.id()) {
            let stack_len = stack.len();
            match command {
                // If the command is an assume, just copy it without change.
                ProofCommand::Assume { .. } => {
                    let last_placed = (stack.len() - 1, stack[stack.len() - 1].current_position);
                    stack[stack_len - 1].commands.push(command.clone());
                    stack[stack_len - 1].current_position += 1;

                    // Associate the ID of this assume with its new location in the proof.
                    id_to_index.insert(command.id().to_owned(), last_placed);
                }
                // If the command is a step and we need its premises, copy it with its original rule and
                // the new locations of its premises. Otherwise, use a trust hole.
                ProofCommand::Step(proof_step) => {
                    // Make a note once we have encountered the target step so that we know we're no longer on premises
                    if proof_step.id == id {
                        have_seen_target = true;
                    }

                    let is_penult: bool = copy_iter.is_in_subproof() && {
                        let current_subproof = copy_iter
                            .current_subproof()
                            .expect("is_in_subproof is true, but current_subproof() is None");
                        let penult = &current_subproof[current_subproof.len() - 2];
                        proof_step.id == penult.id()
                    };

                    let step = if need_premises {
                        let (premises, discharge) =
                            if let Some(premise_ids) = id_to_premise_ids.get(command.id()) {
                                (
                                    premise_ids
                                        .premises
                                        .iter()
                                        .map(|s| id_to_index[s])
                                        .collect(),
                                    proof_step.discharge.clone(),
                                )
                            } else {
                                (Vec::new(), Vec::new())
                            };

                        ProofStep {
                            premises,
                            discharge,
                            ..proof_step.clone()
                        }
                    } else {
                        // If the step we are placing occurs after the target step and is the second to last step of a subproof,
                        // we should include child as a premise for it with :rule hole :args trust.
                        ProofStep {
                            id: command.id().to_owned(),
                            clause: command.clause().to_vec(),
                            rule: "hole".to_owned(),
                            premises: if have_seen_target && is_penult {
                                vec![child.expect("child variable should have been initialized")]
                            } else {
                                Vec::new()
                            },
                            args: vec![trust.clone()],
                            discharge: Vec::new(), // The trust rule doesn't discharge any assumptions
                        }
                    };

                    // Associate the ID of this step with its new location in the proof.
                    let last_placed = (stack.len() - 1, stack[stack.len() - 1].current_position);
                    if !id_to_index.contains_key(command.id()) {
                        id_to_index.insert(command.id().to_owned(), last_placed);
                    }

                    if proof_step.id == id {
                        child = Some(last_placed);
                    }

                    // Add the step
                    stack[stack_len - 1].commands.push(ProofCommand::Step(step));
                    stack[stack_len - 1].current_position += 1;

                    // If this step ends a subproof, we need to put all the commands of that subproof into the subproof struct in the previous stack frame.
                    if copy_iter.is_end_step() && need_premises {
                        // Pop the last frame and add its commands to the previous one.
                        let mut popped_frame = stack.pop().unwrap();
                        let prev = stack.last_mut().unwrap();
                        let ProofCommand::Subproof(sp) = prev.commands.last_mut().unwrap() else {
                            panic!("Expected subproof")
                        };
                        sp.commands.append(&mut popped_frame.commands);
                        if have_seen_target {
                            child =
                                Some((stack.len() - 1, stack.last().unwrap().commands.len() - 1));
                        }
                    }
                }
                ProofCommand::Subproof(subproof) => {
                    // If we need the premises of this subproof step, create a subproof command.
                    // Otherwise skip. We'll come across this ID again but as a step, and that's when we'll create a holey step.
                    if need_premises {
                        stack[stack_len - 1]
                            .commands
                            .push(ProofCommand::Subproof(Subproof {
                                commands: Vec::new(),
                                args: subproof.args.clone(),
                                context_id: subproof.context_id,
                            }));

                        // Associate ID with location in new proof.
                        let last_placed =
                            (stack.len() - 1, stack[stack.len() - 1].current_position);
                        id_to_index.insert(command.id().to_owned(), last_placed);

                        // Push fresh frame to stack to keep track of subproof commands.
                        stack[stack_len - 1].current_position += 1;
                        stack.push(Frame {
                            current_position: 0,
                            commands: Vec::new(),
                        });
                    }
                }
            }
        }
    }

    let end_step: ProofStep = ProofStep {
        id: "slice_end".to_owned(),
        clause: Vec::new(),
        rule: "hole".to_owned(),
        premises: vec![child.unwrap()],
        args: vec![trust],
        discharge: Vec::new(),
    };
    stack
        .last_mut()
        .unwrap()
        .commands
        .push(ProofCommand::Step(end_step));
    Some(stack.last().unwrap().commands.clone())
}

/// Slices a step with its associated subproof structure and constructs a proof containing that step.
pub fn slice(
    problem: &Problem,
    proof: &Proof,
    id: &str,
    pool: &mut PrimitivePool,
    max_distance: usize,
) -> Option<(Proof, String, String)> {
    use std::fmt::Write;

    let sliced_step_commands = get_slice_body(proof, id, pool, max_distance)?;

    let mut new_proof: Proof = Proof {
        constant_definitions: proof.constant_definitions.clone(),
        commands: Vec::new(),
    };
    for c in &sliced_step_commands {
        new_proof.commands.push(c.clone());
    }

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
    let _ = crate::ast::printer::write_asserts(pool, &problem.prelude, &mut bytes, &asserts, false);
    write!(&mut problem_string, "{}", String::from_utf8(bytes).unwrap()).unwrap();
    writeln!(&mut problem_string, "(check-sat)").unwrap();
    writeln!(&mut problem_string, "(exit)").unwrap();

    Some((new_proof, problem_string, proof_string))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::{self, parse_instance};

    #[test]
    fn test_slice() {
        let problem_string: &[u8] = b"
        (declare-const a Bool) 
        (declare-const b Bool)
        (declare-const c Bool)
        (assert a)
        (assert b)
        (check-sat)
        (exit)
        ";

        let proof_string: &[u8] = b"
        (assume a0 a)
        (step t0 (cl a b) :rule hole :premises (a0))
        (step t1 (cl b a) :rule hole :premises (t0))
        (step t2 (cl a b (not a)) :rule hole :premises (t0))
        (anchor :step t3)
        (assume t3.a0 (not a))
        (step t3.t0 (cl b) :rule hole :premises (t3.a0 t1))
        (step t3.t1 (cl b b) :rule hole :premises (t3.t0))
        (step t3.t2 (cl (or b b)) :rule hole :premises (t3.t1))
        (step t3 (cl (not (not a)) (or b b)) :rule subproof :discharge (t3.a0))
        (step t4 (cl a (or b b)) :rule hole :premises (t3))
        (step t5 (cl) :rule hole :premises (t4 a0 t2))   
        ";

        let (problem, proof, mut pool) =
            parse_instance(problem_string, proof_string, parser::Config::new()).unwrap();

        // Only steps that exist are sliceable
        assert!(slice(&problem, &proof, "FAKE_STEP", &mut pool, 0).is_none());

        // Assumes are unsliceable
        assert!(slice(&problem, &proof, "a0", &mut pool, 0).is_none());
        assert!(slice(&problem, &proof, "a1", &mut pool, 0).is_none());

        // Slice a normal step with distance 0 (This one uses the last step of a subproof as a premise)
        let expected_t4_d_0 = "(step t3 (cl (not (not a)) (or b b)) :rule hole :args (\"trust\"))
(step t4 (cl a (or b b)) :rule hole :premises (t3))
(step slice_end (cl) :rule hole :premises (t4) :args (\"trust\"))
";

        let actual_t4_d_0 = slice(&problem, &proof, "t4", &mut pool, 0).unwrap().2;
        assert_eq!(expected_t4_d_0, actual_t4_d_0);

        // Slice subproof conclusion with distance 0
        let expected_t3_d_0 = "(anchor :step t3)
(assume t3.a0 (not a))
(step t3.t2 (cl (or b b)) :rule hole :args (\"trust\"))
(step t3 (cl (not (not a)) (or b b)) :rule subproof :discharge (t3.a0))
(step slice_end (cl) :rule hole :premises (t3) :args (\"trust\"))
";

        let actual_t3_d_0 = slice(&problem, &proof, "t3", &mut pool, 0).unwrap().2;
        assert_eq!(expected_t3_d_0, actual_t3_d_0);

        // Slice a step inside of a subproof with distance 0
        let expected_t3_t1_d_0 = "(anchor :step t3)
(assume t3.a0 (not a))
(step t3.t0 (cl b) :rule hole :args (\"trust\"))
(step t3.t1 (cl b b) :rule hole :premises (t3.t0))
(step t3.t2 (cl (or b b)) :rule hole :premises (t3.t1) :args (\"trust\"))
(step t3 (cl (not (not a)) (or b b)) :rule subproof :discharge (t3.a0))
(step slice_end (cl) :rule hole :premises (t3) :args (\"trust\"))
";

        let actual_t3_t1_d_0 = slice(&problem, &proof, "t3.t1", &mut pool, 0).unwrap().2;
        assert_eq!(expected_t3_t1_d_0, actual_t3_t1_d_0);

        // Greater distances
        let expected_t5_d_1 = "(assume a0 a)
(step t0 (cl a b) :rule hole :args (\"trust\"))
(step t2 (cl a b (not a)) :rule hole :premises (t0))
(step t3 (cl (not (not a)) (or b b)) :rule hole :args (\"trust\"))
(step t4 (cl a (or b b)) :rule hole :premises (t3))
(step t5 (cl) :rule hole :premises (t4 a0 t2))
(step slice_end (cl) :rule hole :premises (t5) :args (\"trust\"))
";

        let actual_t5_d_1 = slice(&problem, &proof, "t5", &mut pool, 1).unwrap().2;
        assert_eq!(expected_t5_d_1, actual_t5_d_1);

        let expected_t5_d_2 = "(assume a0 a)
(step t0 (cl a b) :rule hole :premises (a0))
(step t2 (cl a b (not a)) :rule hole :premises (t0))
(anchor :step t3)
(assume t3.a0 (not a))
(step t3.t2 (cl (or b b)) :rule hole :args (\"trust\"))
(step t3 (cl (not (not a)) (or b b)) :rule subproof :discharge (t3.a0))
(step t4 (cl a (or b b)) :rule hole :premises (t3))
(step t5 (cl) :rule hole :premises (t4 a0 t2))
(step slice_end (cl) :rule hole :premises (t5) :args (\"trust\"))
";

        let actual_t5_d_2 = slice(&problem, &proof, "t5", &mut pool, 2).unwrap().2;
        assert_eq!(expected_t5_d_2, actual_t5_d_2);
    }
}
