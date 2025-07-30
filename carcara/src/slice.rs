//! Backend of the slice command.
use std::collections::{HashMap, VecDeque};

use crate::ast::{PrimitivePool, Proof, ProofCommand, ProofStep, Rc, Subproof, Term, TermPool};

enum PremiseType {
    Discharge,
    Premise,
    SubproofEnd,
}
/// Creates a map whose keys are step IDs in the proof until the conclusion of the outermost subproof of the target step
/// whose values are vectors containing the IDs of those steps' premises.
fn get_step_to_premises(
    proof: &Proof,
    target_step: &str,
) -> HashMap<String, Vec<(String, PremiseType)>> {
    let mut map = HashMap::new();
    let mut iter = proof.iter();
    let mut num_open_subproofs: usize = 0;
    let mut found_target = false;
    while let Some(command) = iter.next() {
        let ProofCommand::Step(step) = command else {
            if let ProofCommand::Subproof(_) = command {
                num_open_subproofs += 1;
            }
            continue;
        };

        if command.id() == target_step {
            found_target = true;
        }

        let mut premises: Vec<(String, PremiseType)> = step
            .premises
            .iter()
            .map(|p| (iter.get_premise(*p).id().to_owned(), PremiseType::Premise))
            .collect();

        let mut discharge: Vec<(String, PremiseType)> = step
            .discharge
            .iter()
            .map(|p| (iter.get_premise(*p).id().to_owned(), PremiseType::Discharge))
            .collect();

        premises.append(&mut discharge);

        if iter.is_end_step() {
            let previous = iter.current_subproof().unwrap().iter().nth_back(1).unwrap();
            premises.push((previous.id().to_owned(), PremiseType::SubproofEnd));
            num_open_subproofs -= 1;
        }
        map.insert(step.id.clone(), premises);

        if found_target && num_open_subproofs == 0 {
            break;
        }
    }
    map
}

/// Produces a map containing all the ids of the transitive premises of the input step and
/// bools denoting whether we need the premises of those premises.
fn get_transitive_premises(
    step_id: String,
    step_to_premises: &HashMap<String, Vec<(String, PremiseType)>>,
    max_distance: usize,
) -> HashMap<String, bool> {
    // Items to process in BFS
    let mut queue: VecDeque<(String, usize)> = VecDeque::new();

    // Output
    let mut id_to_keep_premises: HashMap<String, bool> = HashMap::new();

    queue.push_back((step_id, max_distance + 1)); // Different use of distance than in interface. Here it is the number of steps to include after this one
    while let Some((step_id, d)) = queue.pop_front() {
        let last = d == 0;
        // We should always default to needing premises if there's a conflict between what's already in the map and what would be added.
        let keep_premises = !last || *id_to_keep_premises.get(&step_id).unwrap_or(&false);
        id_to_keep_premises.insert(step_id.clone(), keep_premises);
        if !last {
            for (premise, _) in step_to_premises.get(&step_id).unwrap_or(&Vec::new()) {
                queue.push_back((premise.to_owned(), d - 1));
            }
        }
    }

    id_to_keep_premises
}

#[derive(Debug)]
struct Frame {
    /// The position we are at now in this subproof. It's the i of a (d, i) pair.
    current_position: usize,
    /// The commands of this subproof
    commands: Vec<ProofCommand>,
}

/// Returns a vector of proof commands representing the step to slice with any necessary
/// subproof context, the target step's transitive premises, and a special end step with a hole.
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

    let id_to_premise_ids = get_step_to_premises(proof, id);

    let mut to_keep =
        get_transitive_premises(from_step.id().to_owned(), &id_to_premise_ids, max_distance);

    // A map of IDs to their positions in the new proof.
    let mut id_to_index: HashMap<String, (usize, usize)> = HashMap::new();

    match from_step {
        ProofCommand::Assume { .. } => return None, // We can't slice an assume
        // Make a note to keep context of the step we're slicing.
        ProofCommand::Step(_) | ProofCommand::Subproof(_) => {
            for sp in subproof_stack {
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

    // This variable is to make sure steps get linked to their children in the proof tree
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
                                        .iter()
                                        .filter(|(_, t)| matches!(t, PremiseType::Premise))
                                        .map(|(s, _)| id_to_index[s])
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
                        // This is to prevent the target step from being removed from the proof if it is converted to a `ProofNode`
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

                    // We need to artificially make the step we're slicing a transitive premise of any steps that occur after it,
                    // i.e., any steps we keep from its enclosing subproofs
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
                        // We need to artifically make the inner subproofs a premise of the outer subproof.
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

    // The last step of the proof concludes (cl) using the rule hole and the argument "trust"
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
    proof: &Proof,
    id: &str,
    pool: &mut PrimitivePool,
    max_distance: usize,
) -> Option<(Proof, Vec<Rc<Term>>)> {
    let sliced_step_commands = get_slice_body(proof, id, pool, max_distance)?;

    let new_proof: Proof = Proof {
        constant_definitions: proof.constant_definitions.clone(),
        commands: sliced_step_commands,
    };

    // Create an assertion in the problem for each assumption in the proof.
    let mut asserts = Vec::new();

    for command in &new_proof.commands {
        match command {
            ProofCommand::Assume { term, .. } => asserts.push(term.clone()),
            _ => break,
        }
    }

    Some((new_proof, asserts))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        ast::{compare_nodes, ProofNode},
        parser::{self, parse_instance, parse_instance_with_pool, Config},
    };

    const PROBLEM_STRING: &[u8] = b"
        (declare-const a Bool) 
        (declare-const b Bool)
        (declare-const c Bool)
        (assert a)
        (assert b)
        (check-sat)
        (exit)
        ";

    const PROOF_STRING: &[u8] = b"
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

    const PAIRS: [(&[u8], (&str, usize)); 5] = [
        // from t4, d=0 (normal step)
        (
            b"(step t3 (cl (not (not a)) (or b b)) :rule hole :args (\"trust\"))
(step t4 (cl a (or b b)) :rule hole :premises (t3))
(step slice_end (cl) :rule hole :premises (t4) :args (\"trust\"))",
            ("t4", 0),
        ),
        // from t3, d=0 (subproof conclusion)
        (
            b"(anchor :step t3)
(assume t3.a0 (not a))
(step t3.t2 (cl (or b b)) :rule hole :args (\"trust\"))
(step t3 (cl (not (not a)) (or b b)) :rule subproof :discharge (t3.a0))
(step slice_end (cl) :rule hole :premises (t3) :args (\"trust\"))
",
            ("t3", 0),
        ),
        // from t3.t1, d=0 (step inside subproof)
        (
            b"(anchor :step t3)
(assume t3.a0 (not a))
(step t3.t0 (cl b) :rule hole :args (\"trust\"))
(step t3.t1 (cl b b) :rule hole :premises (t3.t0))
(step t3.t2 (cl (or b b)) :rule hole :premises (t3.t1) :args (\"trust\"))
(step t3 (cl (not (not a)) (or b b)) :rule subproof :discharge (t3.a0))
(step slice_end (cl) :rule hole :premises (t3) :args (\"trust\"))
",
            ("t3.t1", 0),
        ),
        // Slicing with greater max distance values
        (
            b"(assume a0 a)
(step t0 (cl a b) :rule hole :args (\"trust\"))
(step t2 (cl a b (not a)) :rule hole :premises (t0))
(step t3 (cl (not (not a)) (or b b)) :rule hole :args (\"trust\"))
(step t4 (cl a (or b b)) :rule hole :premises (t3))
(step t5 (cl) :rule hole :premises (t4 a0 t2))
(step slice_end (cl) :rule hole :premises (t5) :args (\"trust\"))
",
            ("t5", 1),
        ),
        (
            b"(assume a0 a)
(step t0 (cl a b) :rule hole :premises (a0))
(step t2 (cl a b (not a)) :rule hole :premises (t0))
(anchor :step t3)
(assume t3.a0 (not a))
(step t3.t2 (cl (or b b)) :rule hole :args (\"trust\"))
(step t3 (cl (not (not a)) (or b b)) :rule subproof :discharge (t3.a0))
(step t4 (cl a (or b b)) :rule hole :premises (t3))
(step t5 (cl) :rule hole :premises (t4 a0 t2))
(step slice_end (cl) :rule hole :premises (t5) :args (\"trust\"))
",
            ("t5", 2),
        ),
    ];

    fn get_parser_config() -> Config {
        let mut config = parser::Config::new();
        config.parse_hole_args = true;
        config
    }

    #[test]
    fn test_slice() {
        let (_, proof, mut pool) =
            parse_instance(PROBLEM_STRING, PROOF_STRING, get_parser_config()).unwrap();

        // Only steps that exist are sliceable
        assert!(slice(&proof, "FAKE_STEP", &mut pool, 0).is_none());

        // Assumes are unsliceable
        assert!(slice(&proof, "a0", &mut pool, 0).is_none());
        assert!(slice(&proof, "a1", &mut pool, 0).is_none());

        for (expected, (id, d)) in PAIRS {
            let (_, expected) =
                parse_instance_with_pool(PROBLEM_STRING, expected, get_parser_config(), &mut pool)
                    .unwrap();

            let expected = ProofNode::from_commands(expected.commands);

            let actual =
                ProofNode::from_commands(slice(&proof, id, &mut pool, d).unwrap().0.commands);
            assert!(compare_nodes(&expected, &actual));
        }
    }
}
