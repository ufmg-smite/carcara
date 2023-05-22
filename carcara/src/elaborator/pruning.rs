use super::{CommandDiff, ProofDiff};
use crate::ast::*;
use std::collections::VecDeque;

struct Frame<'a> {
    commands: &'a [ProofCommand],

    /// The computed diffs for subproofs that are inside of this one
    subproof_diffs: Vec<Option<ProofDiff>>,

    /// The index of the subproof that this frame represents, in the outer subproof
    index_of_subproof: usize,

    /// For each command, the distance between it and the source.
    distance_to_source: Vec<usize>,

    /// The queue of commands to visit, represented as a tuple of (command index, distance to
    /// source)
    queue: VecDeque<(usize, usize)>,
}

pub fn prune_proof(proof: &[ProofCommand]) -> ProofDiff {
    let end_step = proof
        .iter()
        .position(|c| c.clause().is_empty())
        .expect("proof does not reach empty clause");

    slice_proof(proof, end_step, None)
}

pub fn slice_proof(
    proof: &[ProofCommand],
    source: usize,
    max_distance: Option<usize>,
) -> ProofDiff {
    assert!(proof.len() > source, "invalid slice index");

    let mut stack = vec![Frame {
        commands: proof,
        subproof_diffs: vec![None; proof.len()],
        distance_to_source: vec![usize::MAX; proof.len()],
        index_of_subproof: 0, // For the root proof, this value is irrelevant
        queue: VecDeque::from([(source, 0usize)]),
    }];

    loop {
        'inner: loop {
            let frame = stack.last_mut().unwrap();
            let Some((current, current_dist)) = frame.queue.pop_front() else {
                break 'inner;
            };
            if frame.distance_to_source[current] < usize::MAX {
                continue;
            }
            frame.distance_to_source[current] =
                std::cmp::min(frame.distance_to_source[current], current_dist);

            if max_distance.map_or(false, |max| current_dist > max) {
                continue;
            }

            match &frame.commands[current] {
                ProofCommand::Assume { .. } => (),
                ProofCommand::Step(s) => {
                    for &(_, i) in &s.premises {
                        frame.queue.push_back((i, current_dist + 1));
                    }
                }
                ProofCommand::Subproof(s) => {
                    let n = s.commands.len();
                    let mut new_queue = VecDeque::new();
                    new_queue.push_back((n - 1, current_dist));

                    // Since `assume` commands in a subproof are implicitly referenced by the last
                    // step in the subproof, we must add them to the queue now
                    for (i, command) in s.commands.iter().enumerate() {
                        if command.is_assume() {
                            new_queue.push_back((i, current_dist + 1));
                        }
                    }

                    // The second to last command in a subproof is also implicitly referenced by the
                    // last step, so we also add it to the queue
                    if n >= 2 {
                        new_queue.push_back((n - 2, current_dist + 1));
                    }

                    let frame = Frame {
                        commands: &s.commands,
                        subproof_diffs: vec![None; n],
                        distance_to_source: vec![usize::MAX; n],
                        index_of_subproof: current,
                        queue: new_queue,
                    };
                    stack.push(frame);
                }
            }
        }
        let mut frame = stack.pop().unwrap();

        let mut result_diff = Vec::new();
        let mut new_indices = Vec::new();
        let mut num_pruned = 0;
        let depth = stack.len();
        for i in 0..frame.commands.len() {
            new_indices.push((depth, i - num_pruned));

            if frame.distance_to_source[i] == usize::MAX {
                result_diff.push((i, CommandDiff::Delete));
                num_pruned += 1;
            } else if max_distance.map_or(false, |max| frame.distance_to_source[i] == max + 1) {
                let new_command = ProofCommand::Step(ProofStep {
                    id: frame.commands[i].id().to_owned(),
                    clause: frame.commands[i].clause().to_vec(),
                    rule: "hole".to_owned(),
                    premises: Vec::new(),
                    args: Vec::new(),
                    discharge: Vec::new(),
                });
                result_diff.push((i, CommandDiff::Step(vec![new_command])));
            } else if let Some(diff) = frame.subproof_diffs[i].take() {
                result_diff.push((i, CommandDiff::Subproof(diff)));
            }
        }
        let result_diff = ProofDiff { commands: result_diff, new_indices };

        if let Some(outer_frame) = stack.last_mut() {
            outer_frame.subproof_diffs[frame.index_of_subproof] = Some(result_diff);
        } else {
            return result_diff;
        }
    }
}
