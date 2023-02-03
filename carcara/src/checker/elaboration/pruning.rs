use super::{CommandDiff, ProofDiff};
use crate::ast::*;
use std::collections::VecDeque;

struct Frame<'a> {
    commands: &'a [ProofCommand],

    /// The computed diffs for subproofs that are inside of this one
    subproof_diffs: Vec<Option<ProofDiff>>,

    /// The index of the subproof that this frame represents, in the outer subproof
    index_of_subproof: usize,
    visited: Vec<bool>,
}

pub fn prune_proof(proof: &[ProofCommand]) -> ProofDiff {
    assert!(!proof.is_empty(), "cannot prune an empty proof");

    let end_step = proof
        .iter()
        .position(|c| c.clause().is_empty())
        .expect("proof does not reach empty clause");

    let root = Frame {
        commands: proof,
        subproof_diffs: vec![None; proof.len()],
        visited: vec![false; proof.len()],
        index_of_subproof: 0, // For the root proof, this value is irrelevant
    };
    let mut stack = vec![root];
    let mut to_visit = vec![VecDeque::from([end_step])];

    loop {
        'inner: loop {
            let frame = stack.last_mut().unwrap();
            let current = match to_visit.last_mut().unwrap().pop_front() {
                Some(i) => i,
                None => break 'inner,
            };
            if frame.visited[current] {
                continue;
            }

            frame.visited[current] = true;
            match &frame.commands[current] {
                ProofCommand::Assume { .. } => (),
                ProofCommand::Step(s) => {
                    for &(depth, i) in &s.premises {
                        to_visit[depth].push_back(i);
                    }
                }
                ProofCommand::Subproof(s) => {
                    let n = s.commands.len();
                    let mut visited = vec![false; n];
                    let mut new_queue = VecDeque::new();
                    new_queue.push_back(n - 1);

                    // Since the second to last command in a subproof may be implicitly referenced
                    // by the last command, we have to add it to the `to_visit` queue if it exists
                    if n >= 2 {
                        new_queue.push_back(n - 2);
                    }

                    // Since `assume` commands in the subproof cannot be removed we need to always
                    // visit them. As they don't have any premises, we can just mark them as visited
                    // now
                    for (i, command) in s.commands.iter().enumerate() {
                        if command.is_assume() {
                            visited[i] = true;
                        }
                    }

                    let frame = Frame {
                        commands: &s.commands,
                        subproof_diffs: vec![None; n],
                        visited,
                        index_of_subproof: current,
                    };
                    stack.push(frame);
                    to_visit.push(new_queue);
                }
                ProofCommand::Closing => {}
            }
        }
        to_visit.pop();
        let mut frame = stack.pop().unwrap();

        let mut result_diff = Vec::new();
        let mut new_indices = Vec::new();
        let mut num_pruned = 0;
        let depth = stack.len();
        for i in 0..frame.commands.len() {
            new_indices.push((depth, i - num_pruned));

            if !frame.visited[i] {
                result_diff.push((i, CommandDiff::Delete));
                num_pruned += 1;
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
