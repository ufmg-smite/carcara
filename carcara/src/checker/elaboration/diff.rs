use crate::ast::*;
use std::{iter, vec};

#[derive(Debug, Clone, Default, PartialEq)]
pub struct ProofDiff {
    pub commands: Vec<(usize, CommandDiff)>,
    pub new_indices: Vec<(usize, usize)>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum CommandDiff {
    Step(Vec<ProofCommand>),
    Subproof(ProofDiff),
    Delete,
}

pub fn apply_diff(root: ProofDiff, proof: Vec<ProofCommand>) -> Vec<ProofCommand> {
    struct Frame {
        result: Subproof,
        commands: iter::Enumerate<vec::IntoIter<ProofCommand>>,
        diff_iter: vec::IntoIter<(usize, CommandDiff)>,
        new_indices: Vec<(usize, usize)>,
    }
    let mut stack = vec![Frame {
        result: Subproof::default(),
        commands: proof.into_iter().enumerate(),
        diff_iter: root.commands.into_iter(),
        new_indices: root.new_indices,
    }];

    loop {
        let f = stack.last_mut().unwrap();
        let Some((i, mut command)) = f.commands.next() else {
            let result = stack.pop().unwrap().result;
            if let Some(outer_frame) = stack.last_mut() {
                outer_frame
                    .result
                    .commands
                    .push(ProofCommand::Subproof(result));
                continue;
            } else {
                return result.commands;
            }
        };

        match f.diff_iter.as_slice().first() {
            Some((j, _)) if i == *j => {
                let (_, command_diff) = f.diff_iter.next().unwrap();
                match (command, command_diff) {
                    (ProofCommand::Subproof(mut subproof), CommandDiff::Subproof(diff)) => {
                        let commands = std::mem::take(&mut subproof.commands);
                        let new_frame = Frame {
                            result: subproof,
                            commands: commands.into_iter().enumerate(),
                            diff_iter: diff.commands.into_iter(),
                            new_indices: diff.new_indices,
                        };
                        stack.push(new_frame);
                    }
                    (
                        ProofCommand::Step(_) | ProofCommand::Assume { .. },
                        CommandDiff::Step(mut elaboration),
                    ) => {
                        f.result.commands.append(&mut elaboration);
                    }
                    (_, CommandDiff::Delete) => (),
                    _ => panic!("invalid diff!"),
                }
            }
            _ => {
                if let ProofCommand::Step(s) = &mut command {
                    for p in &mut s.premises {
                        let (depth, i) = *p;
                        *p = stack[depth].new_indices[i];
                    }
                }
                stack.last_mut().unwrap().result.commands.push(command);
            }
        }
    }
}
