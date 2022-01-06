use crate::ast::*;

#[derive(Debug)]
pub enum CommandDiff {
    Step(Vec<ProofCommand>),
    Subproof(ProofDiff),
}

#[derive(Debug, Default)]
pub struct ProofDiff {
    pub commands: Vec<(usize, CommandDiff)>,
    pub new_indices: Vec<usize>,
}

pub fn apply_diff(root: ProofDiff, proof: Vec<ProofCommand>) -> Vec<ProofCommand> {
    struct Frame {
        result: Subproof,
        commands: std::iter::Enumerate<std::vec::IntoIter<ProofCommand>>,
        diff_iter: std::vec::IntoIter<(usize, CommandDiff)>,
        new_indices: Vec<usize>,
    }
    let mut stack = vec![Frame {
        result: Subproof::default(),
        commands: proof.into_iter().enumerate(),
        diff_iter: root.commands.into_iter(),
        new_indices: root.new_indices,
    }];
    loop {
        let f = stack.last_mut().unwrap();
        let (i, command) = match f.commands.next() {
            Some(c) => c,
            None => {
                let result = stack.pop().unwrap().result;
                if stack.is_empty() {
                    return result.commands;
                }
                stack
                    .last_mut()
                    .unwrap()
                    .result
                    .commands
                    .push(ProofCommand::Subproof(result));
                continue;
            }
        };

        match f.diff_iter.as_slice().first() {
            Some((j, _)) if i == *j => {
                let (_, reconstructed) = f.diff_iter.next().unwrap();
                match (command, reconstructed) {
                    (ProofCommand::Subproof(subproof), CommandDiff::Subproof(diff)) => {
                        let result = Subproof {
                            commands: Vec::new(),
                            assignment_args: subproof.assignment_args,
                            variable_args: subproof.variable_args,
                        };
                        let new_frame = Frame {
                            result,
                            commands: subproof.commands.into_iter().enumerate(),
                            diff_iter: diff.commands.into_iter(),
                            new_indices: diff.new_indices,
                        };
                        stack.push(new_frame);
                    }
                    (ProofCommand::Step(_), CommandDiff::Step(mut reconstructed)) => {
                        f.result.commands.append(&mut reconstructed);
                    }
                    _ => panic!("invalid diff!"),
                }
            }
            _ => {
                let mut command = command;
                if let ProofCommand::Step(s) = &mut command {
                    for p in s.premises.iter_mut() {
                        let (depth, i) = *p;
                        *p = (depth, stack[depth].new_indices[i]);
                    }
                }
                stack.last_mut().unwrap().result.commands.push(command);
            }
        }
    }
}
