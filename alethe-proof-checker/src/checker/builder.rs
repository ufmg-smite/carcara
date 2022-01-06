use crate::ast::*;

#[derive(Debug)]
enum CommandDiff {
    Step(Vec<ProofCommand>),
    Subproof(ProofDiff),
}

#[derive(Debug, Default)]
struct ProofDiff {
    commands: Vec<(usize, CommandDiff)>,
    new_indices: Vec<usize>,
}

// TODO: Move this to separate submodule
fn apply_diff(root: ProofDiff, proof: Vec<ProofCommand>) -> Vec<ProofCommand> {
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

#[derive(Debug, Default)]
struct Frame {
    diff: Vec<(usize, CommandDiff)>,
    new_indices: Vec<usize>,
    current_offset: usize,
}

#[derive(Debug)]
pub struct ProofBuilder {
    stack: Vec<Frame>,
    accumulator: Vec<ProofCommand>,
}

impl Default for ProofBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl ProofBuilder {
    pub fn new() -> Self {
        Self {
            stack: vec![Frame::default()],
            accumulator: Vec::new(),
        }
    }

    /// Maps the index of a command in the original proof to the index of that command in the
    /// reconstructed proof, taking into account the offset created by new steps introduced.
    pub(super) fn map_index(&self, (depth, i): (usize, usize)) -> (usize, usize) {
        (depth, self.stack[depth].new_indices[i])
    }

    pub(super) fn add_new_step(&mut self, step: ProofStep) -> (usize, usize) {
        let frame = self.stack.last_mut().unwrap();
        let index = frame.new_indices.len() + frame.current_offset;
        frame.current_offset += 1;
        self.accumulator.push(ProofCommand::Step(step));
        (self.stack.len() - 1, index)
    }

    pub(super) fn push_reconstructed_step(&mut self, step: ProofStep) -> (usize, usize) {
        let frame = self.stack.last_mut().unwrap();
        let old_index = frame.new_indices.len();
        let new_index = old_index + frame.current_offset;
        frame.new_indices.push(new_index);

        let mut added = std::mem::take(&mut self.accumulator);
        added.push(ProofCommand::Step(step));
        frame.diff.push((old_index, CommandDiff::Step(added)));

        (self.stack.len() - 1, new_index)
    }

    pub(super) fn signal_unchanged(&mut self) {
        let frame = self.stack.last_mut().unwrap();
        let new_index = frame.new_indices.len() + frame.current_offset;
        frame.new_indices.push(new_index);
    }

    pub(super) fn add_symm_step(
        &mut self,
        pool: &mut TermPool,
        original_premise: (usize, usize),
        original_equality: (Rc<Term>, Rc<Term>),
        index: String,
    ) -> (usize, usize) {
        let (a, b) = original_equality;
        let clause = vec![build_term!(pool, (= {b} {a}))];
        let step = ProofStep {
            index,
            clause,
            rule: "symm".into(),
            premises: vec![self.map_index(original_premise)],
            args: Vec::new(),
            discharge: Vec::new(),
        };
        self.add_new_step(step)
    }

    pub(super) fn open_subproof(&mut self) {
        self.stack.push(Frame {
            diff: Vec::new(),
            new_indices: Vec::new(),
            current_offset: 0,
        })
    }

    pub(super) fn close_subproof(&mut self) {
        let Frame { diff, new_indices, .. } = self.stack.pop().expect("can't close root subproof");

        let frame = self.stack.last_mut().unwrap();
        let old_index = frame.new_indices.len();
        let new_index = old_index + frame.current_offset;
        frame.new_indices.push(new_index);

        if !diff.is_empty() {
            let diff = ProofDiff { commands: diff, new_indices };
            frame.diff.push((old_index, CommandDiff::Subproof(diff)));
        }
    }

    pub(super) fn end(&mut self, original: Vec<ProofCommand>) -> Vec<ProofCommand> {
        if self.stack.len() != 1 {
            panic!("trying to end proof building before closing subproof")
        }
        let Frame { diff, new_indices, .. } = self.stack.pop().unwrap();
        let diff = ProofDiff { commands: diff, new_indices };
        apply_diff(diff, original)
    }
}
