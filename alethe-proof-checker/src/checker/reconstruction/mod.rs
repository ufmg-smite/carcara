mod diff;

use crate::ast::*;
use diff::{apply_diff, CommandDiff, ProofDiff};

#[derive(Debug, Default)]
struct Frame {
    diff: Vec<(usize, CommandDiff)>,
    new_indices: Vec<usize>,
    current_offset: usize,
}

#[derive(Debug)]
pub struct Reconstructor {
    stack: Vec<Frame>,
    accumulator: Vec<ProofCommand>,
}

impl Default for Reconstructor {
    fn default() -> Self {
        Self::new()
    }
}

impl Reconstructor {
    pub fn new() -> Self {
        Self {
            stack: vec![Frame::default()],
            accumulator: Vec::new(),
        }
    }

    fn top_frame(&mut self) -> &mut Frame {
        self.stack.last_mut().unwrap()
    }

    /// Maps the index of a command in the original proof to the index of that command in the
    /// reconstructed proof, taking into account the offset created by new steps introduced.
    pub(super) fn map_index(&self, (depth, i): (usize, usize)) -> (usize, usize) {
        (depth, self.stack[depth].new_indices[i])
    }

    pub(super) fn add_new_step(&mut self, step: ProofStep) -> (usize, usize) {
        let frame = self.top_frame();
        let index = frame.new_indices.len() + frame.current_offset;
        frame.current_offset += 1;
        self.accumulator.push(ProofCommand::Step(step));
        (self.stack.len() - 1, index)
    }

    pub(super) fn get_new_index(&mut self, root_index: &str) -> String {
        format!("{}.t{}", root_index, self.accumulator.len() + 1)
    }

    pub(super) fn push_reconstructed_step(&mut self, step: ProofStep) -> (usize, usize) {
        let reconstruction = {
            let mut added = std::mem::take(&mut self.accumulator);
            added.push(ProofCommand::Step(step));
            CommandDiff::Step(added)
        };

        let frame = self.top_frame();
        let old_index = frame.new_indices.len();
        let new_index = old_index + frame.current_offset;
        frame.new_indices.push(new_index);

        frame.diff.push((old_index, reconstruction));

        (self.stack.len() - 1, new_index)
    }

    pub(super) fn signal_unchanged(&mut self) {
        let frame = self.top_frame();
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
        });
    }

    pub(super) fn close_subproof(&mut self) {
        let Frame { diff, new_indices, .. } = self.stack.pop().expect("can't close root subproof");

        let frame = self.top_frame();
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
            panic!("trying to end proof building before closing subproof");
        }
        let Frame { diff, new_indices, .. } = self.stack.pop().unwrap();
        let diff = ProofDiff { commands: diff, new_indices };
        apply_diff(diff, original)
    }
}
