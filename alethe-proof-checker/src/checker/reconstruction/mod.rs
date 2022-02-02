mod diff;
mod pruning;

use crate::{ast::*, utils::SymbolTable};
use diff::{apply_diff, CommandDiff, ProofDiff};
use pruning::prune_proof;

#[derive(Debug, Default)]
struct Frame {
    diff: Vec<(usize, CommandDiff)>,
    new_indices: Vec<(usize, usize)>,
    current_offset: isize,
    subproof_length: usize,
}

#[derive(Debug)]
pub struct Reconstructor {
    stack: Vec<Frame>,
    seen_clauses: SymbolTable<Vec<Rc<Term>>, usize>,
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
            seen_clauses: SymbolTable::new(),
        }
    }

    fn top_frame(&mut self) -> &mut Frame {
        self.stack.last_mut().unwrap()
    }

    /// Maps the index of a command in the original proof to the index of that command in the
    /// reconstructed proof, taking into account the offset created by new steps introduced.
    pub(super) fn map_index(&self, (depth, i): (usize, usize)) -> (usize, usize) {
        self.stack[depth].new_indices[i]
    }

    pub(super) fn add_new_step(&mut self, step: ProofStep) -> (usize, usize) {
        if let Some((d, &i)) = self.seen_clauses.get_with_depth(&step.clause) {
            return (d, i);
        }

        let frame = self.top_frame();
        let index = (frame.new_indices.len() as isize + frame.current_offset) as usize;
        frame.current_offset += 1;
        self.seen_clauses.insert(step.clause.clone(), index);
        self.accumulator.push(ProofCommand::Step(step));
        (self.stack.len() - 1, index)
    }

    pub(super) fn get_new_id(&mut self, root_id: &str) -> String {
        format!("{}.t{}", root_id, self.accumulator.len() + 1)
    }

    pub(super) fn push_reconstructed_step(&mut self, step: ProofStep) -> (usize, usize) {
        let reconstruction = {
            let mut added = std::mem::take(&mut self.accumulator);
            added.push(ProofCommand::Step(step));
            CommandDiff::Step(added)
        };

        let depth = self.stack.len() - 1;
        let frame = self.top_frame();
        let old_index = frame.new_indices.len();
        let new_index = (old_index as isize + frame.current_offset) as usize;
        frame.new_indices.push((depth, new_index));

        frame.diff.push((old_index, reconstruction));

        (self.stack.len() - 1, new_index)
    }

    pub(super) fn signal_unchanged(&mut self, clause: &[Rc<Term>]) {
        let depth = self.stack.len() - 1;
        let frame = self.top_frame();
        let old_index = frame.new_indices.len();
        let new_index = (old_index as isize + frame.current_offset) as usize;
        frame.new_indices.push((depth, new_index));

        if let Some((depth, &index)) = self.seen_clauses.get_with_depth(clause) {
            // If this command is the second to last in a subproof, it may be implicitly used by the
            // last step in the subproof, so we cannot delete it
            if old_index + 2 != self.top_frame().subproof_length {
                // We must also consider the edge case when the current step closes a subproof that
                // is itself the second to last command in an outer subproof. If we delete this
                // step, the inner subproof will also be deleted, which will invalidate the implicit
                // reference used in the last step of the outer subproof
                let closes_subproof_that_must_be_kept = if depth >= 2 {
                    let outer_frame = &self.stack[depth - 1];
                    let index_in_outer = outer_frame.new_indices.len();
                    index_in_outer + 2 == outer_frame.subproof_length
                } else {
                    false
                };
                if !closes_subproof_that_must_be_kept {
                    let frame = self.top_frame();
                    frame.new_indices[old_index] = (depth, index);
                    frame.diff.push((old_index, CommandDiff::Delete));
                    frame.current_offset -= 1;
                }
            }
        } else {
            self.seen_clauses.insert(clause.to_vec(), new_index);
        }
    }

    pub(super) fn add_symm_step(
        &mut self,
        pool: &mut TermPool,
        original_premise: (usize, usize),
        original_equality: (Rc<Term>, Rc<Term>),
        id: String,
    ) -> (usize, usize) {
        let (a, b) = original_equality;
        let clause = vec![build_term!(pool, (= {b} {a}))];
        let step = ProofStep {
            id,
            clause,
            rule: "symm".into(),
            premises: vec![self.map_index(original_premise)],
            args: Vec::new(),
            discharge: Vec::new(),
        };
        self.add_new_step(step)
    }

    pub(super) fn open_subproof(&mut self, length: usize) {
        self.seen_clauses.push_scope();
        self.stack.push(Frame {
            diff: Vec::new(),
            new_indices: Vec::new(),
            current_offset: 0,
            subproof_length: length,
        });
    }

    pub(super) fn close_subproof(&mut self) {
        self.seen_clauses.pop_scope();
        let inner = self.stack.pop().expect("can't close root subproof");

        let depth = self.stack.len() - 1;
        let frame = self.top_frame();
        let old_index = frame.new_indices.len();
        let new_index = (old_index as isize + frame.current_offset) as usize;
        frame.new_indices.push((depth, new_index));

        let last_command_index = inner.new_indices.len() - 1;
        let diff = if inner.diff.last() == Some(&(last_command_index, CommandDiff::Delete)) {
            CommandDiff::Delete
        } else {
            // Even if the subproof diff is empty, we still need to update the indices of the
            // premises of steps inside the subproof, so we push a `CommandDiff` anyway
            CommandDiff::Subproof(ProofDiff {
                commands: inner.diff,
                new_indices: inner.new_indices,
            })
        };
        frame.diff.push((old_index, diff));
    }

    pub(super) fn end(&mut self, original: Vec<ProofCommand>) -> Vec<ProofCommand> {
        if self.stack.len() != 1 {
            panic!("trying to end proof building before closing subproof");
        }
        let Frame { diff, new_indices, .. } = self.stack.pop().unwrap();
        let diff = ProofDiff { commands: diff, new_indices };
        let reconstructed = apply_diff(diff, original);
        apply_diff(prune_proof(&reconstructed), reconstructed)
    }
}
