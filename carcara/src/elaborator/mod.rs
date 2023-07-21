mod accumulator;
mod diff;
mod polyeq;
mod pruning;

pub use diff::{apply_diff, CommandDiff, ProofDiff};
pub use pruning::{prune_proof, slice_proof};

use crate::{ast::*, utils::HashMapStack};
use accumulator::Accumulator;
use polyeq::PolyeqElaborator;

#[derive(Debug, Default)]
struct Frame {
    diff: Vec<(usize, CommandDiff)>,
    new_indices: Vec<(usize, usize)>,
    current_offset: isize,
    subproof_length: usize,
}

impl Frame {
    fn current_index(&self) -> usize {
        self.new_indices.len()
    }

    fn push_new_index(&mut self, current_depth: usize) -> (usize, usize) {
        let old_index = self.current_index();
        let new_index = (self.current_index() as isize + self.current_offset) as usize;
        self.new_indices.push((current_depth, new_index));
        (old_index, new_index)
    }
}

#[derive(Debug)]
pub struct Elaborator {
    stack: Vec<Frame>,
    seen_clauses: HashMapStack<Vec<Rc<Term>>, usize>,
    accumulator: Accumulator,
}

impl Default for Elaborator {
    fn default() -> Self {
        Self::new()
    }
}

impl Elaborator {
    pub fn new() -> Self {
        Self {
            stack: vec![Frame::default()],
            accumulator: Accumulator::new(),
            seen_clauses: HashMapStack::new(),
        }
    }

    fn top_frame(&self) -> &Frame {
        self.stack.last().unwrap()
    }

    fn top_frame_mut(&mut self) -> &mut Frame {
        self.stack.last_mut().unwrap()
    }

    fn depth(&self) -> usize {
        self.stack.len() - 1
    }

    /// Returns `true` if the command on the current frame at index `index` cannot be deleted.
    fn must_keep(&self, index: usize) -> bool {
        // If the command is the second to last in a subproof, it may be implicitly used by the last
        // step in the subproof, so we cannot delete it
        if index + 2 == self.top_frame().subproof_length {
            return true;
        }

        // We must also consider the edge case when the step closes a subproof that
        // is itself the second to last command in an outer subproof. If we delete this
        // step, the inner subproof will also be deleted, which will invalidate the implicit
        // reference used in the last step of the outer subproof
        let depth = self.depth();
        if depth >= 2 {
            let outer_frame = &self.stack[depth - 1];
            let index_in_outer = outer_frame.current_index();
            index_in_outer + 2 == outer_frame.subproof_length
        } else {
            false
        }
    }

    /// Maps the index of a command in the original proof to the index of that command in the
    /// elaborated proof, taking into account the offset created by new steps introduced.
    pub fn map_index(&self, (depth, i): (usize, usize)) -> (usize, usize) {
        self.stack[depth].new_indices[i]
    }

    pub fn add_new_command(&mut self, command: ProofCommand, must_keep: bool) -> (usize, usize) {
        if !must_keep {
            if let Some((d, &i)) = self.seen_clauses.get_with_depth(command.clause()) {
                return (d, i);
            }
        }

        let index = if self.accumulator.depth() == 0 {
            let frame = self.top_frame_mut();
            frame.current_offset += 1;
            (frame.new_indices.len() as isize + frame.current_offset - 1) as usize
        } else {
            self.accumulator.top_frame_len()
        };
        self.seen_clauses.insert(command.clause().to_vec(), index);
        self.accumulator.push_command(command);
        (self.depth() + self.accumulator.depth(), index)
    }

    pub fn add_new_step(&mut self, step: ProofStep) -> (usize, usize) {
        self.add_new_command(ProofCommand::Step(step), false)
    }

    pub fn get_new_id(&mut self, root_id: &str) -> String {
        self.accumulator.next_id(root_id)
    }

    pub fn push_elaborated_step(&mut self, step: ProofStep) -> (usize, usize) {
        // TODO: discard elaborated steps that introduce already seen conclusions (and can be
        // deleted)

        let clause = step.clause.clone();
        let elaboration = {
            let mut added = std::mem::take(&mut self.accumulator).end();
            added.push(ProofCommand::Step(step));
            CommandDiff::Step(added)
        };

        let depth = self.depth();
        let frame = self.top_frame_mut();
        let (old_index, new_index) = frame.push_new_index(depth);

        frame.diff.push((old_index, elaboration));

        self.seen_clauses.insert(clause, new_index);
        (self.depth(), new_index)
    }

    pub fn open_accumulator_subproof(&mut self) {
        self.seen_clauses.push_scope();
        self.accumulator.open_subproof();
    }

    /// Closes a subproof in the accumulator. This method will overwrite the `id` in `end_step`, to
    /// make sure it is the next `id` in the outer subproof.
    pub fn close_accumulator_subproof(
        &mut self,
        assignment_args: Vec<(String, Rc<Term>)>,
        variable_args: Vec<SortedVar>,
        end_step: ProofStep,
        root_id: &str,
    ) -> (usize, usize) {
        self.seen_clauses.pop_scope();

        // If the end step clause was already seen, we must skip the subproof as a whole, and not
        // just the end step itself
        if let Some((d, &i)) = self.seen_clauses.get_with_depth(&end_step.clause) {
            self.accumulator.drop_subproof();
            return (d, i);
        }
        self.add_new_step(end_step);
        let s = self
            .accumulator
            .close_subproof(assignment_args, variable_args, root_id);
        self.add_new_command(s, true)
    }

    fn push_command(&mut self, clause: &[Rc<Term>], is_assume: bool) {
        let depth = self.depth();
        let frame = self.top_frame_mut();
        let (old_index, new_index) = frame.push_new_index(depth);

        if let Some((depth, &index)) = self.seen_clauses.get_with_depth(clause) {
            let must_keep = self.must_keep(old_index) || is_assume && depth > 0;
            if !must_keep {
                let frame = self.top_frame_mut();
                frame.new_indices[old_index] = (depth, index);
                frame.diff.push((old_index, CommandDiff::Delete));
                frame.current_offset -= 1;
            }
        } else {
            self.seen_clauses.insert(clause.to_vec(), new_index);
        }
    }

    pub fn assume(&mut self, term: &Rc<Term>) {
        self.push_command(std::slice::from_ref(term), true);
    }

    pub fn unchanged(&mut self, clause: &[Rc<Term>]) {
        self.push_command(clause, false);
    }

    /// Adds a `symm` step that flips the equality of the given premise. The `original_premise`
    /// index must already be mapped to the new index space.
    pub fn add_symm_step(
        &mut self,
        pool: &mut dyn TPool,
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
            premises: vec![original_premise],
            args: Vec::new(),
            discharge: Vec::new(),
        };
        self.add_new_step(step)
    }

    /// Adds a `refl` step that asserts that the two given terms are equal.
    pub fn add_refl_step(
        &mut self,
        pool: &mut dyn TPool,
        a: Rc<Term>,
        b: Rc<Term>,
        id: String,
    ) -> (usize, usize) {
        let step = ProofStep {
            id,
            clause: vec![build_term!(pool, (= {a} {b}))],
            rule: "refl".into(),
            premises: Vec::new(),
            args: Vec::new(),
            discharge: Vec::new(),
        };
        self.add_new_step(step)
    }

    pub fn elaborate_polyeq(
        &mut self,
        pool: &mut dyn TPool,
        root_id: &str,
        a: Rc<Term>,
        b: Rc<Term>,
        is_alpha_equivalence: bool,
    ) -> (usize, usize) {
        PolyeqElaborator::new(self, root_id, is_alpha_equivalence).elaborate(pool, a, b)
    }

    pub fn elaborate_assume(
        &mut self,
        pool: &mut dyn TPool,
        premise: Rc<Term>,
        term: Rc<Term>,
        id: &str,
    ) -> (usize, usize) {
        let new_assume = self.add_new_command(
            ProofCommand::Assume {
                id: id.to_owned(),
                term: premise.clone(),
            },
            false,
        );
        let equality_step = self.elaborate_polyeq(pool, id, premise.clone(), term.clone(), false);
        let equiv1_step = {
            let new_id = self.get_new_id(id);
            let clause = vec![build_term!(pool, (not {premise.clone()})), term.clone()];
            self.add_new_step(ProofStep {
                id: new_id,
                clause,
                rule: "equiv1".to_owned(),
                premises: vec![equality_step],
                args: Vec::new(),
                discharge: Vec::new(),
            })
        };

        let new_id = self.get_new_id(id);
        self.push_elaborated_step(ProofStep {
            id: new_id,
            clause: vec![term],
            rule: "resolution".to_owned(),
            premises: vec![new_assume, equiv1_step],
            args: vec![ProofArg::Term(premise), ProofArg::Term(pool.bool_true())],
            discharge: Vec::new(),
        })
    }

    pub fn open_subproof(&mut self, length: usize) {
        self.seen_clauses.push_scope();
        self.stack.push(Frame {
            diff: Vec::new(),
            new_indices: Vec::new(),
            current_offset: 0,
            subproof_length: length,
        });
    }

    pub fn close_subproof(&mut self) {
        self.seen_clauses.pop_scope();
        let inner = self.stack.pop().expect("can't close root subproof");

        let depth = self.depth();
        let frame = self.top_frame_mut();
        let (old_index, _) = frame.push_new_index(depth);

        let last_command_index = inner.current_index() - 1;
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

    pub fn end(&mut self, original: Vec<ProofCommand>) -> Vec<ProofCommand> {
        assert!(
            self.depth() == 0,
            "trying to end proof building before closing subproof"
        );
        let Frame { diff, new_indices, .. } = self.stack.pop().unwrap();
        let diff = ProofDiff { commands: diff, new_indices };
        let elaborated = apply_diff(diff, original);
        apply_diff(prune_proof(&elaborated), elaborated)
    }
}
