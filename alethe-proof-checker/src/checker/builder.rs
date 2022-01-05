use crate::ast::*;

#[derive(Debug, Default)]
struct Frame {
    subproof: Subproof,
    new_indices: Vec<usize>,
    current_offset: usize,
}

#[derive(Debug)]
pub struct ProofBuilder {
    stack: Vec<Frame>,
}

impl Default for ProofBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl ProofBuilder {
    pub fn new() -> Self {
        Self { stack: vec![Frame::default()] }
    }

    /// Maps the index of a command in the original proof to the index of that command in the
    /// reconstructed proof, taking into account the offset created by new steps introduced.
    pub(super) fn map_index(&self, (depth, i): (usize, usize)) -> (usize, usize) {
        (depth, self.stack[depth].new_indices[i])
    }

    /// Maps all the premises of `s` to reference the correct commaand indices in the reconstructed
    /// proof.
    pub(super) fn map_all_premises(&self, s: &mut ProofStep) {
        for p in s.premises.iter_mut() {
            *p = self.map_index(*p)
        }
    }

    /// Pushes a new command into the reconstructed proof. If the given command does not correspond
    /// to a command in the original proof (and is therefore completely new), `is_new` should be
    /// `true`.
    // TODO: Rename this to be consistent with `add_step`
    pub(super) fn push_command(&mut self, command: ProofCommand, is_new: bool) -> (usize, usize) {
        let frame = &mut self.stack.last_mut().unwrap();
        if is_new {
            frame.current_offset += 1;
        } else {
            let new_index = frame.new_indices.len() + frame.current_offset;
            frame.new_indices.push(new_index);
        }
        let index = frame.subproof.commands.len();
        frame.subproof.commands.push(command);
        (self.stack.len() - 1, index)
    }

    /// Pushes a step into the reconstructed proof. If the given step does not correspond to a step
    /// in the original proof (and is therefore completely new), `is_new` should be `true`. This
    /// method assumes all premises in `step` already reference indices is the reconstructed proof.
    pub(super) fn add_step(&mut self, step: ProofStep, is_new: bool) -> (usize, usize) {
        self.push_command(ProofCommand::Step(step), is_new)
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
        self.add_step(step, true)
    }

    pub(super) fn open_subproof(
        &mut self,
        assignment_args: Vec<(String, Rc<Term>)>,
        variable_args: Vec<SortedVar>,
    ) {
        self.stack.push(Frame {
            subproof: Subproof {
                commands: Vec::new(),
                assignment_args,
                variable_args,
            },
            new_indices: Vec::new(),
            current_offset: 0,
        })
    }

    pub(super) fn close_subproof(&mut self) {
        if self.stack.len() == 1 {
            return; // Can't close root subproof
        }
        let command = ProofCommand::Subproof(self.stack.pop().unwrap().subproof);
        self.push_command(command, false);
    }

    pub(super) fn end(&mut self) -> Vec<ProofCommand> {
        self.stack
            .pop()
            .expect("trying to end proof building before closing subproof")
            .subproof
            .commands
    }
}
