use crate::ast::*;

// TODO: The proof reconstruction currently creates invalid premise references. We need to update
// the premise indices that reference steps that were reconstructed into more than one step.

#[derive(Debug)]
pub struct ProofBuilder {
    stack: Vec<Subproof>,
}

impl Default for ProofBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl ProofBuilder {
    pub fn new() -> Self {
        let root = Subproof {
            commands: Vec::new(),
            assignment_args: Vec::new(),
            variable_args: Vec::new(),
        };
        Self { stack: vec![root] }
    }

    pub(super) fn push_command(&mut self, command: ProofCommand) -> (usize, usize) {
        let current_subproof_commands = &mut self.stack.last_mut().unwrap().commands;
        let index = current_subproof_commands.len();
        current_subproof_commands.push(command);
        (self.stack.len() - 1, index)
    }

    pub(super) fn add_step(&mut self, step: ProofStep) -> (usize, usize) {
        self.push_command(ProofCommand::Step(step))
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
        self.add_step(ProofStep {
            index,
            clause,
            rule: "symm".into(),
            premises: vec![original_premise],
            args: Vec::new(),
            discharge: Vec::new(),
        })
    }

    pub(super) fn open_subproof(
        &mut self,
        assignment_args: Vec<(String, Rc<Term>)>,
        variable_args: Vec<SortedVar>,
    ) {
        self.stack.push(Subproof {
            commands: Vec::new(),
            assignment_args,
            variable_args,
        })
    }

    pub(super) fn close_subproof(&mut self) {
        if self.stack.len() == 1 {
            return; // Can't close root subproof
        }
        let command = ProofCommand::Subproof(self.stack.pop().unwrap());
        self.push_command(command);
    }

    pub(super) fn end(&mut self) -> Vec<ProofCommand> {
        self.stack
            .pop()
            .expect("trying to end proof building before closing subproof")
            .commands
    }
}
