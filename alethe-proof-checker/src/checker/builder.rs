use crate::ast::*;

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

    pub(super) fn push_command(&mut self, command: ProofCommand) {
        self.stack.last_mut().unwrap().commands.push(command)
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
        self.push_command(command)
    }

    pub(super) fn end(&mut self) -> Vec<ProofCommand> {
        self.stack
            .pop()
            .expect("trying to end proof building before closing subproof")
            .commands
    }
}
