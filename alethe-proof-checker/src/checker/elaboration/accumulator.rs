use crate::ast::*;
use std::fmt::Write;

#[derive(Debug, Default)]
struct Frame {
    commands: Vec<ProofCommand>,
}

#[derive(Debug)]
pub struct Accumulator {
    stack: Vec<Frame>,
}

impl Accumulator {
    pub fn new() -> Self {
        Self { stack: vec![Frame::default()] }
    }

    fn top_frame(&self) -> &Frame {
        self.stack.last().unwrap()
    }

    fn top_frame_mut(&mut self) -> &mut Frame {
        self.stack.last_mut().unwrap()
    }

    pub fn depth(&self) -> usize {
        self.stack.len() - 1
    }

    pub fn top_frame_len(&self) -> usize {
        self.top_frame().commands.len()
    }

    pub fn next_id(&self, root_id: &str) -> String {
        let mut current = root_id.to_owned();
        for f in &self.stack {
            write!(&mut current, ".t{}", f.commands.len() + 1).unwrap();
        }
        current
    }

    pub fn push_command(&mut self, command: ProofCommand) {
        self.top_frame_mut().commands.push(command);
    }

    pub fn open_subproof(&mut self) {
        self.stack.push(Frame::default());
    }

    pub fn close_subproof(
        &mut self,
        assignment_args: Vec<(String, Rc<Term>)>,
        variable_args: Vec<SortedVar>,
    ) -> ProofCommand {
        let commands = self.stack.pop().unwrap().commands;
        ProofCommand::Subproof(Subproof {
            commands,
            assignment_args,
            variable_args,
        })
    }

    pub fn drop_subproof(&mut self) {
        self.stack.pop();
    }

    pub fn end(mut self) -> Vec<ProofCommand> {
        assert!(self.depth() == 0);
        self.stack.pop().unwrap().commands
    }
}

impl Default for Accumulator {
    fn default() -> Self {
        Self::new()
    }
}
