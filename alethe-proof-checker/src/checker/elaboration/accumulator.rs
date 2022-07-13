use crate::ast::*;

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
        self.stack.len()
    }

    pub fn top_frame_len(&self) -> usize {
        self.top_frame().commands.len()
    }

    pub fn push_command(&mut self, command: ProofCommand) {
        self.top_frame_mut().commands.push(command);
    }

    #[allow(dead_code)]
    pub fn open_subproof(&mut self) {
        self.stack.push(Frame::default());
    }

    #[allow(dead_code)]
    pub fn close_subproof(
        &mut self,
        assignment_args: Vec<(String, Rc<Term>)>,
        variable_args: Vec<SortedVar>,
    ) {
        let commands = self.stack.pop().unwrap().commands;
        let subproof = Subproof {
            commands,
            assignment_args,
            variable_args,
        };
        self.push_command(ProofCommand::Subproof(subproof));
    }

    pub fn end(mut self) -> Vec<ProofCommand> {
        assert!(self.depth() == 1);
        self.stack.pop().unwrap().commands
    }
}

impl Default for Accumulator {
    fn default() -> Self {
        Self::new()
    }
}
