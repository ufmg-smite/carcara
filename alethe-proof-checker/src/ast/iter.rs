// TODO: Add documentation to this module

use super::*;

pub struct ProofIter<'a> {
    stack: Vec<(usize, &'a [ProofCommand])>,
}

impl<'a> ProofIter<'a> {
    pub fn new(commands: &'a [ProofCommand]) -> Self {
        Self { stack: vec![(0, commands)] }
    }

    pub fn is_in_subproof(&self) -> bool {
        // The root proof is considered a nesting depth of 0
        self.stack.len() > 1
    }

    pub fn is_end_step(&self) -> bool {
        self.is_in_subproof() && {
            let &(i, commands) = self.stack.last().unwrap();
            i == commands.len()
        }
    }

    pub fn current_subproof(&self) -> Option<&[ProofCommand]> {
        self.is_in_subproof().then(|| self.stack.last().unwrap().1)
    }
}

impl<'a> Iterator for ProofIter<'a> {
    type Item = &'a ProofCommand;

    fn next(&mut self) -> Option<Self::Item> {
        let (i, commands) = self.stack.last_mut()?;
        if *i == commands.len() {
            if self.is_in_subproof() {
                self.stack.pop();
                self.next()
            } else {
                None
            }
        } else {
            *i += 1;
            let command = &commands[*i - 1];
            if let ProofCommand::Subproof(subproof) = command {
                self.stack.push((0, &subproof.commands));
            }
            Some(command)
        }
    }
}
