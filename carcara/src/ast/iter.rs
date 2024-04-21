//! This module implements `ProofIter`, an iterator that recursively iterates over the proof
//! commands in a proof.

use std::borrow::Borrow;

use super::*;

/// An iterator over the proof commands in a proof.
///
/// This struct traverses the proof recursively, yielding all proof commands in order. When
/// encountering a subproof, the iterator first yields the `ProofCommand::Subproof`, and then
/// iterates through the subproofs commands.
///
/// This struct is created by the [`iter`](Proof::iter) method on proofs.
///
/// # Examples
///
/// ```
/// # use carcara::*;
/// # fn main() -> CarcaraResult<()> {
/// let proof = "
///     (assume h1 (forall ((x Int)) (> x 0)))
///     (assume h2 (not (forall ((y Int)) (> y 0))))
///     (anchor :step t3 :args ((y Int) (:= (x Int) y)))
///     (step t3.t1 (cl (= x y)) :rule refl)
///     (step t3.t2 (cl (= (> x 0) (> y 0))) :rule cong :premises (t3.t1))
///     (step t3 (cl (= (forall ((x Int)) (> x 0)) (forall ((y Int)) (> y 0)))) :rule bind)
///     (step t4 (cl (not (forall ((x Int)) (> x 0))) (forall ((y Int)) (> y 0)))
///         :rule equiv1 :premises (t3))
///     (step t5 (cl) :rule resolution :premises (t4 h1 h2))
/// "
/// .as_bytes();
/// let (_, proof, _, _) = parser::parse_instance("".as_bytes(), proof, parser::Config::new())?;
/// let ids: Vec<_> = proof.iter().map(|c| c.id()).collect();
/// assert_eq!(ids, ["h1", "h2", "t3", "t3.t1", "t3.t2", "t3", "t4", "t5"]);
/// # Ok(())
/// # }
/// ```
pub struct ProofIter<'a> {
    stack: Vec<(usize, &'a [ProofCommand])>,
}

impl<'a> ProofIter<'a> {
    /// Constructs a new `ProofIter`, given a slice of proof commands.
    pub(super) fn new(commands: &'a [ProofCommand]) -> Self {
        Self { stack: vec![(0, commands)] }
    }

    /// Returns the current nesting depth of the iterator, or more precisely, the nesting depth of
    /// the last command that was returned. This depth starts at zero, for commands in the root
    /// proof.
    pub fn depth(&self) -> usize {
        self.stack.len() - 1
    }

    /// Returns `true` if the iterator is currently in a subproof, that is, if its depth is greater
    /// than zero.
    pub fn is_in_subproof(&self) -> bool {
        self.depth() > 0
    }

    /// Returns a slice to the commands of the inner-most open subproof.
    pub fn current_subproof(&self) -> Option<&[ProofCommand]> {
        self.is_in_subproof().then(|| self.stack.last().unwrap().1)
    }

    /// Returns `true` if the last command that was returned was the end step of the current
    /// subproof.
    pub fn is_end_step(&self) -> bool {
        self.is_in_subproof() && {
            let &(i, commands) = self.stack.last().unwrap();
            i == commands.len()
        }
    }

    /// Returns the command referenced by a premise index of the form (depth, index in subproof).
    /// This method may panic if the premise index does not refer to a valid command.
    pub fn get_premise(&self, (depth, index): (usize, usize)) -> &ProofCommand {
        &self.stack[depth].1[index]
    }

    /// Returns the id of the command
    /// This method may panic if the premise index does not refer to a valid command.
    pub fn get_premise_id(&self, (depth, index): (usize, usize)) -> String {
        match self.stack[depth].1[index].borrow() {
            ProofCommand::Assume { id, .. } => id.to_string(),
            ProofCommand::Step(ProofStep { id, .. }) => id.to_string(),
            ProofCommand::Subproof(Subproof { commands, .. }) => {
                commands.last().unwrap().id().to_string()
            }
        }
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
