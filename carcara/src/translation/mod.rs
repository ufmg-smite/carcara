/// Translation of Alethe proofs services.
pub mod eunoia;

use crate::ast::*;

// Deref for ast::rc::Rc<Term>
use std::ops::Deref;

/// Interface with an Alethe proof compiler.
pub trait Translator {
    type Output;

    fn translate<'a>(&'a mut self, proof: &Rc<ProofNode>) -> &'a Self::Output;
}

/// For translation purposes, it is useful to have a pre-ordered version of the
/// proof to be translated. This struct represents that concept.
#[derive(Default)]
struct PreOrderedAletheProof {
    // TODO: declared as attributes to avoid
    // "cannot move out... a captured variable in an `FnMut` closure" errors
    // TODO: declared as Vec<ProofNode> (not using borrows) to avoid
    // error "borrowed data escapes outside of closure"
    /// Auxiliary attribute useful to maintain a pre-ordered version
    /// of the `ProofNode` graph.
    pre_ord_proof: Vec<ProofNode>,

    // TODO: this should be a variable local to post_order_to_list
    /// Depth of the previous node visited.
    previous_depth: usize,

    /// Auxiliary attribute useful to maintain a pre-ordered version
    /// of every node from a subproof with depth bigger than 1.
    pre_ord_subproofs: Vec<Vec<ProofNode>>,
}

/// Services to translate an ordinary Alethe proof into its pre-ordered version.
impl PreOrderedAletheProof {
    pub fn new(proof: &Rc<ProofNode>) -> Self {
        let mut new_pre_ord_proof = Self {
            pre_ord_proof: Vec::new(),
            previous_depth: 0,
            pre_ord_subproofs: Vec::new(),
        };

        new_pre_ord_proof.post_order_to_list(proof);

        new_pre_ord_proof
    }

    fn post_order_to_list(&mut self, proof: &Rc<ProofNode>) {
        // NOTE: need to clone ProofNodes to avoid
        // "borrowed data escapes outside of closure" error here.
        proof.traverse(|node: &Rc<ProofNode>| {
            self.node_post_order_to_list(node);
        });
    }

    // TODO: is there some practical way of doing partial application of
    // procedures? Quick fix: using attributes (aux_pre_ord_proof_node, etc)
    /// For a given &Rc<ProofNode>,
    fn node_post_order_to_list(&mut self, node: &Rc<ProofNode>) {
        match (*node).deref() {
            ProofNode::Assume { id: _, depth, .. } => {
                if *depth > self.previous_depth {
                    // A new subproof
                    // TODO: ugly
                    while self.pre_ord_subproofs.len() < *depth {
                        self.pre_ord_subproofs.push(Vec::new());
                    }

                    // { self.pre_ord_subproofs.len() == *depth }

                    self.pre_ord_subproofs[*depth - 1].push((*node).deref().clone());
                } else {
                    // TODO: abstract this last step into some procedure; it
                    // is repeated for each ProofNode case.

                    // { *depth <= self.previous_depth }
                    // We jumped out of a subproof.
                    if *depth == 0 {
                        // This is not a node from another subproof, we can
                        // safely push it into pre_ord_proof_node.
                        self.pre_ord_proof.push((*node).deref().clone());
                    } else {
                        // { *depth > 0 }
                        // We are still within some subproof
                        assert!(self.pre_ord_subproofs.len() >= *depth - 1);
                        // A node of depth "depth", always belong to
                        // subproof "depth" - 1.
                        self.pre_ord_subproofs[*depth - 1].push((*node).deref().clone());
                    }
                }

                self.previous_depth = *depth;
            }

            ProofNode::Step(StepNode { id: _, depth, .. }) => {
                if *depth > self.previous_depth {
                    // A new subproof
                    // TODO: ugly
                    while self.pre_ord_subproofs.len() < *depth {
                        self.pre_ord_subproofs.push(Vec::new());
                    }

                    // { self.pre_ord_subproofs.len() >= *depth }
                    self.pre_ord_subproofs[*depth - 1].push((*node).deref().clone());
                } else {
                    // { *depth <= self.previous_depth }
                    if *depth == 0 {
                        // This is not a node from a subproof, we can safely push it
                        // into pre_ord_proof_node.
                        self.pre_ord_proof.push((*node).deref().clone());
                    } else {
                        // { *depth > 0 }
                        // We are still within a subproof
                        assert!(self.pre_ord_subproofs.len() >= *depth);
                        self.pre_ord_subproofs[*depth - 1].push((*node).deref().clone());
                    }
                }

                self.previous_depth = *depth;
            }

            // A subproof introduced by the 'anchor' command.
            ProofNode::Subproof(SubproofNode { last_step, .. }) => {
                match (*last_step).deref() {
                    ProofNode::Step(StepNode { id: _, depth, .. }) => {
                        assert!(1 <= *depth && *depth == self.previous_depth);

                        if *depth == 1 {
                            // Outermost subproof: we return to self.pre_ord_proof
                            self.pre_ord_proof.push((*node).deref().clone());
                            self.pre_ord_proof
                                .append(&mut self.pre_ord_subproofs[*depth - 1]);
                        } else {
                            // { depth > 1 }
                            // UNSAFE
                            let (left_slice, right_slice) =
                                self.pre_ord_subproofs.split_at_mut(*depth - 1);
                            left_slice[*depth - 2].push((*node).deref().clone());
                            left_slice[*depth - 2].append(&mut right_slice[0]);
                        }

                        // Pop the subproof being closed
                        self.pre_ord_subproofs.pop();

                        // We jump out of the subproof.
                        self.previous_depth = *depth - 1;
                    }

                    _ => {
                        // It shouldn't be a ProofNode different than a Step
                        panic!();
                    }
                }
            }
        }
    }

    pub fn get_pre_ord_proof(&mut self) -> &mut Vec<ProofNode> {
        &mut self.pre_ord_proof
    }
}
