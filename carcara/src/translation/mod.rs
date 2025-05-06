/// Translation of Alethe proofs services.
pub mod eunoia;

use crate::ast::*;

// Deref for ast::rc::Rc<Term>
use std::ops::Deref;
// scopes
use crate::utils::HashMapStack;

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

/// Generic representation of scopes of variables introduced by the several
/// Alethe constructions with binding occurrences: contexts, quantifications,
/// lets, etc. It must be instantiated for a given type of values that we want
/// to associate with each variable in scope.
struct AletheScopes<T: Clone> {
    /// Mapping variable -> sort for variables in scope, as introduced by
    /// Alethe's binders (including contexts).
    // TODO: would it be useful to use borrows?
    // TODO: not taking into account fixed variables in context
    variables_in_scope: HashMapStack<String, T>,

    /// Flags that indicate if the context of a given index has been
    /// actually introduced in the certificate through an Eunoia definition.
    context_introduced: Vec<bool>,

    /// Counter for contexts opened: useful for naming context and reasoning
    /// about context opening.
    contexts_opened: usize,
}

impl<T: Clone> AletheScopes<T> {
    pub fn new() -> Self {
        Self {
            variables_in_scope: HashMapStack::new(),
            context_introduced: Vec::new(),
            contexts_opened: 0,
        }
    }

    /// Abstracts the operations required for opening a new context scope.
    pub fn open_context_scope(&mut self) {
        self.open_scope(true);
    }

    /// Abstracts the operations required for opening a new scope introduced
    /// by some binder different than a context.
    pub fn open_non_context_scope(&mut self) {
        self.open_scope(false);
    }

    pub fn get_contexts_opened(&self) -> usize {
        self.contexts_opened
    }

    pub fn clean_scopes(&mut self) {
        self.variables_in_scope = HashMapStack::new();
        self.context_introduced = Vec::new();
        self.contexts_opened = 0;
    }

    pub fn insert_variable_in_scope(&mut self, name: &str, value: &T) {
        self.variables_in_scope
            .insert(name.to_owned(), value.clone());
    }

    pub fn get_variable_in_scope(&self, name: &String) -> Option<&T> {
        self.variables_in_scope.get(name)
    }

    /// Abstracts the operations required for opening a new scope,
    /// once we need to translate the body of a construction with
    /// binding occurrences of variables.
    /// PARAMS:
    /// - `context_introduced`: boolean flag indicated if the opened
    ///   scope belongs to a newly introduced "context" (through "anchor").
    fn open_scope(&mut self, context_introduced: bool) {
        if context_introduced {
            self.contexts_opened += 1;
        }

        // NOTE: HashMapStack::new() adds a scope. We only push another
        // scope if this is not the first time open_scope was called, in order
        // to maintain invariant
        // self.context_introduced.len() == self.variables_in_scope.height()
        if !self.context_introduced.is_empty() {
            // NOTE: reusing variables_in_scope concept
            // for this new kind of scope (not the one
            // related with contexts introduced through
            // "anchor" commands).
            self.variables_in_scope.push_scope();
        }

        self.context_introduced.push(context_introduced);
    }

    /// Closes the last open scope.
    /// PRE : { `self.context_introduced.len()` >= 1 }
    pub fn close_scope(&mut self) {
        self.variables_in_scope.pop_scope();

        // TODO: let Some(true)?
        let context_introduced = self.context_introduced.pop();

        if context_introduced == Some(true) {
            // We are closing a context (instead of closing the scope of some other
            // binder).
            self.contexts_opened -= 1;
        }
    }

    /// For a given "nesting" level (some number <= `self.contexts_opened`),
    /// returns the index of the last surrounding context actually introduced
    /// within the proof certificate. This is so since scopes are used to
    /// represent variables bound in contexts and by other binding constructions,
    /// like quantifiers. This method helps to recover the index of the last
    /// scope actually referring to a context.
    /// PRE: { 0 < `nesting_level` < `self.contexts_opened`}
    pub fn get_last_introduced_context_index(&self, nesting_level: usize) -> usize {
        let mut last_scope: usize = 0;

        for i in 0..nesting_level {
            if self.context_introduced[nesting_level - 1 - i] {
                last_scope = nesting_level - 1 - i;
                break;
            }
        }

        last_scope
    }
}
