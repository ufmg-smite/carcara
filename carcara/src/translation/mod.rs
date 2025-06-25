/// Services for the translation of Alethe proofs.
pub mod eunoia;
// pub mod tstp;

use crate::ast::*;

// Deref for ast::rc::Rc<Term>
use std::ops::Deref;
// scopes
use crate::utils::HashMapStack;

// TODO: is this correct? also: pub type alias?
/// SMT-LIB version 3.0 symbol.
pub type Symbol = String;

/// Interface with an Alethe proof compiler.
pub trait Translator {
    type Output;

    /// Translates a proof in its DAG form, into some target language.
    fn translate<'a>(&'a mut self, proof: &Rc<ProofNode>) -> &'a Self::Output;

    /// Translates only an SMT-lib problem.
    fn translate_problem(&mut self, problem: &Problem) -> Self::Output;
}

/// For translation purposes, it is useful to have a pre-ordered version of the
/// proof to be translated. This struct represents that concept.
#[derive(Default)]
struct PreOrderedAletheProof {
    // TODO: declared as attributes to avoid
    // "cannot move out... a captured variable in an `FnMut` closure" errors
    // TODO: declared as Vec<ProofNode> (not using borrows) to avoid
    // error "borrowed data escapes outside of closure"
    /// Pre-ordered version of a given `ProofNode` graph.
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

    /// Returns the index of the last surrounding context actually introduced
    /// within the proof certificate. This is so since scopes are used to
    /// represent scopes from contexts and other constructions with binding occurences
    /// of variables.
    pub fn get_last_introduced_context_index(&self) -> usize {
        let mut last_scope: usize = 0;
        let nesting_level: usize = self.get_contexts_opened() - 1;

        for i in 0..nesting_level {
            if self.context_introduced[nesting_level - 1 - i] {
                last_scope = nesting_level - 1 - i;
                break;
            }
        }

        last_scope
    }
}

/// Information from the last step of the actual subproof. Useful to retrieve
/// information required to decide about how to proceed with the translation
/// of subproofs ending with some specific rule.
struct LastSteps {
    /// Rule name and id of the last step from the actual subproof, if any.
    last_steps_rules: Vec<String>,

    last_steps_ids: Vec<String>,
}

impl LastSteps {
    fn new() -> Self {
        Self {
            last_steps_rules: Vec::new(),
            last_steps_ids: Vec::new(),
        }
    }

    /// Pre : { !`self.last_steps_rule.is_empty()` }
    pub fn last_steps_pop(&mut self) {
        assert!(self.last_steps_rules.len() == self.last_steps_ids.len());
        self.last_steps_rules.pop();
        self.last_steps_ids.pop();
    }

    pub fn last_steps_push(&mut self, last_step_rule: &str, last_step_id: &str) {
        assert!(self.last_steps_rules.len() == self.last_steps_ids.len());
        self.last_steps_rules.push(last_step_rule.to_owned());
        self.last_steps_ids.push(last_step_id.to_owned());
    }

    /// Pre : { !`self.last_steps_rule.is_empty()` }
    pub fn get_last_step_rule(&self) -> &str {
        match self.last_steps_rules.last() {
            Some(rule_name) => rule_name,

            None => {
                // Pre not satisfied
                panic!()
            }
        }
    }

    /// Pre : { !`self.last_steps_id.is_empty()` }
    pub fn get_last_step_id(&self) -> &str {
        match self.last_steps_ids.last() {
            Some(id) => id,

            None => {
                // Pre not satisfied
                panic!()
            }
        }
    }

    pub fn last_steps_empty(&self) -> bool {
        self.last_steps_rules.is_empty()
    }
}

pub struct TranslatorData<StepType, TermType: Clone> {
    /// Pre-ordered version of the Alethe proof to be translated.
    pre_ord_proof: PreOrderedAletheProof,

    /// Information about scopes of variables introduced by contexts,
    /// quantifications and other binders.
    alethe_scopes: AletheScopes<TermType>,

    // /// Maintains references to previous steps from the actual subproof.
    // local_steps: Vec<Vec<usize>>,
    /// Rule and id of the last step from the actual subproof, if any.
    last_steps: LastSteps,

    // For translation purposes, we are just using this representation.
    // TODO: would it be useful to use a DAG representation?
    translated_proof: Vec<StepType>,
}

impl<StepType, TermType: Clone> TranslatorData<StepType, TermType> {
    fn new() -> Self {
        Self {
            translated_proof: Vec::new(),
            pre_ord_proof: PreOrderedAletheProof::default(),
            alethe_scopes: AletheScopes::new(),
            last_steps: LastSteps::new(),
        }
    }
}

/// Describes the behavior of a translator that converts an Alethe proof in its DAG
/// representation, into a vector of steps representation, in some given target language.
/// Parameterized over the types of the target language steps and terms.
pub trait VecToVecTranslator<'a, StepType, TermType: Clone + 'a, TypeTermType> {
    /// Mutable access to common fields.
    fn get_mut_translator_data(&mut self) -> &mut TranslatorData<StepType, TermType>;

    /// Read-only access to common fields.
    fn get_read_translator_data(&self) -> &TranslatorData<StepType, TermType>;

    /// For a given variable name "id", that is bound by some
    /// context, it builds and returns its @var representation.
    /// That is, its representation as a variable bound by some
    /// enclosing context.
    fn build_var_binding(&self, id: &str) -> TermType;

    /// Translates `BindingList` constructs, as used for binder terms forall, exists,
    /// choice and lambda. The "let" binder uses the same construction but assigns to
    /// it a different semantics. See `translate_let_binding_list` for its translation.
    fn translate_binding_list(&mut self, binding_list: &BindingList) -> TermType;

    /// Translates a `BindingList`: it builds a list of pairs (variable, type) for the binding
    /// occurrences, and returns this coupled with the original list of actual values, as a `@VarList`.
    fn translate_let_binding_list(
        &mut self,
        binding_list: &BindingList,
    ) -> (TermType, Vec<TermType>);

    /// Translates a given Alethe Term into its corresponding representation, possibly
    /// modifying scoping information contained in self, to deal with
    /// translation of binding constructions.
    fn translate_term(&mut self, term: &Term) -> TermType;

    fn translate_operator(&self, operator: Operator) -> Symbol;

    fn translate_constant(constant: &Constant) -> TermType;

    fn translate_sort(sort: &Sort) -> TypeTermType;

    /// Implements the translation of an Alethe `Assume`, taking into
    /// account technical differences in the way Alethe rules are
    /// expressed in the target language.
    fn translate_assume(&mut self, id: &str, _depth: usize, term: &Rc<Term>) -> StepType;

    /// Implements the translation of an Alethe `ProofStep`, taking into
    /// account technical differences in the way Alethe rules are
    /// expressed in the target language.
    /// Updates `self.get_mut_translator_data().translated_proof`.
    fn translate_step(&mut self, node: &ProofNode);

    /// Abstracts the steps required to define and push a new context.
    /// PARAMS:
    /// `option_ctx_params`: a vector with the variables introduced by the context (optionally)
    fn define_push_new_context(&mut self, option_ctx_params: Option<Vec<TermType>>);

    /// Abstracts the process of traversing a given context, identifying the fixed
    /// variables and the substitutions. Returns the corresponding list of
    /// variables and substitutions to be used when building a @ctx.
    fn process_anchor_context(&mut self, context: &[AnchorArg]) -> Vec<TermType>;

    /// Returns the identifier of the last context actually introduced within the proof certificate.
    /// PRE: { 0 < `self.contexts_opened`}
    fn get_last_introduced_context_id(&self) -> String {
        // TODO: do not hard-code this string
        String::from("ctx")
            + &(self
                .get_read_translator_data()
                .alethe_scopes
                .get_last_introduced_context_index()
                + 1)
            .to_string()
    }

    /// Inspects a given Alethe step from which we want to extract its id,
    /// also verifying that it is a proper "previous step" from another subproof's
    /// last step.
    fn get_previous_step_id(previous_step: &Option<Rc<ProofNode>>) -> String {
        // Include, as premise, the previous step.
        match previous_step {
            Some(step) => {
                match step.deref() {
                    ProofNode::Step(StepNode { id, .. }) => id.clone(),

                    ProofNode::Subproof(SubproofNode { last_step, .. }) => {
                        // The previous step is the closing step of a subproof.
                        // It is represented as a single SubproofNode. We look
                        // for the actual last step of this subproof.
                        match last_step.deref() {
                            ProofNode::Step(StepNode { id, .. }) => id.clone(),

                            _ => {
                                // It shouldn't be another kind of ProofNode
                                panic!();
                            }
                        }
                    }

                    ProofNode::Assume { .. } => {
                        // It shouldn't be another kind of ProofNode
                        panic!();
                    }
                }
            }

            _ => {
                // There should be some previous step.
                panic!();
            }
        }
    }

    /// Encapsulates the mechanism used to generate fresh identifiers of contexts.
    fn generate_new_context_id(&self) -> String {
        // TODO: do not hard-code this string
        String::from("ctx")
            + &self
                .get_read_translator_data()
                .alethe_scopes
                .get_contexts_opened()
                .to_string()
    }

    /// Implements the actual translation logic, but over a list representation of the proof.
    /// That is, once the original `ProofNode` graph has been translated into a list of single
    /// `ProofNode` steps.
    /// PRE : { `self.pre_ord_proof` is set with a pre-ordered version of the corresponding
    ///               Alethe proof }
    fn translate_pre_ord_proof_node(&mut self) {
        let proof;

        // NOTE: cloning to avoid error
        // "closure requires unique access to `*mut_data` but it is already borrowed//
        {
            proof = self
                .get_mut_translator_data()
                .pre_ord_proof
                .get_pre_ord_proof()
                .clone();
        }

        proof.iter().for_each(|node| {
            match node {
                ProofNode::Assume { id, depth, term } => {
                    // TODO: what about :named?
                    let translated_assume = self.translate_assume(id, *depth, term);
                    self.get_mut_translator_data()
                        .translated_proof
                        .push(translated_assume);
                }

                ProofNode::Step(StepNode { id, .. }) => {
                    self.translate_step(node);

                    // Is this the closing step of the actual subproof?
                    if !self.get_mut_translator_data().last_steps.last_steps_empty() {
                        let last_step_id =
                            &self.get_mut_translator_data().last_steps.get_last_step_id();
                        if *last_step_id == id {
                            // TODO: ugly, hacky way of dealing with
                            // "bind" rule already doing a step-pop of the pushed
                            // context

                            self.get_mut_translator_data().last_steps.last_steps_pop();

                            // Closing the context...
                            self.get_mut_translator_data().alethe_scopes.close_scope();

                            // self.get_mut_translator_data().local_steps.pop();
                        }
                    }
                }

                // A subproof introduced by the 'anchor' command.
                ProofNode::Subproof(SubproofNode { last_step, args, .. }) => {
                    // To store @VarList parameters to @ctx
                    let ctx_params;

                    if args.is_empty() {
                        self.get_mut_translator_data()
                            .alethe_scopes
                            .open_non_context_scope();
                    } else {
                        // { !args.is_empty() }
                        // We actually have an anchor introducing new variables
                        self.get_mut_translator_data()
                            .alethe_scopes
                            .open_context_scope();
                        ctx_params = self.process_anchor_context(args);

                        // Define and open a new context
                        self.define_push_new_context(Some(ctx_params));
                    }

                    // Save information about the last step of the subproof
                    match (*last_step).deref() {
                        ProofNode::Step(StepNode {
                            id: last_step_id,
                            depth: _,
                            clause: _,
                            rule: last_step_rule,
                            ..
                        }) => {
                            self.get_mut_translator_data()
                                .last_steps
                                .last_steps_push(last_step_rule.as_str(), last_step_id.as_str());
                        }

                        _ => {
                            // It shouldn't be something different then a step
                            panic!();
                        }
                    }
                }
            }
        });
    }

    /// Translation of proof certificates, working over a `ProofNode` DAG representation
    /// of the proof. Reorders the received DAG proof into its list of steps representations, and
    /// invokes the corresponding translation routine to translate the result.
    fn translate_2_vect(&'a mut self, proof: &Rc<ProofNode>) -> &'a Vec<StepType> {
        // Mutable borrow to translator data
        {
            // We only translate pre-ordered proofs.
            let mut_data = self.get_mut_translator_data();

            mut_data.pre_ord_proof = PreOrderedAletheProof::new(proof);

            // Clean previously created data.
            if mut_data.alethe_scopes.get_contexts_opened() > 0 {
                mut_data.translated_proof = Vec::new();
                mut_data.alethe_scopes.clean_scopes();
                mut_data.last_steps = LastSteps::new();
            }

            // TODO: Subproof has a context_id that could be used instead of contexts_opened
            // TODO: is it possible to define a private name-space prefixing some
            // symbol?
            // Some rules query the context (e.g., refl). We need to always have
            // opened at least one context
            mut_data.alethe_scopes.open_context_scope();
        }

        self.define_push_new_context(None);

        self.translate_pre_ord_proof_node();

        &self.get_read_translator_data().translated_proof
    }

    /// Translates only an SMT-lib problem.
    fn translate_problem_2_vect(&mut self, problem: &Problem) -> Vec<StepType>;
}
