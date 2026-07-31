#![allow(unused)]
/// Services for the translation of Alethe proofs.
pub mod eunoia;
pub mod tstp;

use crate::ast::*;

use std::io::Result;
// Deref for ast::rc::Rc<Term>
use std::ops::Deref;

// scopes
use crate::utils::HashMapStack;

/// SMT-LIB version 3.0 symbol.
type Symbol = String;

/// Interface with an Alethe proof compiler.
pub trait Translator<'a> {
    type Output;

    /// Translates a proof in its vector representation, into some target language.
    fn translate(&mut self, proof: &mut Proof) -> &Self::Output;

    /// Translates only an SMT-lib problem.
    fn translate_problem(&mut self, problem: &Problem) -> Self::Output;
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

        self.variables_in_scope.push_scope();
        self.context_introduced.push(context_introduced);
    }

    /// Closes the last open scope.
    /// PRE : { `self.context_introduced.len()` >= 1 }
    pub fn close_scope(&mut self) {
        assert!(!self.context_introduced.is_empty());

        self.variables_in_scope.pop_scope();

        // TODO: let Some(true)?
        let context_introduced = self.context_introduced.pop();

        if context_introduced == Some(true) {
            // We are closing a context (instead of closing the scope of some other
            // binder).
            self.contexts_opened -= 1;
        }
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

/// Maintains several related data-structures, useful for translation purposes.
pub struct TranslatorData<TermType: Clone, ProofType: Default> {
    /// Information about scopes of variables introduced by contexts,
    /// quantifications and other binders.
    alethe_scopes: AletheScopes<TermType>,

    /// Rule and id of the last step from the actual subproof, if any.
    last_steps: LastSteps,

    translated_proof: ProofType,

    /// Translation of subproofs might require special treatment. We flag when
    /// the compiler enters the body of a subproof.
    is_in_subproof: bool,
}

impl<TermType: Clone, ProofType: Default> TranslatorData<TermType, ProofType> {
    fn new() -> Self {
        Self {
            translated_proof: ProofType::default(),
            alethe_scopes: AletheScopes::new(),
            last_steps: LastSteps::new(),
            is_in_subproof: false,
        }
    }
}

/// Describes the behavior of a translator that converts an Alethe proof in its DAG
/// representation, into a vector of steps representation, in some given target language.
/// Parameterized over the types of the target language steps and terms.
pub trait VecToVecTranslator<
    'a,
    StepType,
    TermType: Clone + 'a,
    TypeTermType: Clone + 'a,
    OperatorType,
>
{
    /// Mutable access to common fields.
    fn get_mut_translator_data(&mut self) -> &mut TranslatorData<TypeTermType, Vec<StepType>>;

    /// Read-only access to common fields.
    fn get_read_translator_data(&self) -> &TranslatorData<TypeTermType, Vec<StepType>>;

    /// For a given variable name "id", that is bound by some
    /// context, it builds and returns its @var representation.
    /// That is, its representation as a variable bound by some
    /// enclosing context.
    fn build_var_binding(&self, id: &str) -> TermType;

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

    /// In some situations, we need to access to the `VecToVecTranslator` object.
    /// Hence the self reference.
    fn translate_operator(&self, operator: Operator) -> OperatorType;

    fn translate_constant(constant: &Constant) -> TermType;

    fn translate_sort(sort: &Sort) -> TypeTermType;

    /// Implements the translation of an Alethe `Assume`, taking into
    /// account technical differences in the way Alethe rules are
    /// expressed in the target language.
    fn translate_assume(&mut self, id: &str, term: &Rc<Term>) -> StepType;

    /// Implements the translation of an Alethe `ProofStep`, taking into
    /// account technical differences in the way Alethe rules are
    /// expressed in the target language.
    /// Updates `self.get_mut_translator_data().translated_proof`.
    fn translate_step(
        &mut self,
        command: &ProofCommand,
        iter: &ProofIter<'_>,
        previous_command_id: Option<&str>,
    );

    /// Abstracts the steps required to define and push a new context.
    /// PARAMS:
    /// `option_ctx_params`: a vector with the variables introduced by the context (optionally)
    fn define_push_new_context(&mut self, option_ctx_params: Option<Vec<TermType>>);

    /// Abstracts the process of traversing a given context, identifying the fixed
    /// variables and the substitutions. Returns the corresponding list of
    /// variables and substitutions to be used when building the representation
    /// of contexts.
    /// PRE : { the scope representing the context to be processed is already
    ///         opened }
    fn process_anchor_context(&mut self, context: &[AnchorArg]) -> Vec<TermType>;

    /// Returns the identifier of the last context actually introduced within the proof certificate.
    /// PRE: { 0 < `self.contexts_opened`}
    fn get_last_introduced_context_id(&self) -> String {
        // TODO: do not hard-code this string
        String::from("ctx")
            + &(self
                .get_read_translator_data()
                .alethe_scopes
                .get_contexts_opened()
                - 1)
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

    /// Iterates over a list representation of the Alethe proof to be translated.
    /// Generates a linear representation of the translated proof.
    /// Should not be called directly by a user implementing this trait for
    /// some custom data-structure.
    fn iterate_and_translate_proof(&mut self, proof: &[ProofCommand], iter: &mut ProofIter<'_>) {
        // NOTE: needed to iterate like this, to be able to get to "previous
        // step", since the current iterator does not allow us to do so.
        for i in 0..proof.len() {
            if let Some(command) = iter.next() {
                match command {
                    ProofCommand::Assume { id, term } => {
                        // TODO: what about :named?
                        let translated_assume = self.translate_assume(id, term);
                        self.get_mut_translator_data()
                            .translated_proof
                            .push(translated_assume);
                    }

                    ProofCommand::Step(ProofStep { id, .. }) => {
                        let previous_command_id = if i > 0 {
                            Some(proof[i - 1].id())
                        } else {
                            // { i == 0 }
                            None
                        };

                        self.translate_step(command, iter, previous_command_id);

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
                                // Exiting the subproof.
                                self.get_mut_translator_data().is_in_subproof = false;
                            }
                        }
                    }

                    // A subproof introduced by the 'anchor' command.
                    ProofCommand::Subproof(Subproof { commands, args, .. }) => {
                        // Some compilers might to give special treatment to subproofs .
                        // We flag once we enter a subproof.
                        self.get_mut_translator_data().is_in_subproof = true;

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

                            // Process the vector of AnchorArgs.
                            ctx_params = self.process_anchor_context(args);

                            // Define and open a new context
                            self.define_push_new_context(Some(ctx_params));
                        }

                        // Save information about the last step of the subproof
                        let last_step = commands.last();

                        match last_step {
                            Some(ProofCommand::Step(ProofStep {
                                id: last_step_id,
                                clause: _,
                                rule: last_step_rule,
                                ..
                            })) => {
                                self.get_mut_translator_data().last_steps.last_steps_push(
                                    last_step_rule.as_str(),
                                    last_step_id.as_str(),
                                );
                            }

                            _ => {
                                // It shouldn't be something different then a step
                                panic!();
                            }
                        }

                        // Translate subproof.
                        self.iterate_and_translate_proof(commands, iter);
                    }
                }
            }
        }
    }

    /// Actual translation routine of proof certificates, working over a vector
    /// representation of the proof. Handles the preparation of scopes, cleaning of
    /// previously created data-structures and invocation of the proper translation
    /// routines.
    fn translate_2_vect<'b>(&'b mut self, proof: &mut Proof) -> &'b Vec<StepType>
    where
        TypeTermType: 'b,
    {
        // Mutable borrow to translator data
        {
            // We only translate pre-ordered proofs.
            let mut_data = self.get_mut_translator_data();

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

        self.iterate_and_translate_proof(&proof.commands, &mut proof.iter());

        &self.get_read_translator_data().translated_proof
    }

    /// Translates only an SMT-lib problem.
    fn translate_problem_2_vect(&mut self, problem: &Problem) -> Vec<StepType>;
}

/// Common pretty printing interface shared by Eunoia and TSTP compilers.
pub trait ProofPrinter {
    type Proof;

    fn write_proof(&mut self, proof: &Self::Proof) -> Result<()>;
}
