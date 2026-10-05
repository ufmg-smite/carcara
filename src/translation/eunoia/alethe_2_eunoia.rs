//! Translator for `EunoiaProof`.
use std::path::Path;

use crate::ast::*;
use crate::translation::{
    Symbol, Translator, TranslatorData, VecToVecTranslator,
    eunoia::{alethe_signature::theory::*, ast::*},
};
use crate::utils::HashMapStack;

pub struct EunoiaTranslator {
    /// "Alethe in Eunoia" signature considered during translation.
    alethe_signature: AletheTheory,

    translation: TranslatorData<EunoiaType, EunoiaProof>,

    terms: pool::Storage<EunoiaTerm>,

    cache: HashMapStack<Rc<Term>, Rc<EunoiaTerm>>,
}

impl EunoiaTranslator {
    pub fn new(eunoia_mech: &Path) -> EunoiaTranslator {
        Self {
            alethe_signature: AletheTheory::new(eunoia_mech),
            translation: TranslatorData::new(),
            terms: pool::Storage::default(),
            cache: HashMapStack::default(),
        }
    }

    fn make_var(&mut self, id: &str, ty: EunoiaType) -> Rc<EunoiaTerm> {
        let id = self.terms.add(EunoiaTerm::Id(id.to_owned()));
        let sort = self.terms.add(EunoiaTerm::Type(ty));
        self.terms.add(EunoiaTerm::List(vec![id.clone(), sort]))
    }

    /// Binds a variable in the current scope.
    ///
    /// Since this changes how terms that mention the variable are translated, it also invalidates
    /// the current scope's cache.
    fn bind_variable(&mut self, name: &str, sort: &EunoiaType) {
        self.translation
            .alethe_scopes
            .insert_variable_in_scope(name, sort);
        self.cache.clear_top();
    }

    /// Translates `BindingList` constructs, as used for binder terms forall, exists,
    /// choice and lambda. The "let" binder uses the same construction but assigns to
    /// it a different semantics. See `translate_let_binding_list` for its translation.
    fn translate_binding_list(&mut self, binding_list: &BindingList) -> Rc<EunoiaTerm> {
        let mut ret = Vec::new();

        binding_list.iter().for_each(|sorted_var| {
            let (name, sort) = sorted_var;
            let sort = self
                .terms
                .add(EunoiaTerm::Type(EunoiaTranslator::translate_sort(sort)));
            ret.push(self.terms.add(EunoiaTerm::Var(name.clone(), sort)));
        });

        self.terms.add(EunoiaTerm::List(ret))
    }

    /// Implements the construction of an Eunoia `step` command, for the
    /// given Eunoia conclusion, premises and arguments.
    fn translate_generic_step(
        &mut self,
        id: &str,
        conclusion: Rc<EunoiaTerm>,
        rule: &String,
        premises: Vec<Rc<EunoiaTerm>>,
        arguments: Vec<Rc<EunoiaTerm>>,
    ) {
        if self.alethe_signature.rule_receives_premises(rule) && premises.is_empty() {
            println!("'{}' step without premises?", rule);
            panic!();
        }

        let eunoia_arguments = if self.alethe_signature.rule_receives_varying_arguments(rule) {
            EunoiaList {
                list: vec![self.terms.add(EunoiaTerm::App(
                    self.alethe_signature.varlist_cons.to_owned(),
                    arguments,
                ))],
            }
        } else {
            // { not self.alethe_signature.rule_receives_varying_arguments(rule) }
            EunoiaList { list: arguments }
        };

        self.translation.translated_proof.push(EunoiaCommand::Step {
            id: id.to_owned(),
            conclusion_clause: Some(conclusion),
            rule: rule.clone(),
            premises: EunoiaList { list: premises },
            arguments: eunoia_arguments,
        });
    }

    /// Implements the construction of an Eunoia `step-pop` command, for the
    /// given Eunoia conclusion, premises and arguments. Implements the semantics
    /// of Alethe step-pop steps:
    /// - The surrounding context is passed as argument.
    /// - The immediate previous step is passed as a premise.
    fn translate_generic_step_pop(
        &mut self,
        id: &str,
        conclusion: Rc<EunoiaTerm>,
        rule: &str,
        mut premises: Vec<Rc<EunoiaTerm>>,
        mut arguments: Vec<Rc<EunoiaTerm>>,
        previous_command_id: Option<&str>,
    ) {
        // Step-pops are used to close subproofs. Premises shouldn't be empty.
        // Include, as premises, previous step from the actual subproof.
        premises.push(
            self.terms.add(EunoiaTerm::Id(
                previous_command_id
                    .expect("step without premises?")
                    .to_owned(),
            )),
        );

        // We include, as argument, the context surrounding this
        // subproof's context.
        arguments.push(
            self.terms
                .add(EunoiaTerm::Id(self.get_last_introduced_context_id())),
        );

        self.translation
            .translated_proof
            .push(EunoiaCommand::StepPop {
                id: id.to_owned(),
                conclusion_clause: Some(conclusion),
                rule: rule.to_owned(),
                premises: EunoiaList { list: premises },
                arguments: EunoiaList { list: arguments },
            });
    }
}

impl VecToVecTranslator<'_> for EunoiaTranslator {
    // Corresponding Eunoia ASTs.
    type StepType = EunoiaCommand;
    type TermType = Rc<EunoiaTerm>;
    type TypeTermType = EunoiaType;
    type OperatorType = Symbol;

    fn get_mut_translator_data(&mut self) -> &mut TranslatorData<EunoiaType, EunoiaProof> {
        &mut self.translation
    }

    fn get_read_translator_data(&self) -> &TranslatorData<EunoiaType, EunoiaProof> {
        &self.translation
    }

    fn scope_opened(&mut self) {
        self.cache.push_scope();
    }

    fn scope_closed(&mut self) {
        self.cache.pop_scope();
    }

    fn scopes_cleaned(&mut self) {
        self.cache.clear();
    }

    /// Abstracts the steps required to define and push a new context.
    /// PARAMS:
    /// `option_ctx_params`: a vector with the variables introduced by the context (optionally)
    fn define_push_new_context(&mut self, option_ctx_params: Option<Vec<Rc<EunoiaTerm>>>) {
        let new_context_id = self.get_current_context_id();

        match option_ctx_params {
            // First call to the method. We create a dummy context with no actual
            // information.
            None => {
                self.translation
                    .translated_proof
                    .push(EunoiaCommand::Define {
                        name: new_context_id.clone(),
                        typed_params: EunoiaList { list: vec![] },
                        term: self.terms.add(EunoiaTerm::True),
                        attrs: Vec::new(),
                    });

                self.translation
                    .translated_proof
                    .push(EunoiaCommand::Assume {
                        name: self.alethe_signature.ctx_assumption.to_owned(),
                        term: self.terms.add(EunoiaTerm::Id(new_context_id.clone())),
                    });
            }

            Some(ctx_params) => {
                // { not ctx_params.is_empty() }
                self.translation
                    .translated_proof
                    .push(EunoiaCommand::Define {
                        name: new_context_id.clone(),
                        typed_params: EunoiaList { list: Vec::new() },
                        term: self.terms.add(EunoiaTerm::App(
                            self.alethe_signature.ctx.to_owned(),
                            ctx_params,
                        )),
                        attrs: Vec::new(),
                    });

                // (assume-push context ctxn)
                self.translation
                    .translated_proof
                    .push(EunoiaCommand::AssumePush {
                        name: self.alethe_signature.ctx_assumption.to_owned(),
                        term: self.terms.add(EunoiaTerm::Id(new_context_id.clone())),
                    });
            }
        }
    }

    fn process_anchor_context(&mut self, context: &[AnchorArg]) -> Vec<Rc<EunoiaTerm>> {
        // Returned list of variables and substitutions to be used when
        // building a @ctx.
        let mut ctx_params = Vec::new();
        // Variables bound by the context
        let mut context_domain = Vec::new();
        // Actual substitution induced by the context
        let mut subst: Vec<Rc<EunoiaTerm>> = Vec::new();
        // Dummy initial value
        let mut eunoia_sort: EunoiaType = EunoiaType::Bool;

        context.iter().for_each(|arg| match arg {
            AnchorArg::Variable((name, sort)) => {
                // TODO: either use borrows or implement
                // Copy trait for EunoiaTerms
                eunoia_sort = EunoiaTranslator::translate_sort(sort);

                // TODO: encapsulate variables_in_scope
                // TODO: see how to abstract this into a single function
                match self
                    .translation
                    .alethe_scopes
                    .variables_in_scope
                    .get_with_depth(name)
                {
                    Some((depth, _)) => {
                        if depth < self.translation.alethe_scopes.variables_in_scope.height() - 1 {
                            // This variable is bound somewhere else.  We
                            // shadow any previous def.
                            self.bind_variable(name, &eunoia_sort);

                            context_domain.push(self.make_var(name, eunoia_sort.clone()));
                        }
                    }

                    None => {
                        // This variable is not bound somewhere else.
                        self.bind_variable(name, &eunoia_sort);

                        context_domain.push(self.make_var(name, eunoia_sort.clone()));
                    }
                }

                // { name is in scope }
                // Variable "name" is fixed. We represent it explicitly
                // with a substitution map of the form name -> name,
                // reified it as a term (= name name)
                let bound_var = self.build_var_binding(name);

                subst.push(self.terms.add(EunoiaTerm::App(
                    self.alethe_signature.eq.to_owned(),
                    vec![bound_var.clone(), bound_var],
                )));
            }

            AnchorArg::Assign((name, sort), term) => {
                // TODO: either use borrows or implement
                // Copy trait for EunoiaTerms
                eunoia_sort = EunoiaTranslator::translate_sort(sort);

                let rhs = self.translate_term(term);

                // TODO: see how to abstract this into a single function, it is repeated
                // above.
                match self
                    .translation
                    .alethe_scopes
                    .variables_in_scope
                    .get_with_depth(name)
                {
                    Some((depth, _)) => {
                        // TODO: some better way to implement this
                        if depth < self.translation.alethe_scopes.variables_in_scope.height() - 1 {
                            // This variable is bound somewhere else.  We
                            // shadow any previous def.
                            self.bind_variable(name, &eunoia_sort);

                            context_domain.push(self.make_var(name, eunoia_sort.clone()));

                            // { variable (name, sort) is in scope }

                            // Substitution map of the form name -> rhs: we
                            // reify it as a term (= name rhs)
                            let bound_var = self.build_var_binding(name);
                            subst.push(self.terms.add(EunoiaTerm::App(
                                self.alethe_signature.eq.to_owned(),
                                vec![bound_var, rhs],
                            )));
                        }
                    }

                    None => {
                        // This variable is not bound somewhere else.
                        self.bind_variable(name, &eunoia_sort);

                        context_domain.push(self.make_var(name, eunoia_sort.clone()));

                        // { variable (name, sort) is in scope }

                        // Substitution map of the form name -> rhs: we
                        // reify it as a term (= name rhs)
                        let bound_var = self.build_var_binding(name);
                        subst.push(self.terms.add(EunoiaTerm::App(
                            self.alethe_signature.eq.to_owned(),
                            vec![bound_var, rhs],
                        )));
                    }
                }
            }
        });

        // Add the previous context, which we are extending.
        subst.push(
            self.terms
                .add(EunoiaTerm::Id(self.get_last_introduced_context_id())),
        );

        // Add typed params.
        if context_domain.is_empty() {
            // Empty VarList
            ctx_params.push(
                self.terms
                    .add(EunoiaTerm::Id(self.alethe_signature.varlist_nil.to_owned())),
            );
        } else {
            ctx_params.push(self.terms.add(EunoiaTerm::List(context_domain)));
        }

        // Concat (and...)
        ctx_params.push(
            self.terms
                .add(EunoiaTerm::App(self.alethe_signature.and.to_owned(), subst)),
        );

        ctx_params
    }

    /// Translates a given Term into its corresponding `EunoiaTerm`, possibly
    /// modifying scoping information contained in self, to deal with
    /// translation of binding constructions.
    fn translate_term(&mut self, term: &Rc<Term>) -> Rc<EunoiaTerm> {
        if let Some(cached) = self.cache.get_top(term) {
            return cached.clone();
        }

        let translated = match term.as_ref() {
            Term::Const(constant) => self.translate_constant(constant),

            Term::Op(operator, operands) => {
                let operands_eunoia = operands
                    .iter()
                    .map(|operand| self.translate_term(operand))
                    .collect();

                self.terms.add(match operator {
                    Operator::True => EunoiaTerm::True,
                    Operator::False => EunoiaTerm::False,
                    // NOTE: the category EunoiaOperator refers to Eunoia's built-ins.
                    // Here, we are translating an application of an Alethe operator, which
                    // are not expressed in terms of Eunoia's. We translate this as a regular
                    // application of some constant defined in the signature used.
                    _ => EunoiaTerm::App(self.translate_operator(*operator), operands_eunoia),
                })
            }

            // TODO: not considering the sort of the variable.
            Term::Var(string, _) => {
                // Check if it is a variable introduced by some binder
                match self.translation.alethe_scopes.get_variable_in_scope(string) {
                    Some(_) => self.build_var_binding(string),

                    None => self.terms.add(EunoiaTerm::Id(string.clone())),
                }
            }

            Term::App(fun, params) => {
                let mut fun_params = Vec::new();

                params.iter().for_each(|param| {
                    fun_params.push(self.translate_term(param));
                });

                self.terms
                    .add(EunoiaTerm::App((*fun).to_string(), fun_params))
            }

            Term::Let(binding_list, scope) => {
                // New scope.
                self.translation.alethe_scopes.open_non_context_scope();
                self.scope_opened();

                let (bindings, translated_values) = self.translate_let_binding_list(binding_list);

                bindings.iter().for_each(|var| match var.as_ref() {
                    EunoiaTerm::Var(id, sort) => {
                        let eunoia_sort = match **sort {
                            EunoiaTerm::Type(ref actual_sort) => actual_sort,

                            _ => {
                                println!("Expected sort3, got {:?}", sort);
                                panic!()
                            }
                        };

                        self.bind_variable(id, eunoia_sort);
                    }

                    _ => {
                        // It shouldn't be diff. than EunoiaTerm::Var.
                        panic!();
                    }
                });

                let bindings = self.terms.add(EunoiaTerm::List(bindings));
                let scope = self.translate_term(scope);
                let let_binder = self.terms.add(EunoiaTerm::App(
                    self.alethe_signature.let_binder.to_owned(),
                    vec![bindings, scope],
                ));
                let final_let_trans = self
                    .terms
                    .add(EunoiaTerm::HOApp(let_binder, translated_values));

                self.translation.alethe_scopes.close_scope();
                self.scope_closed();

                final_let_trans
            }

            Term::Binder(binder, binding_list, scope) => {
                // New scope to shadow those context variables that
                // now bound by this binder.
                self.translation.alethe_scopes.open_non_context_scope();
                self.scope_opened();
                let translated_bindings = self.translate_binding_list(binding_list);
                match translated_bindings.as_ref() {
                    EunoiaTerm::List(bindings) => {
                        bindings.iter().for_each(|var| match var.as_ref() {
                            EunoiaTerm::Var(id, sort) => {
                                let eunoia_sort = match **sort {
                                    EunoiaTerm::Type(ref actual_sort) => actual_sort,

                                    _ => {
                                        println!("Expected sort4, got {:?}", sort);
                                        panic!()
                                    }
                                };

                                self.bind_variable(id, eunoia_sort);
                            }

                            _ => {
                                // It shouldn't be diff. than EunoiaTerm::Var.
                                panic!();
                            }
                        });
                    }

                    _ => {
                        // It shouldn't be diff. than EunoiaTerm::List.
                        panic!();
                    }
                }

                let translated_binder = match binder {
                    Binder::Forall => EunoiaTerm::App(
                        self.alethe_signature.forall_binder.to_owned(),
                        vec![translated_bindings, self.translate_term(scope)],
                    ),

                    Binder::Exists => EunoiaTerm::App(
                        self.alethe_signature.exists_binder.to_owned(),
                        vec![translated_bindings, self.translate_term(scope)],
                    ),

                    Binder::Choice => {
                        let choice_var: Rc<EunoiaTerm>;
                        // There should be just one defined variable.
                        match translated_bindings.as_ref() {
                            EunoiaTerm::List(list) => {
                                assert!(list.len() == 1);
                                match list[0].as_ref() {
                                    EunoiaTerm::Var(var_name, ..) => {
                                        choice_var =
                                            self.terms.add(EunoiaTerm::Id(var_name.clone()));
                                    }

                                    _ => panic!(),
                                }
                            }

                            _ => panic!(),
                        };

                        EunoiaTerm::App(
                            self.alethe_signature.choice_binder.to_owned(),
                            vec![translated_bindings, choice_var, self.translate_term(scope)],
                        )
                    }

                    // TODO: complete
                    Binder::Lambda => EunoiaTerm::App(
                        self.alethe_signature.exists_binder.to_owned(),
                        vec![translated_bindings, self.translate_term(scope)],
                    ),
                };
                let translated_binder = self.terms.add(translated_binder);

                // Closing the context...
                self.translation.alethe_scopes.close_scope();
                self.scope_closed();

                translated_binder
            }

            _ => {
                println!("No defined translation for term {:?}", term);
                panic!()
            }
        };
        self.cache.insert(term.clone(), translated.clone());
        translated
    }

    /// For a given variable name "id", that is bound by some
    /// binder, it builds and returns its @var representation.
    /// That is, its representation as a variable bound by some
    /// enclosing binder.
    /// PRE : { id is in scope }
    fn build_var_binding(&mut self, id: &str) -> Rc<EunoiaTerm> {
        // TODO: this could be much simpler and faster if alethe scopes stored the result of
        // `make_var`
        let sort = self
            .translation
            .alethe_scopes
            .get_variable_in_scope(&id.to_owned())
            .expect("Id is not in scope.")
            .clone();

        let binding = self.make_var(id, sort);
        let binding = self.terms.add(EunoiaTerm::List(vec![binding]));

        let id_term = self.terms.add(EunoiaTerm::Id(id.to_owned()));
        self.terms.add(EunoiaTerm::App(
            self.alethe_signature.var.to_owned(),
            vec![binding, id_term],
        ))
    }

    /// Translates a `BindingList` as required by our definition of @let: it builds a list
    /// of pairs (variable, type) for the binding occurrences, and returns this coupled with
    /// the original list of actual values, as a `@VarList`.
    fn translate_let_binding_list(
        &mut self,
        binding_list: &BindingList<Rc<Term>>,
    ) -> (Vec<Rc<EunoiaTerm>>, Vec<Rc<EunoiaTerm>>) {
        let mut binding_occ = Vec::new();
        let mut values = Vec::new();

        binding_list.iter().for_each(|sorted_var| {
            let (name, value) = sorted_var;
            let translated_value = self.translate_term(value);
            let value_sort = value.raw_sort();
            let translated_value_sort = EunoiaTranslator::translate_sort(&value_sort);

            let sort = self.terms.add(EunoiaTerm::Type(translated_value_sort));
            binding_occ.push(self.terms.add(EunoiaTerm::Var(name.clone(), sort)));

            values.push(translated_value.clone());
        });

        (binding_occ, values)
    }

    fn translate_operator(&self, operator: Operator) -> Symbol {
        match operator {
            // Logic
            Operator::And => self.alethe_signature.and.to_owned(),

            Operator::Or => self.alethe_signature.or.to_owned(),

            Operator::Xor => self.alethe_signature.xor.to_owned(),

            Operator::Not => self.alethe_signature.not.to_owned(),

            Operator::Implies => self.alethe_signature.implies.to_owned(),

            Operator::Ite => self.alethe_signature.ite.to_owned(),

            // Order / Comparison.
            Operator::Equals => self.alethe_signature.eq.to_owned(),

            Operator::GreaterThan => self.alethe_signature.gt.to_owned(),

            Operator::GreaterEq => self.alethe_signature.ge.to_owned(),

            Operator::LessThan => self.alethe_signature.lt.to_owned(),

            Operator::LessEq => self.alethe_signature.le.to_owned(),

            Operator::Distinct => String::from("distinct"),

            // Arithmetic
            Operator::Add => self.alethe_signature.add.to_owned(),

            Operator::Sub => self.alethe_signature.sub.to_owned(),

            Operator::Mult => self.alethe_signature.mult.to_owned(),

            Operator::IntDiv => self.alethe_signature.int_div.to_owned(),

            Operator::RealDiv => self.alethe_signature.real_div.to_owned(),

            _ => {
                println!("No defined translation for operator {:?}", operator);
                panic!()
            }
        }
    }

    fn translate_constant(&mut self, constant: &Constant) -> Rc<EunoiaTerm> {
        let term = match constant {
            Constant::Integer(integer) => EunoiaTerm::Numeral(integer.clone()),

            Constant::Real(rational) => EunoiaTerm::Decimal(rational.clone()),

            Constant::String(string) => EunoiaTerm::String(string.clone()),

            // TODO
            Constant::BitVec(..) => panic!(),
            Constant::RegLan(_, _) => panic!(),
        };

        self.terms.add(term)
    }

    fn translate_sort(sort: &Sort) -> EunoiaType {
        match sort {
            Sort::Real => EunoiaType::Real,

            // User-defined sort
            // TODO: what about args?
            Sort::Atom(string, ..) => EunoiaType::Name(string.to_string()),

            Sort::Function(sorts) => {
                assert!(sorts.len() >= 2,);

                let return_sort = EunoiaTranslator::translate_sort(sorts.last().unwrap());

                let mut sorts_params = Vec::new();

                for (pos, sort) in sorts.iter().enumerate() {
                    if pos < sorts.len() - 1 {
                        sorts_params.push(EunoiaTranslator::translate_sort(sort));
                    }
                }

                // TODO: no attrs?
                EunoiaType::Fun(vec![], sorts_params, Box::new(return_sort))
            }

            Sort::Bool => EunoiaType::Bool,

            _ => EunoiaType::Real,
        }
    }

    /// Implements the translation of an Alethe `Assume`, taking into
    /// account technical differences in the way Alethe rules are
    /// expressed within Eunoia.
    fn translate_assume(&mut self, id: &str, term: &Rc<Term>) -> EunoiaCommand {
        let term = self.translate_term(term);
        let clause = self.terms.add(EunoiaTerm::App(
            self.alethe_signature.cl.to_owned(),
            vec![term],
        ));

        // Check last instruction in actual subproof

        if self.translation.last_steps.last_steps_empty() {
            // Regular introduction of assumptions
            EunoiaCommand::Assume { name: id.to_owned(), term: clause }
        } else {
            // { not self.translation.last_steps.last_steps_empty() }
            match self.translation.last_steps.get_last_step_rule() {
                // "subproof" receives every "assume" command as an actual
                // ethos assumption; we need to push every assumption
                "subproof" => EunoiaCommand::AssumePush { name: id.to_owned(), term: clause },

                // Regular introduction of assumptions
                _ => EunoiaCommand::Assume { name: id.to_owned(), term: clause },
            }
        }
    }

    /// Implements the translation of an Alethe `ProofStep`, taking into
    /// account technical differences in the way Alethe rules are
    /// expressed within Eunoia.
    /// Updates `self.translation.translated_proof`.
    fn translate_step(
        &mut self,
        command: &ProofCommand,
        iter: &ProofIter<'_>,
        previous_command_id: Option<&str>,
    ) {
        let mut eunoia_premises: Vec<Rc<EunoiaTerm>> = Vec::new();

        match command {
            ProofCommand::Step(ProofStep {
                id,
                clause,
                rule,
                premises,
                args,
                discharge,
            }) => {
                // Add premises actually present in the original step command.
                eunoia_premises.extend(
                    premises
                        .iter()
                        .map(|premise| {
                            self.terms.add(EunoiaTerm::Id(String::from(
                                iter.get_premise(*premise).id(),
                            )))
                        })
                        .collect::<Vec<_>>(),
                );

                // NOTE: in ProofStep, clause has type
                // Vec<Rc<Term>>, though it represents an
                // invocation of Alethe's cl operator
                // TODO: we are always adding the conclusion clause
                let conclusion = if clause.is_empty() {
                    self.terms
                        .add(EunoiaTerm::Id(self.alethe_signature.empty_cl.to_owned()))
                } else {
                    // {!clause.is_empty()}
                    let clause = clause
                        .iter()
                        .map(|term| self.translate_term(term))
                        .collect();
                    self.terms
                        .add(EunoiaTerm::App(self.alethe_signature.cl.to_owned(), clause))
                };

                // NOTE: not adding conclusion clause to this list
                let mut eunoia_arguments: Vec<Rc<EunoiaTerm>> = Vec::new();

                args.iter().for_each(|arg| {
                    eunoia_arguments.push(self.translate_term(arg));
                });

                match rule.as_str() {
                    // Subproof-closing steps
                    "let" | "bind_let" | "bind" | "sko_ex" => {
                        self.translate_generic_step_pop(
                            id,
                            conclusion,
                            if rule == "let" { "let_elim" } else { rule },
                            eunoia_premises,
                            eunoia_arguments,
                            previous_command_id,
                        );
                    }

                    "subproof" => {
                        // The command (as mechanized in Eunoia) gets the formula proven
                        // through an "assumption", hence, we use StepPop.
                        // The discharged assumptions (specified, in Alethe, through the
                        // "discharge" formal parameter), will be pushed
                        // Assuming that the conclusion is of the form
                        // not φ1, ..., not φn, ψ
                        // extract ψ
                        let mut premise = self.terms.add(EunoiaTerm::App(
                            self.alethe_signature.cl.to_owned(),
                            vec![self.alethe_signature.extract_consequent(&conclusion)],
                        ));

                        let mut cl_disjuncts: Vec<Rc<EunoiaTerm>> = vec![];

                        // Id of the premise step
                        let mut id_premise: Symbol = "".to_owned();

                        discharge.iter().rev().for_each(|discharged_assumption| {
                            let assumption = iter.get_premise(*discharged_assumption);

                            // TODO: we are discarding vector premises
                            match assumption {
                                ProofCommand::Assume { id: _, term } => {
                                    let term = self.translate_term(term);
                                    cl_disjuncts = vec![self.terms.add(EunoiaTerm::App(
                                        self.alethe_signature.not.to_owned(),
                                        vec![term],
                                    ))];

                                    cl_disjuncts.append(
                                        &mut self.alethe_signature.extract_cl_disjuncts(&premise),
                                    );

                                    let implied_conclusion = self.terms.add(EunoiaTerm::App(
                                        self.alethe_signature.cl.to_owned(),
                                        cl_disjuncts.clone(),
                                    ));

                                    // Get id of previous step
                                    let eunoia_proof = &self.translation.translated_proof;

                                    id_premise = eunoia_proof[eunoia_proof.len() - 1].get_step_id();

                                    // TODO: change id!
                                    // TODO: ethos does not complain about repeated ids
                                    self.translation.translated_proof.push(
                                        EunoiaCommand::StepPop {
                                            id: id.to_owned(),
                                            conclusion_clause: Some(implied_conclusion.clone()),
                                            rule: rule.clone(),
                                            premises: EunoiaList {
                                                list: vec![
                                                    self.terms
                                                        .add(EunoiaTerm::Id(id_premise.clone())),
                                                ],
                                            },
                                            arguments: EunoiaList {
                                                list: eunoia_arguments.clone(),
                                            },
                                        },
                                    );

                                    premise = implied_conclusion.clone();
                                }

                                _ => {
                                    // It shouldn't be a ProofCommand different than an Assume
                                    panic!();
                                }
                            }
                        });
                    }

                    "refl" => {
                        // We include, as an argument, the context surrounding this
                        // subproof's context.
                        eunoia_arguments.push(
                            self.terms
                                .add(EunoiaTerm::Id(self.get_current_context_id())),
                        );

                        self.translate_generic_step(
                            id,
                            conclusion,
                            rule,
                            eunoia_premises,
                            eunoia_arguments,
                        );
                    }

                    "rare_rewrite" => {
                        let rule_name = match eunoia_arguments[0].as_ref() {
                            EunoiaTerm::String(rare_rewrite_name) => rare_rewrite_name,

                            _ => {
                                println!(
                                    "Expected rare_rewrite rule name, got {:?}",
                                    eunoia_arguments[0]
                                );
                                panic!()
                            }
                        };

                        self.translate_generic_step(
                            id,
                            conclusion,
                            rule_name,
                            eunoia_premises,
                            // Dropping rule name.
                            eunoia_arguments[1..].to_vec(),
                        );
                    }

                    _ => {
                        // Generic step.
                        self.translate_generic_step(
                            id,
                            conclusion,
                            rule,
                            eunoia_premises,
                            eunoia_arguments,
                        );
                    }
                }
            }

            _ => {
                // Method should be called upon a StepNode
                panic!();
            }
        }
    }

    /// Translates only an SMT-lib problem. Note that it only translates the
    /// "problem prelude" (as described in the implementation of Carcara's
    /// `Problem` struct). The assertions introduced in the problem definition
    /// are not translated.
    fn translate_problem_2_vect(&mut self, problem: &Problem) -> EunoiaProof {
        let Problem { prelude, .. } = problem;

        let ProblemPrelude {
            sort_declarations,
            function_declarations,
            ..
        } = prelude;

        let mut eunoia_prelude = Vec::new();

        // Include files for the Alethe mechanization in Eunoia.
        self.alethe_signature
            .mechanization_files
            .iter()
            .for_each(|path| {
                eunoia_prelude.push(EunoiaCommand::Include {
                    path: path.to_string_lossy().into_owned(),
                });
            });

        // Sorts declarations.
        sort_declarations.iter().for_each(|pair| {
            eunoia_prelude.push(EunoiaCommand::DeclareConst {
                name: pair.0.clone(),
                eunoia_type: self.terms.add(EunoiaTerm::Type(EunoiaType::Type)),
                attrs: Vec::new(),
            });
        });

        // Constants declarations.
        function_declarations.iter().for_each(|pair| {
            eunoia_prelude.push(EunoiaCommand::DeclareConst {
                name: pair.0.clone(),
                eunoia_type: self
                    .terms
                    .add(EunoiaTerm::Type(EunoiaTranslator::translate_sort(&pair.1))),
                attrs: Vec::new(),
            });
        });

        eunoia_prelude
    }
}

impl Translator<'_> for EunoiaTranslator {
    type Output = EunoiaProof;

    fn translate(&mut self, proof: &mut Proof) -> &Self::Output {
        self.translate_2_vect(proof)
    }

    fn translate_problem(&mut self, problem: &Problem) -> Self::Output {
        self.translate_problem_2_vect(problem)
    }
}
