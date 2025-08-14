//! Translator for `TstpProof`.
use crate::ast::*;
use crate::translation::tstp::tstp_ast::*;
use crate::translation::Translator;
use crate::translation::TranslatorData;
use crate::translation::VecToVecTranslator;

// Deref for ast::rc::Rc<Term>
use std::ops::Deref;
// formulas_count
use std::collections::HashMap;

pub struct TstpTranslator {
    translation: TranslatorData<TstpFormula, TstpProof>,
    // To keep a counting of each annotated formula introduced, for
    // naming purposes.
    formulas_count: HashMap<TstpFormulaRole, rug::Integer>,
    // To keep track of each named formula, for reference purposes.
    formulas_map: HashMap<String, TstpFormula>,
}

impl TstpTranslator {
    pub fn new() -> Self {
        Self {
            translation: TranslatorData::new(),
            formulas_count: HashMap::new(),
            formulas_map: HashMap::new(),
        }
    }

    /// Abstracts the main mechanisms put to work to build an annotated formula:
    /// - generate a new name
    /// - build the corresponding AST
    /// - maintain a correspondence between the given name and the formula
    fn new_annotated_formula(
        &mut self,
        language: TstpLanguage,
        role: TstpFormulaRole,
        formula: TstpFormula,
        source: TstpAnnotatedFormulaSource,
        useful_info: Symbol,
    ) -> TstpAnnotatedFormula {
        let formula_name = self.new_formula_name(&role);

        // Register the formula
        self.formulas_map
            .insert(formula_name.clone(), formula.clone());

        TstpAnnotatedFormula::new(
            // TODO: some other language?
            language,
            formula_name.clone(),
            // TODO: define a proper way for generation and index of these names.
            // "some_formula_name".to_owned(),
            role,
            formula.clone(),
            source,
            useful_info,
        )
    }

    /// Abstracts the mechanism used to generate a new name for an annotated
    /// formula, and register it, for future reference.
    fn new_formula_name(&mut self, role: &TstpFormulaRole) -> String {
        // For axioms, lemmas, conjecture, hypothesis, naming
        // mechanism is rather simple: role + number.

        let mut new_name: String;

        if self.formulas_count.contains_key(role) {
            self.formulas_count
                .insert(role.clone(), self.formulas_count[role].clone() + 1);
        } else {
            // { ! self.formulas_count.contains_key(role) }
            self.formulas_count
                .insert(role.clone(), rug::Integer::from(1));
        }

        // TODO: ugly way to deal with this, since I do not want to implement
        // the Display trait for TstpFormulaRole at this level (or at the level
        // of the ASTs themselves).
        match role {
            TstpFormulaRole::Axiom => {
                new_name = "axiom".to_owned();
            }

            TstpFormulaRole::Lemma => {
                new_name = "lemma".to_owned();
            }

            TstpFormulaRole::Conjecture => {
                new_name = "conjecture".to_owned();
            }

            TstpFormulaRole::Hypothesis => {
                new_name = "hypothesis".to_owned();
            }

            TstpFormulaRole::Logic => {
                new_name = "logic".to_owned();
            }

            TstpFormulaRole::Type => {
                new_name = "type".to_owned();
            }

            TstpFormulaRole::Plain => {
                new_name = "plain".to_owned();
            }
        }

        new_name += &("_".to_owned() + &self.formulas_count[role].to_string());

        new_name
    }

    /// Translates the application of an Alethe operator into its expected TSTP
    /// representation. We devote a specific method to this task, to tackle some
    /// special situations that appear when translating into Tstp.
    fn translate_operator_application(
        &mut self,
        operator: Operator,
        operands: &[Rc<Term>],
    ) -> TstpFormula {
        let operands_tstp: Vec<TstpFormula> = operands
            .iter()
            .map(|operand| self.translate_term(operand))
            .collect();

        match self.translate_operator(operator) {
            TstpOperator::NullaryOperator(nullary_op) => {
                assert!(operands.is_empty());

                TstpFormula::NullaryOperatorApp(nullary_op)
            }

            TstpOperator::UnaryOperator(unary_op) => {
                assert!(operands.len() == 1);

                TstpFormula::UnaryOperatorApp(unary_op, Box::new(operands_tstp[0].clone()))
            }

            TstpOperator::BinaryOperator(binary_op) => {
                // From TPTP docs:
                // "The binary connectives are left associative."
                // Assumption: we never receive a partial application of a binary operator.

                // translate_operator_application might be invoked to translate a unit clause.
                assert!(!operands.is_empty());

                let mut ret: TstpFormula;

                if operands.len() >= 2 {
                    ret = TstpFormula::BinaryOperatorApp(
                        binary_op.clone(),
                        Box::new(operands_tstp[0].clone()),
                        Box::new(operands_tstp[1].clone()),
                    );
                } else {
                    // { operands.len() == 1 }
                    // We should be translating just a unit clause
                    assert!(operator == Operator::Or);

                    ret = TstpFormula::BinaryOperatorApp(
                        binary_op.clone(),
                        Box::new(TstpFormula::NullaryOperatorApp(TstpNullaryOperator::False)),
                        Box::new(operands_tstp[0].clone()),
                    );
                }

                // TODO: some better way to skip the first 2 positions?
                let mut position = 0;
                operands_tstp.iter().for_each(|operand| {
                    if position > 1 {
                        ret = TstpFormula::BinaryOperatorApp(
                            binary_op.clone(),
                            Box::new(ret.clone()),
                            Box::new(operand.clone()),
                        );
                    } else {
                        // { position <= 1 }
                        position += 1;
                    }
                });

                ret
            }
        }
    }
}

impl VecToVecTranslator<'_, TstpAnnotatedFormula, TstpFormula, TstpType, TstpOperator>
    for TstpTranslator
{
    fn get_mut_translator_data(&mut self) -> &mut TranslatorData<TstpFormula, TstpProof> {
        &mut self.translation
    }

    fn get_read_translator_data(&self) -> &TranslatorData<TstpFormula, TstpProof> {
        &self.translation
    }

    // /// Inspects a given Alethe step from which we want to extract its id,
    // /// also verifying that it is a proper "previous step" from another subproof's
    // /// last step.
    // fn get_previous_step_id(previous_step: &Option<Rc<ProofNode>>) -> TstpFormula {
    //     // TODO: abstract this into a procedure
    //     // Include, as premise, the previous step.
    //     match previous_step {
    //         Some(step) => {
    //             match step.deref() {
    //                 ProofNode::Step(StepNode { id, .. }) => TstpFormula::Variable(id.clone()),

    //                 ProofNode::Subproof(SubproofNode { last_step, .. }) => {
    //                     // The previous step is the closing step of a subproof.
    //                     // It is represented as a single SubproofNode. We look
    //                     // for the actual last step of this subproof.
    //                     match last_step.deref() {
    //                         ProofNode::Step(StepNode { id, .. }) => TstpFormula::Variable(id.clone()),

    //                         _ => {
    //                             // It shouldn't be another kind of ProofNode
    //                             panic!();
    //                         }
    //                     }
    //                 }

    //                 ProofNode::Assume { .. } => {
    //                     // It shouldn't be another kind of ProofNode
    //                     panic!();
    //                 }
    //             }
    //         }

    //         _ => {
    //             // There should be some previous step.
    //             panic!();
    //         }
    //     }
    // }

    // /// Returns the identifier (as an `TstpFormula`) of the last context
    // /// actually introduced within the proof certificate.
    // /// PRE: { 0 < `self.contexts_opened`}
    // fn get_last_introduced_context_id(&self) -> TstpFormula {
    //     // TODO: do not hard-code this string
    //     TstpFormula::Variable(
    //         String::from("ctx")
    //             + &(self.alethe_scopes.get_last_introduced_context_index() + 1).to_string(),
    //     )
    // }

    // /// Encapsulates the mechanism used to generate fresh identifiers of contexts.
    // fn generate_new_context_id(&self) -> String {
    //     // TODO: do not hard-code this string
    //     String::from("ctx") + &self.alethe_scopes.get_contexts_opened().to_string()
    // }

    /// Abstracts the steps required to define and push a new context.
    /// PARAMS:
    /// `option_ctx_params`: a vector with the variables introduced by the context (optionally)
    fn define_push_new_context(&mut self, _option_ctx_params: Option<Vec<TstpFormula>>) {
        let _new_context_id = self.generate_new_context_id();

        // match option_ctx_params {
        //     // First call to the method. We create a dummy context with no actual
        //     // information.
        //     // TODO: do we really need to introduce this dummy context?
        //     None => {
        //         self.tstp_proof.push(TstpCommand::Define {
        //             name: new_context_id.clone(), // TODO: performance?
        //             typed_params: TstpList { list: vec![] },
        //             term: TstpFormula::True,
        //             attrs: Vec::new(),
        //         });

        //         self.tstp_proof.push(TstpCommand::Assume {
        //             // TODO: do not hard-code this string
        //             name: String::from("context"),
        //             term: TstpFormula::Variable(new_context_id.clone()),
        //         });
        //     }

        //     Some(ctx_params) => {
        //         // { not ctx_params.is_empty() }
        //         self.tstp_proof.push(TstpCommand::Define {
        //             name: new_context_id.clone(),
        //             // TODO: do not hard-code this string
        //             typed_params: TstpList { list: Vec::new() },
        //             term: TstpFormula::App(self.alethe_signature.ctx.clone(), ctx_params),
        //             attrs: Vec::new(),
        //         });

        //         // TODO: should we step-pop this context, when closing the
        //         // scope?
        //         // (assume-push context ctxn)
        //         self.tstp_proof.push(TstpCommand::AssumePush {
        //             name: String::from("context"),
        //             term: TstpFormula::Variable(new_context_id.clone()),
        //         });
        //     }
        // }
    }

    /// Abstracts the process of traversing a given context, identifying the fixed
    /// variables and the substitutions. Returns the corresponding list of
    /// variables and substitutions to be used when building a @ctx.
    fn process_anchor_context(&mut self, _context: Vec<&AnchorArg>) -> Vec<TstpFormula> {
        let mut _ctx_params: Vec<TstpFormula> = Vec::new();
        // Variables bound by the context
        let mut _context_domain: Vec<TstpFormula> = Vec::new();
        // Actual substitution induced by the context
        let mut _subst: Vec<TstpFormula> = Vec::new();
        // Dummy initial value
        let mut _tstp_sort: TstpFormula = TstpFormula::Variable("dummy".to_owned());

        // TODO
        // context.iter().for_each(|arg| match arg {
        //     AnchorArg::Variable((name, sort)) => {
        //         // TODO: either use borrows or implement
        //         // Copy trait for TstpFormulas
        //         tstp_sort = self.translate_term(sort);

        //         self.alethe_scopes
        //             .insert_variable_in_scope(name, &tstp_sort);

        //         context_domain.push(TstpFormula::List(vec![
        //             TstpFormula::Variable(name.clone()),
        //             tstp_sort.clone(),
        //         ]));
        //     }

        //     AnchorArg::Assign((name, sort), term) => {
        //         // TODO: either use borrows or implement
        //         // Copy trait for TstpFormulas
        //         tstp_sort = self.translate_term(sort);

        //         // TODO: ugly patch...
        //         let rhs: TstpFormula = match term.deref() {
        //             Term::Var(string, _) => TstpFormula::Variable(string.clone()),

        //             _ => self.translate_term(term),
        //         };

        //         context_domain.push(TstpFormula::List(vec![
        //             TstpFormula::Variable(name.clone()),
        //             tstp_sort.clone(),
        //         ]));

        //         self.alethe_scopes
        //             .insert_variable_in_scope(name, &tstp_sort);

        //         // match self.variables_in_scope.get_with_depth(name) {
        //         //     Some((depth, _)) => {
        //         //         if depth < self.variables_in_scope.height() - 1 {
        //         //             // This variable is bound somewhere else.  We
        //         //             // shadow any previous def.
        //         //             self.variables_in_scope
        //         //                 .insert(name.clone(), tstp_sort.clone());
        //         //         }
        //         //     }

        //         //     None => {
        //         //         // This variable is not bound somewhere else.
        //         //         self.variables_in_scope
        //         //             .insert(name.clone(), tstp_sort.clone());
        //         //     }
        //         // }

        //         // Substitution map of the form name -> rhs: we
        //         // reify it as a term (= name rhs)
        //         subst.push(TstpFormula::App(
        //             self.alethe_signature.eq.clone(),
        //             vec![TstpFormula::Variable(name.clone()), rhs],
        //         ));
        //     }
        // });

        // subst.push(self.get_last_introduced_context_id());

        // // Add typed params.
        // if context_domain.is_empty() {
        //     // Empty VarList
        //     ctx_params.push(TstpFormula::Variable(self.alethe_signature.varlist_nil.clone()));
        // } else {
        //     // TODO: shouldn' we build it with @varlist?
        //     ctx_params.push(TstpFormula::List(context_domain));
        // }

        // // Concat (and...)
        // ctx_params.push(TstpFormula::App(self.alethe_signature.and.clone(), subst));

        _ctx_params
    }

    /// Translates a given Term into its corresponding `TstpFormula`, possibly
    /// modifying scoping information contained in self, to deal with
    /// translation of binding constructions.
    fn translate_term(&mut self, term: &Term) -> TstpFormula {
        match term {
            Term::Const(constant) => TstpTranslator::translate_constant(constant),

            // TODO: how do we deal with this?
            Term::Sort(_sort) => {
                // TstpTranslator::translate_sort(sort),
                println!("Not known translation for sort {:?}", _sort);
                panic!();
            }

            Term::Op(operator, operands) => {
                let operands_tstp: Vec<TstpFormula> = operands
                    .iter()
                    .map(|operand| self.translate_term(operand))
                    .collect();

                match self.translate_operator(*operator) {
                    TstpOperator::NullaryOperator(nullary_op) => {
                        assert!(operands.is_empty());

                        TstpFormula::NullaryOperatorApp(nullary_op)
                    }

                    TstpOperator::UnaryOperator(unary_op) => {
                        assert!(operands.len() == 1);

                        TstpFormula::UnaryOperatorApp(unary_op, Box::new(operands_tstp[0].clone()))
                    }

                    TstpOperator::BinaryOperator(binary_op) => TstpFormula::BinaryOperatorApp(
                        binary_op,
                        Box::new(operands_tstp[0].clone()),
                        Box::new(operands_tstp[1].clone()),
                    ),
                }
            }

            // TODO: not considering the sort of the variable.
            Term::Var(string, _) => {
                // Check if it is a variable introduced by some binder
                match self
                    .get_read_translator_data()
                    .alethe_scopes
                    .get_variable_in_scope(string)
                {
                    Some(_) => self.build_var_binding(string),

                    None => TstpFormula::Variable(string.clone()),
                }
            }

            Term::App(fun, params) => {
                let mut fun_params = Vec::new();

                params.iter().for_each(|param| {
                    fun_params.push(self.translate_term(param));
                });

                TstpFormula::FunctorApp((*fun).to_string(), fun_params)
            }

            Term::Let(binding_list, _scope) => {
                // New scope.
                self.get_mut_translator_data()
                    .alethe_scopes
                    .open_non_context_scope();

                let (_translated_binding_list, _translated_values) =
                    self.translate_let_binding_list(binding_list);

                // TODO
                // match translated_binding_list {
                //     TstpFormula::List(ref bindings) => {
                //         bindings.iter().for_each(|var| match var {
                //             TstpFormula::Var(id, sort) => {
                //                 self.alethe_scopes.insert_variable_in_scope(id, sort);
                //             }

                //             _ => {
                //                 // It shouldn't be diff. than TstpFormula::Var.
                //                 panic!();
                //             }
                //         });
                //     }

                //     _ => {
                //         // It shouldn't be diff. than TstpFormula::List.
                //         panic!();
                //     }
                // }

                // let final_let_trans = TstpFormula::HOApp(
                //     Box::new(TstpFormula::App(
                //         self.alethe_signature.let_binder.clone(),
                //         vec![translated_binding_list, self.translate_term(scope)],
                //     )),
                //     translated_values,
                // );

                // self.alethe_scopes.close_scope();

                // final_let_trans
                TstpFormula::Variable("dummy".to_owned())
            }

            Term::Binder(_binder, binding_list, _scope) => {
                // New scope to shadow those context variables that
                // now bound by this binder.
                // TODO: reusing variables_in_scope concept
                // for this new kind of scope (not the one
                // related with contexts introduced through
                // "anchor" commands).
                self.get_mut_translator_data()
                    .alethe_scopes
                    .open_non_context_scope();
                let _translated_bindings = self.translate_binding_list(binding_list);
                // match translated_bindings {
                //     TstpFormula::List(ref bindings) => {
                //         bindings.iter().for_each(|var| match var {
                //             TstpFormula::Var(id, sort) => {
                //                 self.alethe_scopes.insert_variable_in_scope(id, sort);
                //             }

                //             _ => {
                //                 // It shouldn't be diff. than TstpFormula::Var.
                //                 panic!();
                //             }
                //         });
                //     }

                //     _ => {
                //         // It shouldn't be diff. than TstpFormula::List.
                //         panic!();
                //     }
                // }

                // let translated_binder = match binder {
                //     Binder::Forall => TstpFormula::App(
                //         self.alethe_signature.forall_binder.clone(),
                //         vec![translated_bindings, self.translate_term(scope)],
                //     ),

                //     Binder::Exists => TstpFormula::App(
                //         self.alethe_signature.exists_binder.clone(),
                //         vec![translated_bindings, self.translate_term(scope)],
                //     ),

                //     Binder::Choice => {
                //         let choice_var: TstpFormula;
                //         // There should be just one defined variable.
                //         match &translated_bindings {
                //             TstpFormula::List(list) => {
                //                 assert!(list.len() == 1);
                //                 match &list[0] {
                //                     TstpFormula::Var(var_name, ..) => {
                //                         choice_var = TstpFormula::Variable(var_name.to_string());
                //                     }

                //                     _ => panic!(),
                //                 }
                //             }

                //             _ => panic!(),
                //         };

                //         TstpFormula::App(
                //             self.alethe_signature.choice_binder.clone(),
                //             vec![translated_bindings, choice_var, self.translate_term(scope)],
                //         )
                //     }

                //     // TODO: complete
                //     Binder::Lambda => TstpFormula::App(
                //         self.alethe_signature.exists_binder.clone(),
                //         vec![translated_bindings, self.translate_term(scope)],
                //     ),
                // };

                // Closing the context...
                self.get_mut_translator_data().alethe_scopes.close_scope();
                // self.local_steps.pop();

                // translated_binder
                TstpFormula::Variable("dummy".to_owned())
            }

            // TODO: complete
            Term::ParamOp { .. } => panic!(),
        }
    }

    /// TODO: this method was used in the context of Eunoia. Repurpose it
    /// for TSTP.
    /// TODO: In the THF, TFF, and FOF languages, every variable in a Formula
    /// must be bound by a preceding quantification with adequate scope.
    fn build_var_binding(&self, id: &str) -> TstpFormula {
        // TODO: using clone, ugly...
        let _sort = match self
            .get_read_translator_data()
            .alethe_scopes
            .get_variable_in_scope(&id.to_owned())
        {
            Some(value) => value.clone(),

            None => {
                // Not satisfying pre-condition
                panic!()
            }
        };

        // TODO:
        TstpFormula::Variable("dummy".to_owned())

        // TstpFormula::App(
        //     self.alethe_signature.var.clone(),
        //     vec![
        //         TstpFormula::List(vec![TstpFormula::List(vec![
        //             TstpFormula::Variable(id.clone()),
        //             sort,
        //         ])]),
        //         TstpFormula::Variable(id.clone()),
        //     ],
        // )
    }

    /// Translates `BindingList` constructs, as used for binder terms forall, exists,
    /// choice and lambda. The "let" binder uses the same construction but assigns to
    /// it a different semantics. See `translate_let_binding_list` for its translation.
    fn translate_binding_list(&mut self, binding_list: &BindingList) -> TstpFormula {
        let mut _ret: Vec<TstpFormula> = Vec::new();

        binding_list.iter().for_each(|sorted_var| {
            let (_name, _sort) = sorted_var;
            // ret.push(TstpFormula::Var(
            //     name.clone(),
            //     Box::new(self.translate_term(sort)),
            // ));
        });

        // TstpFormula::List(ret)
        TstpFormula::Variable("dummy".to_owned())
    }

    /// Translates a `BindingList` as required by our definition of @let: it builds a list
    /// of pairs (variable, type) for the binding occurrences, and returns this coupled with
    /// the original list of actual values, as a `@VarList`.
    fn translate_let_binding_list(
        &mut self,
        binding_list: &BindingList,
    ) -> (TstpFormula, Vec<TstpFormula>) {
        let mut _binding_occ: Vec<TstpFormula> = Vec::new();
        let mut values = Vec::new();

        binding_list.iter().for_each(|sorted_var| {
            let (_name, value) = sorted_var;
            let translated_value = self.translate_term(value);
            // TODO: too much cloning...
            // binding_occ.push(TstpFormula::Var(
            //     name.clone(),
            //     // TODO: do not hardcode this
            //     Box::new(TstpFormula::App(
            //         "eo::typeof".to_owned(),
            //         vec![translated_value.clone()],
            //     )),
            // ));

            values.push(translated_value.clone());
        });

        // (TstpFormula::List(binding_occ), values)
        (TstpFormula::Variable("dummy".to_owned()), values)
    }

    /// NOTE: In this case, we would not need a reference to self. Yet,
    /// this is not the case for `Alethe2Eunoia`.
    fn translate_operator(&self, operator: Operator) -> TstpOperator {
        match operator {
            // TODO: put this into theory.rs
            // Logic
            Operator::And => TstpOperator::BinaryOperator(TstpBinaryOperator::And),

            Operator::Or => TstpOperator::BinaryOperator(TstpBinaryOperator::Or),

            Operator::Xor => TstpOperator::BinaryOperator(TstpBinaryOperator::Xor),

            Operator::Not => TstpOperator::UnaryOperator(TstpUnaryOperator::Not),

            Operator::Implies => TstpOperator::BinaryOperator(TstpBinaryOperator::Implies),

            Operator::Ite => TstpOperator::BinaryOperator(TstpBinaryOperator::Ite),

            Operator::True => TstpOperator::NullaryOperator(TstpNullaryOperator::True),

            Operator::False => TstpOperator::NullaryOperator(TstpNullaryOperator::False),

            // Order / Comparison.
            Operator::Equals => TstpOperator::BinaryOperator(TstpBinaryOperator::Equality),

            Operator::GreaterThan => TstpOperator::BinaryOperator(TstpBinaryOperator::Greater),

            Operator::GreaterEq => TstpOperator::BinaryOperator(TstpBinaryOperator::GreaterEq),

            Operator::LessThan => TstpOperator::BinaryOperator(TstpBinaryOperator::Less),

            Operator::LessEq => TstpOperator::BinaryOperator(TstpBinaryOperator::LessEq),

            // TODO:?
            Operator::Distinct => TstpOperator::BinaryOperator(TstpBinaryOperator::Inequality),

            // Arithmetic
            Operator::Add => TstpOperator::BinaryOperator(TstpBinaryOperator::Sum),

            Operator::Sub => TstpOperator::BinaryOperator(TstpBinaryOperator::Difference),

            Operator::Mult => TstpOperator::BinaryOperator(TstpBinaryOperator::Product),

            Operator::IntDiv => TstpOperator::BinaryOperator(TstpBinaryOperator::QuotientE),

            Operator::RealDiv => TstpOperator::BinaryOperator(TstpBinaryOperator::Quotient),

            _ => {
                println!("No defined translation for operator {:?}", operator);
                panic!()
            }
        }
    }

    fn translate_constant(constant: &Constant) -> TstpFormula {
        match constant {
            Constant::Integer(integer) => TstpFormula::Integer(integer.clone()),

            Constant::Real(real) => TstpFormula::Real(real.clone()),

            Constant::String(string) => TstpFormula::DistinctObject(string.clone()),

            // TODO
            Constant::BitVec(..) => panic!(),
        }
    }

    // TODO:
    fn translate_sort(sort: &Sort) -> TstpType {
        match sort {
            Sort::Real => TstpType::Real,

            // User-defined sort
            // TODO: what about args?
            Sort::Atom(string, ..) => TstpType::UserDefined(string.clone()),

            Sort::Function(sorts) => {
                // TODO: is this correct?
                assert!(sorts.len() >= 2,);

                let return_sort;

                match sorts.last() {
                    Some(term) => {
                        match (*term).deref() {
                            Term::Sort(sort) => {
                                return_sort = TstpTranslator::translate_sort(sort);
                            }

                            _ => {
                                // TODO: is this correct?
                                panic!();
                            }
                        }
                    }

                    None => {
                        // TODO: is this correct?
                        panic!();
                    }
                };

                let mut sorts_params = Vec::new();

                for (pos, rc_sort) in sorts.iter().enumerate() {
                    if pos < sorts.len() - 1 {
                        match rc_sort.deref() {
                            Term::Sort(sort) => {
                                sorts_params.push(TstpTranslator::translate_sort(sort));
                            }

                            _ => {
                                // TODO: is this correct?
                                panic!();
                            }
                        }
                    }
                }

                // TODO: no attrs?
                TstpType::Fun(sorts_params, Box::new(return_sort))
            }

            Sort::Bool => TstpType::Bool,

            _ => {
                TstpType::Real
                // TODO:
            }
        }
    }

    /// Implements the translation of an Alethe `Assume`, taking into
    /// account technical differences in the way Alethe rules are
    /// expressed within Tstp.
    fn translate_assume(
        &mut self,
        _id: &str,
        _depth: usize,
        term: &Rc<Term>,
    ) -> TstpAnnotatedFormula {
        let translated_term = self.translate_term(term);

        self.new_annotated_formula(
            TstpLanguage::Tff,
            TstpFormulaRole::Axiom,
            translated_term,
            TstpAnnotatedFormulaSource::Empty,
            "nil".to_owned(),
        )
    }

    /// Implements the translation of an Alethe `ProofStep`, taking into
    /// account technical differences in the way Alethe rules are
    /// expressed within Tstp.
    /// Updates `self.tstp_proof`.
    fn translate_step(&mut self, node: &ProofNode) {
        let mut alethe_premises: Vec<TstpFormula> = Vec::new();

        match node {
            ProofNode::Step(StepNode {
                id: _,
                depth: _,
                clause,
                rule,
                premises,
                args,
                discharge: _,
                previous_step: _,
            }) => {
                // Add premises actually present in the original step command.
                alethe_premises.extend(
                    premises
                        .iter()
                        .map(|node| TstpFormula::Variable(String::from(node.deref().id())))
                        .collect::<Vec<TstpFormula>>(),
                );

                // NOTE: in ProofStep, clause has type
                // Vec<Rc<Term>>, though it represents an
                // invocation of Alethe's cl operator
                // TODO: we are always adding the conclusion clause
                let conclusion: TstpFormula = if clause.is_empty() {
                    // TODO: ?
                    // TstpFormula::Variable(self.alethe_signature.empty_cl.clone())
                    TstpFormula::Variable("this should an empty clause".to_owned())
                } else {
                    // {!clause.is_empty()}
                    self.translate_operator_application(Operator::Or, clause)

                    // TstpFormula::App(
                    //     self.alethe_signature.cl.clone(),
                    //     clause
                    //         .iter()
                    //         .map(|term| self.translate_term(term))
                    //         .collect(),
                    // )
                };

                // NOTE: not adding conclusion clause to this list
                let mut tstp_arguments: Vec<TstpFormula> = Vec::new();

                args.iter().for_each(|arg| {
                    tstp_arguments.push(self.translate_term(arg));
                });

                // TODO: develop some generic programmatic way to deal with each rule's
                // semantics instead of this
                match rule.as_str() {
                    "and_neg" => {
                        let annotated_formula = self.new_annotated_formula(
                            TstpLanguage::Tff,
                            TstpFormulaRole::Plain,
                            conclusion,
                            TstpAnnotatedFormulaSource::Empty,
                            "".to_owned(),
                        );

                        self.get_mut_translator_data()
                            .translated_proof
                            .push(annotated_formula);
                    }

                    _ => {
                        let annotated_formula = self.new_annotated_formula(
                            TstpLanguage::Tff,
                            TstpFormulaRole::Plain,
                            conclusion,
                            TstpAnnotatedFormulaSource::Empty,
                            "".to_owned(),
                        );

                        self.get_mut_translator_data()
                            .translated_proof
                            .push(annotated_formula);
                    }
                }
            }

            _ => {
                // Method should be called upon a StepNode
                panic!();
            }
        }
    }

    // TODO: make tstp_prelude an attribute of TstpTranslator
    /// Translates only an SMT-lib problem prelude.
    fn translate_problem_2_vect(&mut self, problem: &Problem) -> TstpProof {
        let Problem { prelude, premises } = problem;

        let mut tstp_problem: TstpProof = Vec::new();

        // Translation of the definitions of constants.
        let ProblemPrelude {
            sort_declarations,
            function_declarations,
            ..
        } = prelude;

        // TODO: use this to guess the language to be used. Something else?
        // match logic {
        //     Some(logic_name) => {
        //         tstp_prelude.push(TstpCommand::SetLogic { name: logic_name.clone() });
        //     }

        //     None => {}
        // }

        sort_declarations.iter().for_each(|pair| {
            let annotated_formula = self.new_annotated_formula(
                TstpLanguage::Tff,
                TstpFormulaRole::Type,
                TstpFormula::Typing(
                    Box::new(TstpFormula::Variable(pair.0.clone())),
                    TstpType::Universe,
                ),
                TstpAnnotatedFormulaSource::Empty,
                "".to_owned(),
            );

            tstp_problem.push(annotated_formula);
        });

        function_declarations.iter().for_each(|pair| {
            let tstp_type: TstpType = match (pair.1).deref() {
                Term::Sort(sort) => TstpTranslator::translate_sort(sort),

                _ => {
                    // It shouldn't be something different than a Sort.
                    println!(" {:?} expected to be a Sort.", &pair.1);
                    panic!();
                }
            };

            let annotated_formula = self.new_annotated_formula(
                TstpLanguage::Tff,
                TstpFormulaRole::Type,
                TstpFormula::Typing(Box::new(TstpFormula::Variable(pair.0.clone())), tstp_type),
                TstpAnnotatedFormulaSource::Empty,
                "".to_owned(),
            );

            // TODO: abstract this into a method to generate annotated formulas
            tstp_problem.push(annotated_formula);
        });

        // Translation of assertions: we represent them as
        // axioms.
        premises.iter().for_each(|assertion| {
            let translated_assertion = self.translate_term(assertion);

            let annotated_formula = self.new_annotated_formula(
                // TODO: some other language?
                TstpLanguage::Tff,
                // "some_formula_name".to_owned(),
                TstpFormulaRole::Axiom,
                translated_assertion,
                TstpAnnotatedFormulaSource::Empty,
                "".to_owned(),
            );

            tstp_problem.push(annotated_formula);
        });

        tstp_problem
    }
}

impl Default for TstpTranslator {
    fn default() -> Self {
        Self::new()
    }
}

impl Translator for TstpTranslator {
    type Output = TstpProof;

    fn translate<'a>(&'a mut self, proof: &Rc<ProofNode>) -> &'a Self::Output {
        self.translate_2_vect(proof)
    }

    fn translate_problem(&mut self, problem: &Problem) -> Self::Output {
        self.translate_problem_2_vect(problem)
    }
}
