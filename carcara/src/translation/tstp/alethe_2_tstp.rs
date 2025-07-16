//! Translator for `TstpProof`.
use crate::ast::*;
use crate::translation::tstp::tstp_ast::*;
use crate::translation::Translator;
use crate::translation::TranslatorData;
use crate::translation::VecToVecTranslator;

// Deref for ast::rc::Rc<Term>
use std::ops::Deref;

pub struct TstpTranslator {
    translation: TranslatorData<TstpFormula, TstpProof>,
}

impl TstpTranslator {
    pub fn new() -> Self {
        Self { translation: TranslatorData::new() }
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
    fn process_anchor_context(&mut self, _context: &[AnchorArg]) -> Vec<TstpFormula> {
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
                println!("No sabemos como traducir sort {:?}", _sort);
                panic!();
            }

            Term::Op(operator, operands) => {
                let operands_tstp: Vec<TstpFormula> = operands
                    .iter()
                    .map(|operand| self.translate_term(operand))
                    .collect();

                TstpFormula::OperatorApp(self.translate_operator(*operator), operands_tstp)
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

    fn translate_operator(&self, operator: Operator) -> TstpOperator {
        match operator {
            // TODO: put this into theory.rs
            // Logic
            Operator::And => TstpOperator::And,

            Operator::Or => TstpOperator::Or,

            Operator::Xor => TstpOperator::Xor,

            Operator::Not => TstpOperator::Not,

            Operator::Implies => TstpOperator::Implies,

            Operator::Ite => TstpOperator::Ite,

            Operator::True => TstpOperator::True,

            Operator::False => TstpOperator::False,

            // Order / Comparison.
            Operator::Equals => TstpOperator::Equality,

            Operator::GreaterThan => TstpOperator::Greater,

            Operator::GreaterEq => TstpOperator::GreaterEq,

            Operator::LessThan => TstpOperator::Less,

            Operator::LessEq => TstpOperator::LessEq,

            // TODO:?
            Operator::Distinct => TstpOperator::Inequality,

            // Arithmetic
            Operator::Add => TstpOperator::Sum,

            Operator::Sub => TstpOperator::Difference,

            Operator::Mult => TstpOperator::Product,

            Operator::IntDiv => TstpOperator::QuotientE,

            Operator::RealDiv => TstpOperator::Quotient,

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
        id: &str,
        _depth: usize,
        term: &Rc<Term>,
    ) -> TstpAnnotatedFormula {
        TstpAnnotatedFormula::new(
            TstpLanguage::Tff,
            id.to_owned(),
            TstpFormulaRole::Axiom,
            self.translate_term(term),
            // TODO: ?
            "nil".to_owned(),
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
                rule: _,
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
                let _conclusion: TstpFormula = if clause.is_empty() {
                    // TODO: ?
                    // TstpFormula::Variable(self.alethe_signature.empty_cl.clone())
                    TstpFormula::Variable("dummy".to_owned())
                } else {
                    // {!clause.is_empty()}
                    TstpFormula::Variable("dummy_else".to_owned())
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
                // semantics (as explained in theory.rs) instead of this
                // match rule.as_str() {
                //     "la_generic" => {
                //         self.tstp_proof.push(TstpCommand::Step {
                //             id: id.clone(),
                //             conclusion_clause: Some(conclusion),
                //             rule: self.alethe_signature.la_generic.clone(),
                //             // TODO: should we check if alethe_premises == []?
                //             premises: TstpList { list: vec![] },
                //             // The coefficients are one single argument.  This means they
                //             // must be be wrapped in a single function call using an n-ary
                //             // function.
                //             arguments: TstpList {
                //                 list: vec![TstpFormula::App(
                //                     self.alethe_signature.add.clone(),
                //                     tstp_arguments,
                //                 )],
                //             },
                //         });
                //     }

                //     "let" => {
                //         // Include, as premises, previous step from the actual subproof.
                //         alethe_premises.push(Self::get_previous_step_id(previous_step));

                //         self.tstp_proof.push(TstpCommand::StepPop {
                //             id: id.clone(),
                //             conclusion_clause: Some(conclusion),
                //             rule: self.alethe_signature.let_rule.clone(),
                //             premises: TstpList { list: alethe_premises },
                //             arguments: TstpList { list: tstp_arguments },
                //         });
                //     }

                //     "refl" => {
                //         // TODO: do not hard-code this string
                //         tstp_arguments.push(TstpFormula::Variable("context".to_owned()));

                //         self.tstp_proof.push(TstpCommand::Step {
                //             id: id.clone(),
                //             conclusion_clause: Some(conclusion),
                //             rule: self.alethe_signature.refl.clone(),
                //             premises: TstpList { list: alethe_premises },
                //             arguments: TstpList { list: tstp_arguments },
                //         });
                //     }

                //     "bind" => {
                //         // Include, as premise, the previous step.
                //         alethe_premises.push(Self::get_previous_step_id(previous_step));

                //         // We include, as argument, the context surrounding this
                //         // subproof's context.
                //         tstp_arguments.push(self.get_last_introduced_context_id());

                //         // :assumption: ctx
                //         self.tstp_proof.push(TstpCommand::StepPop {
                //             id: id.clone(),
                //             conclusion_clause: Some(conclusion),
                //             rule: self.alethe_signature.bind.clone(),
                //             premises: TstpList { list: alethe_premises },
                //             arguments: TstpList { list: tstp_arguments },
                //         });
                //     }

                //     "subproof" => {
                //         // TODO: check this
                //         // The command (as mechanized in Tstp) gets the formula proven
                //         // through an "assumption", hence, we use StepPop.
                //         // The discharged assumptions (specified, in Alethe, through the
                //         // "discharge" formal parameter), will be pushed
                //         // NOTE: spurious value so the compiler won't comply
                //         let mut implied_conclusion: TstpFormula = TstpFormula::Variable("dummy".to_owned());

                //         // Assuming that the conclusion is of the form
                //         // not φ1, ..., not φn, ψ
                //         // extract ψ
                //         let mut premise = TstpFormula::App(
                //             self.alethe_signature.cl.clone(),
                //             vec![self.alethe_signature.extract_consequent(&conclusion)],
                //         );

                //         let mut cl_disjuncts: Vec<TstpFormula> = vec![];

                //         // Id of the premise step
                //         let mut id_premise: Symbol = "".to_owned();

                //         // TODO: some more efficient way to deal with
                //         // the fact that we use a "stack" of assumptions?
                //         let mut discharge_copy = discharge.clone();
                //         discharge_copy.reverse();
                //         discharge_copy.iter().for_each(|assumption| {
                //             // TODO: we are discarding vector premises
                //             match assumption.deref() {
                //                 // TODO: ugly?
                //                 ProofNode::Assume { id: _, depth: _, term } => {
                //                     cl_disjuncts = vec![TstpFormula::App(
                //                         self.alethe_signature.not.clone(),
                //                         vec![self.translate_term(term)],
                //                     )];

                //                     cl_disjuncts.append(
                //                         &mut self.alethe_signature.extract_cl_disjuncts(&premise),
                //                     );

                //                     implied_conclusion = TstpFormula::App(
                //                         self.alethe_signature.cl.clone(),
                //                         // TODO: too much cloning...
                //                         cl_disjuncts.clone(),
                //                     );

                //                     // Get id of previous step
                //                     id_premise = self.tstp_proof[self.tstp_proof.len() - 1]
                //                         .get_step_id();

                //                     self.tstp_proof.push(TstpCommand::StepPop {
                //                         // TODO: change id!
                //                         // TODO: ethos does not complain about repeated ids
                //                         id: id.clone(),
                //                         conclusion_clause: Some(implied_conclusion.clone()),
                //                         rule: self.alethe_signature.subproof.clone(),
                //                         premises: TstpList {
                //                             list: vec![TstpFormula::Variable(id_premise.clone())],
                //                         },
                //                         arguments: TstpList { list: tstp_arguments.clone() },
                //                     });

                //                     // TODO: too much cloning...
                //                     premise = implied_conclusion.clone();
                //                 }

                //                 _ => {
                //                     // TODO: it shouldn't be a ProofNode different than an Assume
                //                     panic!();
                //                 }
                //             }
                //         });
                //     }

                //     "forall_inst" => {
                //         // TODO: we are discarding premises arguments
                //         self.tstp_proof.push(TstpCommand::Step {
                //             id: id.clone(),
                //             conclusion_clause: Some(conclusion),
                //             rule: self.alethe_signature.forall_inst.clone(),
                //             premises: TstpList { list: Vec::new() },
                //             arguments: TstpList {
                //                 list: vec![TstpFormula::App(
                //                     self.alethe_signature.varlist_cons.clone(),
                //                     tstp_arguments,
                //                 )],
                //             },
                //         });
                //     }

                //     "onepoint" => {
                //         self.tstp_proof.push(TstpCommand::StepPop {
                //             id: id.clone(),
                //             conclusion_clause: Some(conclusion),
                //             rule: self.alethe_signature.onepoint.clone(),
                //             premises: TstpList { list: alethe_premises },
                //             arguments: TstpList { list: tstp_arguments },
                //         });
                //     }

                //     "sko_ex" => {
                //         // Include, as premise, the previous step.
                //         alethe_premises.push(Self::get_previous_step_id(previous_step));

                //         // We include, as argument, the context surrounding this
                //         // subproof's context.
                //         tstp_arguments.push(self.get_last_introduced_context_id());

                //         self.tstp_proof.push(TstpCommand::StepPop {
                //             id: id.clone(),
                //             conclusion_clause: Some(conclusion),
                //             rule: self.alethe_signature.sko_ex.clone(),
                //             premises: TstpList { list: alethe_premises },
                //             arguments: TstpList { list: tstp_arguments },
                //         });
                //     }

                //     _ => {
                //         self.tstp_proof.push(TstpCommand::Step {
                //             id: id.clone(),
                //             conclusion_clause: Some(conclusion),
                //             rule: rule.clone(),
                //             premises: TstpList { list: alethe_premises },
                //             arguments: TstpList { list: tstp_arguments },
                //         });
                //     }
                // }
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
            tstp_problem.push(TstpAnnotatedFormula::new(
                // TODO: some other language?
                TstpLanguage::Tff,
                pair.0.clone(),
                TstpFormulaRole::Type,
                TstpFormula::Typing(
                    Box::new(TstpFormula::Variable(pair.0.clone())),
                    TstpType::Universe,
                ),
                "".to_owned(),
                "".to_owned(),
            ));
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

            // TODO: abstract this into a method to generate annotated formulas
            tstp_problem.push(TstpAnnotatedFormula::new(
                // TODO: some other language?
                TstpLanguage::Tff,
                pair.0.clone(),
                TstpFormulaRole::Type,
                TstpFormula::Typing(Box::new(TstpFormula::Variable(pair.0.clone())), tstp_type),
                "".to_owned(),
                "".to_owned(),
            ));
        });

        // Translation of assertions: we represent them as
        // axioms.
        premises.iter().for_each(|assertion| {
            // TODO: abstract this into a method to generate annotated formulas
            tstp_problem.push(TstpAnnotatedFormula::new(
                // TODO: some other language?
                TstpLanguage::Tff,
                "some_name".to_owned(),
                TstpFormulaRole::Axiom,
                self.translate_term(assertion),
                "".to_owned(),
                "".to_owned(),
            ));
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
