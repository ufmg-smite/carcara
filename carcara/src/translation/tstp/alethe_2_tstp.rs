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
    /// - generates a new name
    /// - builds the corresponding AST
    /// - maintains a correspondence between the given name and the formula
    fn new_annotated_formula(
        &mut self,
        step_id: &str,
        language: TstpLanguage,
        role: TstpFormulaRole,
        formula: TstpFormula,
        source: TstpAnnotatedFormulaSource,
        useful_info: Symbol,
    ) -> TstpAnnotatedFormula {
        let formula_name = self.new_formula_name(step_id, &role);

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
    fn new_formula_name(&mut self, step_id: &str, role: &TstpFormulaRole) -> String {
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
            TstpFormulaRole::Assumption => {
                // TODO: for the moment we are just using Alethe step's id.
                // new_name = "assumption".to_owned();
                new_name = step_id.to_owned();
            }

            TstpFormulaRole::Axiom => {
                new_name = "axiom".to_owned();
                new_name += &("_".to_owned() + &self.formulas_count[role].to_string());
            }

            TstpFormulaRole::Lemma => {
                // TODO: for the moment we are just using Alethe step's id.
                // new_name = "lemma".to_owned();
                new_name = step_id.to_owned();
            }

            TstpFormulaRole::Conjecture => {
                // TODO: for the moment we are just using Alethe step's id.
                // new_name = "conjecture".to_owned();
                new_name = step_id.to_owned();
            }

            TstpFormulaRole::Hypothesis => {
                // TODO: for the moment we are just using Alethe step's id.
                // new_name = "hypothesis".to_owned();
                new_name = step_id.to_owned();
            }

            TstpFormulaRole::Logic => {
                // TODO: for the moment we are just using Alethe step's id.
                // new_name = "logic".to_owned();
                new_name = step_id.to_owned();
            }

            TstpFormulaRole::Type => {
                // TODO: it could be better if we just name it after the
                // subject of the typing statement.
                new_name = "type".to_owned();
                new_name += &("_".to_owned() + &self.formulas_count[role].to_string());
            }

            TstpFormulaRole::Plain => {
                // TODO: for the moment we are just using Alethe step's id.
                // new_name = "plain".to_owned();
                new_name = step_id.to_owned();
            }
        }

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
                assert!(!operands_tstp.is_empty());

                let mut ret: TstpFormula;

                if operands_tstp.len() >= 2 {
                    ret = TstpFormula::BinaryOperatorApp(
                        binary_op.clone(),
                        Box::new(operands_tstp[0].clone()),
                        Box::new(operands_tstp[1].clone()),
                    );

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
                } else {
                    // { operands_tstp.len() == 1 }
                    // We should be translating just a unit clause
                    assert!(operator == Operator::Or);

                    ret = TstpFormula::BinaryOperatorApp(
                        binary_op.clone(),
                        Box::new(TstpFormula::NullaryOperatorApp(TstpNullaryOperator::False)),
                        Box::new(operands_tstp[0].clone()),
                    );
                }

                ret
            }

            TstpOperator::Functor(functor) => {
                assert!(!operands_tstp.is_empty());

                TstpFormula::FunctorApp(functor.clone(), operands_tstp)
            }
        }
    }

    ////////////////////////////////////////////
    // SZS ontology-related services.
    ////////////////////////////////////////////

    /// For a given step, classifies its rule according to its corresponding source
    /// (from TPTP's grammar). Builds the corresponding annotated formula, according
    /// to the previous classification.
    fn classify_source_build_step_term(
        &mut self,
        step_id: &str,
        rule_name: &str,
        conclusion: TstpFormula,
        premises: Vec<Symbol>,
        args: Vec<TstpFormula>,
        discharged_assumptions: Vec<Symbol>,
    ) -> TstpAnnotatedFormula {
        if TstpTranslator::is_tautology(rule_name) {
            self.new_annotated_formula(
                step_id,
                TstpLanguage::Tff,
                TstpFormulaRole::Plain,
                conclusion,
                TstpTranslator::get_tautology_formula_source(rule_name, args),
                "".to_owned(),
            )
        } else {
            // { not TstpTranslator::is_tautology(rule_name) }

            self.new_annotated_formula(
                step_id,
                TstpLanguage::Tff,
                TstpFormulaRole::Plain,
                conclusion,
                TstpTranslator::get_inference_formula_source(
                    rule_name,
                    premises,
                    discharged_assumptions,
                    args,
                ),
                "".to_owned(),
            )
        }
    }

    fn is_tautology(rule_name: &str) -> bool {
        // TODO: we should be extracting this from some "Alethe signature"
        // instead of hard-coding these names
        let tautologies = ["and_neg", "implies_neg1", "implies_neg2", "and_pos"];

        tautologies.contains(&rule_name)
    }

    /// Builds the corresponding `TstpAnnotatedFormulaSource`, for an
    /// step that represents the instantiation of a tautology.
    /// PRE : { `rule_name` is a tautology }
    fn get_tautology_formula_source(
        rule_name: &str,
        args: Vec<TstpFormula>,
    ) -> TstpAnnotatedFormulaSource {
        let source_introduced_type = TstpInternalSourceIntroducedType::Tautology;

        // Determine if the rule receives arguments.
        // TODO: abstract this into a process.
        let useful_info: TstpUsefulInfo = if args.is_empty() {
            TstpUsefulInfo::GeneralList(vec![TstpGeneralData::AtomicWord(rule_name.to_owned())])
        } else {
            // { !args.is_empty() }
            TstpUsefulInfo::GeneralList(vec![TstpGeneralData::GeneralFunction(
                rule_name.to_owned(),
                args,
            )])
        };
        // let useful_info: TstpUsefulInfo = if rule_name == "and_pos" {
        // } else {
        // };

        TstpAnnotatedFormulaSource::InternalSourceIntroduced(
            source_introduced_type,
            useful_info,
            vec![],
        )
    }

    /// Builds the corresponding `TstpAnnotatedFormulaSource`, for a
    /// step that represents the application of an inference rule.
    /// PRE : { `rule_name` is not a tautology }
    fn get_inference_formula_source(
        rule_name: &str,
        premises: Vec<Symbol>,
        discharged_assumptions: Vec<Symbol>,
        args: Vec<TstpFormula>,
    ) -> TstpAnnotatedFormulaSource {
        // Collect useful info and parent formula source.
        let mut useful_info_items = vec![TstpInfoItem::InferenceItemInferenceStatusStatus(
            TstpInferenceStatus::Thm,
        )];

        let mut parent_formula_source: Vec<TstpParentFormula> = vec![];

        if !premises.is_empty() {
            // { ! premises.is_empty() }
            // TODO: performance penalty: doing premises.clone()
            useful_info_items.push(TstpInfoItem::InferenceItemAssumptionsRecord(
                premises.clone(),
            ));

            premises.iter().for_each(|symbol| {
                parent_formula_source
                    .push(TstpAnnotatedFormulaSource::DagSourceName(symbol.to_owned()));
            });
        }

        // Handling special cases
        if rule_name == "subproof" {
            // This rule discharges the premises.
            assert!(premises.is_empty());
            useful_info_items.push(TstpInfoItem::InferenceItemInferenceStatusInferenceInfo(
                TstpInferenceRuleName::RuleName(rule_name.to_owned()),
                TstpInferenceInfoGeneralListQualifier::Discharge,
                // TODO: cloning!
                discharged_assumptions.clone(),
            ));

            discharged_assumptions.iter().for_each(|symbol| {
                parent_formula_source
                    .push(TstpAnnotatedFormulaSource::DagSourceName(symbol.to_owned()));
            });
        }

        // TODO: abstract this into a procedure
        // NOTE: some Alethe rules require "arguments". For the moment,
        // we model that in the form of "rule_name(arg,...)", as the
        // rule name of a DagSourceInference.
        let inference_rule_name = if args.is_empty() {
            TstpInferenceRuleName::RuleName(rule_name.to_owned())
        } else {
            // { ! args.is_empty() }
            TstpInferenceRuleName::RuleWithArgs(rule_name.to_owned(), args)
        };

        TstpAnnotatedFormulaSource::DagSourceInference(
            inference_rule_name,
            TstpUsefulInfo::InfoItems(useful_info_items),
            parent_formula_source,
        )
    }

    /// Translates `BindingList` constructs, as used for binder terms forall, exists,
    /// choice and lambda. The "let" binder uses the same construction but assigns to
    /// it a different semantics. See `translate_let_binding_list` for its translation.
    fn translate_binding_list(binding_list: &BindingList) -> Vec<TstpTypedVariable> {
        let mut ret_binding_list: Vec<TstpTypedVariable> = Vec::new();

        binding_list.iter().for_each(|sorted_var| {
            let (name, sort) = sorted_var;

            let translated_sort: TstpType = match &**sort {
                Term::Sort(actual_sort) => TstpTranslator::translate_sort(actual_sort),

                _ => {
                    // It shouldn't be another kind of Alethe term
                    println!("Expected a Sort(sort) Alethe term, found {:?}.", sort);
                    panic!();
                }
            };

            ret_binding_list.push(TstpTypedVariable::TypedVariable(
                name.clone(),
                Box::new(translated_sort),
            ));
        });

        ret_binding_list
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
                println!("Not known translation for sort {:?}", _sort);
                panic!();
            }

            Term::Op(operator, operands) => {
                self.translate_operator_application(*operator, operands)
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

                TstpFormula::FunctorApp(TstpFunctor::ProblemFunctor((*fun).to_string()), fun_params)
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

            Term::Binder(binder, binding_list, scope) => {
                // New scope to shadow those context variables that
                // are now bound by this binder.
                self.get_mut_translator_data()
                    .alethe_scopes
                    .open_non_context_scope();

                let translated_bindings = TstpTranslator::translate_binding_list(binding_list);

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

                let translated_binder = match binder {
                    Binder::Forall => TstpFormula::UniversalQuant(
                        translated_bindings,
                        Box::new(self.translate_term(scope)),
                    ),

                    Binder::Exists => TstpFormula::ExistentialQuant(
                        translated_bindings,
                        Box::new(self.translate_term(scope)),
                    ),

                    Binder::Choice => {
                        // There should be just one defined variable.
                        assert!(translated_bindings.len() == 1);

                        TstpFormula::Choice(
                            // TODO: cloning!
                            Box::new(translated_bindings[0].clone()),
                            Box::new(self.translate_term(scope)),
                        )
                    }

                    // TODO: complete
                    Binder::Lambda => TstpFormula::Lambda(
                        translated_bindings,
                        Box::new(self.translate_term(scope)),
                    ),
                };

                // Closing the context...
                self.get_mut_translator_data().alethe_scopes.close_scope();

                translated_binder
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
            Operator::Add => TstpOperator::Functor(TstpFunctor::Sum),

            Operator::Sub => TstpOperator::Functor(TstpFunctor::Difference),

            Operator::Mult => TstpOperator::Functor(TstpFunctor::Product),

            Operator::IntDiv => TstpOperator::Functor(TstpFunctor::QuotientE),

            Operator::RealDiv => TstpOperator::Functor(TstpFunctor::Quotient),

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
            // User-defined sort
            // TODO: what about args?
            Sort::Atom(string, ..) => TstpType::UserDefined(string.clone()),

            Sort::Bool => TstpType::Bool,

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

            Sort::Int => TstpType::Int,

            Sort::Real => TstpType::Real,

            _ => {
                println!("Problems translating sort {:?}", sort);
                panic!();
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
        let translated_term = self.translate_term(term);
        let formula_source: TstpAnnotatedFormulaSource;
        let formula_role: TstpFormulaRole;

        if self.get_read_translator_data().is_in_subproof {
            // Subproof's assumption.
            formula_source = TstpAnnotatedFormulaSource::InternalSourceIntroduced(
                TstpInternalSourceIntroducedType::Assumption,
                TstpUsefulInfo::GeneralList(vec![]),
                vec![],
            );

            formula_role = TstpFormulaRole::Assumption;
        } else {
            // { not self.get_read_translator_data().is_in_subproof }
            //  TODO: complete this.
            formula_source = TstpAnnotatedFormulaSource::Empty;
            formula_role = TstpFormulaRole::Axiom;
        }

        self.new_annotated_formula(
            id,
            TstpLanguage::Tff,
            formula_role,
            translated_term,
            formula_source,
            "nil".to_owned(),
        )
    }

    /// Implements the translation of an Alethe `ProofStep`, taking into
    /// account technical differences in the way Alethe rules are
    /// expressed within Tstp.
    /// Updates `self.tstp_proof`.
    fn translate_step(&mut self, node: &ProofNode) {
        let mut alethe_premises: Vec<Symbol> = Vec::new();
        let mut alethe_discharged_assumptions: Vec<Symbol> = Vec::new();
        let mut alethe_translated_args: Vec<TstpFormula> = Vec::new();

        match node {
            ProofNode::Step(StepNode {
                id,
                depth: _,
                clause,
                rule,
                premises,
                args,
                discharge,
                previous_step: _,
            }) => {
                // Add premises actually present in the original step command.
                alethe_premises.extend(
                    premises
                        .iter()
                        .map(|node| String::from(node.deref().id()))
                        .collect::<Vec<Symbol>>(),
                );

                alethe_discharged_assumptions.extend(
                    discharge
                        .iter()
                        .map(|node| String::from(node.deref().id()))
                        .collect::<Vec<Symbol>>(),
                );

                alethe_translated_args.extend(
                    args.iter()
                        .map(|arg| self.translate_term(arg))
                        .collect::<Vec<TstpFormula>>(),
                );

                // NOTE: in ProofStep, clause has type
                // Vec<Rc<Term>>, though it represents an
                // invocation of Alethe's cl operator
                let conclusion: TstpFormula = if clause.is_empty() {
                    TstpFormula::NullaryOperatorApp(TstpNullaryOperator::False)
                } else {
                    // {!clause.is_empty()}
                    self.translate_operator_application(Operator::Or, clause)
                };

                // NOTE: not adding conclusion clause to this list
                let mut tstp_arguments: Vec<TstpFormula> = Vec::new();

                args.iter().for_each(|arg| {
                    tstp_arguments.push(self.translate_term(arg));
                });

                let annotated_formula = self.classify_source_build_step_term(
                    id,
                    rule,
                    conclusion,
                    alethe_premises,
                    alethe_translated_args,
                    alethe_discharged_assumptions,
                );

                self.get_mut_translator_data()
                    .translated_proof
                    .push(annotated_formula);
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
                "", // No step id.
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
                "", // No step id.
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
                "", // No step id.
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
