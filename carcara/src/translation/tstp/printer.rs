//! A pretty printer for Tstp proofs.
use crate::translation::tstp::tstp_ast::*;
// Re-exporting PrintProof, to avoid conflicting import paths in other modules.
pub use crate::translation::PrintProof;
use std::io;

// TODO: struct for future actual formatting concerns
// TODO: change this to a proper formatter for TSTP
/// A formatter for annotated formulas.
pub struct AnnotatedFormulaFormatter<'a> {
    sink: &'a mut dyn io::Write,
}

impl<'a> AnnotatedFormulaFormatter<'a> {
    pub fn new(sink: &'a mut dyn io::Write) -> Self {
        AnnotatedFormulaFormatter { sink }
    }

    // Prints an annotated formula with properly formatted concrete syntax, and
    // separating it from surrounding formulas.
    fn write_annotated_formula(&mut self, language: &str, args: &[String]) -> io::Result<()> {
        if args.is_empty() {
            panic!();
        } else {
            // {not args.is_empty()}
            // Formula of the form language(arg1 ...)
            write!(self.sink, "{}", language)?;
            write!(self.sink, "(")?;
            // TODO: some more idiomatic way of dealing with this?
            let mut first_element = true;
            args.iter().for_each(|arg| {
                if first_element {
                    let _ = write!(self.sink, "{}", arg);
                    first_element = false;
                } else {
                    // {not first_element}
                    // There might be optional arguments, we filter them.
                    if !arg.is_empty() {
                        let _ = write!(self.sink, ", {}", arg);
                    }
                }
            });

            write!(self.sink, ").")?;
        };

        writeln!(self.sink)?;

        Ok(())
    }
}

pub struct TstpPrinter<'a> {
    // Where to write.
    // TODO: use something different that an AnnotatedFormulaFormatter
    formatted_sink: AnnotatedFormulaFormatter<'a>,
}

impl<'a> PrintProof for TstpPrinter<'a> {
    type Proof = TstpProof;

    /// Formatted proof printing.
    fn write_proof(&mut self, proof: &TstpProof) -> io::Result<()> {
        let mut language_as_str: String;
        let mut args: Vec<String>;

        // TODO: some generic way of doing this? maybe with macros?
        for command in proof {
            let TstpAnnotatedFormula {
                language,
                name,
                role,
                formula,
                source,
                useful_info: _,
            } = command;
            {
                language_as_str = TstpPrinter::language_to_concrete_syntax(language);
                args = vec![
                    TstpPrinter::formula_name_to_concrete_syntax(name),
                    TstpPrinter::role_to_concrete_syntax(role),
                    TstpPrinter::formula_to_concrete_syntax(formula),
                    TstpPrinter::source_to_concrete_syntax(source),
                    // TODO: discarding useful_info
                    "".to_owned(),
                ];
                self.formatted_sink
                    .write_annotated_formula(&language_as_str, &args)?;
            }
        }

        Ok(())
    }
}

impl<'a> TstpPrinter<'a> {
    pub fn new(dest: AnnotatedFormulaFormatter<'a>) -> Self {
        Self { formatted_sink: dest }
    }

    fn language_to_concrete_syntax(language: &TstpLanguage) -> String {
        match language {
            TstpLanguage::Fof => String::from("fof"),

            TstpLanguage::Tff => String::from("tff"),
        }
    }

    fn role_to_concrete_syntax(role: &TstpFormulaRole) -> String {
        // TODO: reuse role.to_string()
        match role {
            TstpFormulaRole::Assumption => "assumption".to_owned(),

            TstpFormulaRole::Axiom => "axiom".to_owned(),

            TstpFormulaRole::Lemma => "lemma".to_owned(),

            TstpFormulaRole::Conjecture => "conjecture".to_owned(),

            TstpFormulaRole::Hypothesis => "hypothesis".to_owned(),

            TstpFormulaRole::Logic => "logic".to_owned(),

            TstpFormulaRole::Type => "type".to_owned(),

            TstpFormulaRole::Plain => "plain".to_owned(),
        }
    }

    /// Concrete syntax rules (from TPTP's docs):
    /// - "In a formula, terms and atoms follow Prolog conventions - functions and predicates
    ///   start with a lowercase letter or are 'single quoted', and variables start with an
    ///   uppercase letter."
    fn formula_to_concrete_syntax(formula: &TstpFormula) -> String {
        let mut ret: String;

        match formula {
            TstpFormula::BinaryOperatorApp(binary_op, left_operand, right_operand) => {
                ret = "( ".to_owned()
                    + &TstpPrinter::formula_to_concrete_syntax(left_operand)
                    + " "
                    + &TstpPrinter::operator_to_concrete_syntax(&TstpOperator::BinaryOperator(
                        binary_op.clone(),
                    ))
                    + " "
                    + &TstpPrinter::formula_to_concrete_syntax(right_operand)
                    + " )";
            }

            TstpFormula::FunctorApp(functor, arguments) => {
                ret = functor.clone() + "(";

                let mut first_element = true;

                arguments.iter().for_each(|argument| {
                    if first_element {
                        ret += &TstpPrinter::formula_to_concrete_syntax(argument);
                        first_element = false;
                    } else {
                        // { ! first_element }
                        ret +=
                            &(", ".to_owned() + &TstpPrinter::formula_to_concrete_syntax(argument));
                    }
                });

                ret += ")";
            }

            TstpFormula::Integer(integer) => {
                ret = integer.to_string();
            }

            TstpFormula::NullaryOperatorApp(nullary_op) => {
                ret = TstpPrinter::operator_to_concrete_syntax(&TstpOperator::NullaryOperator(
                    nullary_op.clone(),
                ));
            }

            TstpFormula::Typing(var, type_inhabited) => {
                ret = TstpPrinter::formula_to_concrete_syntax(var);
                ret += &(": ".to_owned() + &TstpPrinter::type_to_concrete_syntax(type_inhabited));
            }

            TstpFormula::UnaryOperatorApp(unary_op, operand) => {
                ret = TstpPrinter::operator_to_concrete_syntax(&TstpOperator::UnaryOperator(
                    unary_op.clone(),
                )) + " "
                    + &TstpPrinter::formula_to_concrete_syntax(operand);
            }

            TstpFormula::UniversalQuant(variables, scope) => {
                ret = "(! [".to_owned();
                // TODO: abstract this pattern into a procedure
                let mut first_element = true;

                variables.iter().for_each(|elem| {
                    if first_element {
                        ret += &TstpPrinter::typed_variable_to_concrete_syntax(elem);
                        first_element = false;
                    } else {
                        // { ! first_element }
                        ret += &(", ".to_owned()
                            + &TstpPrinter::typed_variable_to_concrete_syntax(elem));
                    }
                });

                ret += "] : ";
                ret += &TstpPrinter::formula_to_concrete_syntax(scope);
                ret += ")";
            }

            TstpFormula::Variable(name) => {
                ret = name.clone();
            }

            _ => {
                println!("No defined translation for formula {:?}", formula);
                panic!();
            }
        }

        ret
    }

    fn type_to_concrete_syntax(type_term: &TstpType) -> String {
        match type_term {
            TstpType::Bool => "$o".to_owned(),

            TstpType::Fun(domain, codomain) => {
                let mut ret = "( ".to_owned();

                let mut first_element = true;

                domain.iter().for_each(|elem| {
                    if first_element {
                        ret += &TstpPrinter::type_to_concrete_syntax(elem);
                        first_element = false;
                    } else {
                        // { ! first_element }
                        ret += &(" * ".to_owned() + &TstpPrinter::type_to_concrete_syntax(elem));
                    }
                });

                // TODO: hard-coding here the arrow symbol
                ret += " ) > ";

                ret += &TstpPrinter::type_to_concrete_syntax(codomain);

                ret
            }

            TstpType::Int => "$int".to_owned(),

            TstpType::Real => "$real".to_owned(),

            TstpType::Universe => "$tType".to_owned(),

            TstpType::UserDefined(name) => "\'".to_owned() + &name.clone() + "\'",

            _ => {
                println!("Problems translating type term {:?}", type_term);
                panic!();
            }
        }
    }

    fn typed_variable_to_concrete_syntax(typed_variable: &TstpTypedVariable) -> String {
        let mut ret: String;

        match typed_variable {
            TstpTypedVariable::TypedVariable(name, var_type) => {
                ret = name.clone();
                ret += &(":".to_owned() + &TstpPrinter::type_to_concrete_syntax(var_type));
            }
        }

        ret
    }

    fn operator_to_concrete_syntax(op: &TstpOperator) -> String {
        match op {
            // Logic nullary operators
            TstpOperator::NullaryOperator(TstpNullaryOperator::True) => "$true".to_owned(),

            TstpOperator::NullaryOperator(TstpNullaryOperator::False) => "$false".to_owned(),

            // Logic unary operators
            TstpOperator::UnaryOperator(TstpUnaryOperator::Not) => "~".to_owned(),

            // Logic binary operators
            TstpOperator::BinaryOperator(TstpBinaryOperator::And) => "&".to_owned(),

            TstpOperator::BinaryOperator(TstpBinaryOperator::Or) => "|".to_owned(),

            TstpOperator::BinaryOperator(TstpBinaryOperator::Implies) => "=>".to_owned(),

            // Binary relations
            TstpOperator::BinaryOperator(TstpBinaryOperator::Equality) => "=".to_owned(),

            TstpOperator::BinaryOperator(TstpBinaryOperator::Inequality) => "!=".to_owned(),

            // Arithmetic unary ops.
            TstpOperator::UnaryOperator(TstpUnaryOperator::Uminus) => "-".to_owned(),

            // Arithmetic binary ops.
            TstpOperator::BinaryOperator(TstpBinaryOperator::Sum) => "$sum".to_owned(),

            _ => {
                println!("Problems translating operator {:?}", op);
                panic!()
            }
        }
    }

    /// Prints a formula name. It follows the concrete syntax rules of name atoms, of TPTP.
    fn formula_name_to_concrete_syntax(name: &Symbol) -> String {
        // <name>                 ::= <atomic_word> | <integer>
        // <atomic_word>   ::= <lower_word> | <single_quoted>
        // <lower_word>     ::- <lower_alpha><alpha_numeric>*
        // <single_quoted> ::- <single_quote><sq_char><sq_char>*<single_quote>
        // For the moment, just converting everything to lowercase.

        str::to_lowercase(name)
    }

    fn source_to_concrete_syntax(source: &TstpAnnotatedFormulaSource) -> String {
        let mut ret: String;

        match source {
            TstpAnnotatedFormulaSource::Empty => {
                ret = "".to_owned();
            }

            TstpAnnotatedFormulaSource::InternalSourceIntroduced(
                introduced_type,
                useful_info,
                parents,
            ) => {
                // TODO: mixing different concerns: balanced terms should be dealt
                // with elsewhere.
                ret = "introduced(".to_owned();

                ret += &TstpPrinter::internal_source_introduced_type_to_concrete_syntax(
                    introduced_type,
                );

                ret += ", ";

                ret += &TstpPrinter::useful_info_to_concrete_syntax(useful_info);

                ret += ", [";

                // TODO: a more idiomatic way of solving this
                let mut first_iteration = true;

                parents.iter().for_each(|parent| {
                    if first_iteration {
                        ret += &TstpPrinter::source_to_concrete_syntax(parent);
                        first_iteration = false;
                    } else {
                        // { ! first_iteration }
                        ret += ", ";
                        ret += &TstpPrinter::source_to_concrete_syntax(parent);
                    }
                });

                ret += "])";
            }

            TstpAnnotatedFormulaSource::DagSourceInference(rule_name, useful_info, parents) => {
                // TODO: mixing different concerns: balanced terms should be dealt
                // with elsewhere.
                ret = "inference(".to_owned();

                ret += &TstpPrinter::inference_rule_name_to_concrete_syntax(rule_name);

                ret += ", ";

                ret += &TstpPrinter::useful_info_to_concrete_syntax(useful_info);
                ret += ", [";

                // ret += ", [";

                // // TODO: a more idiomatic way of solving this
                // let mut first_iteration = true;

                // general_data.iter().for_each(|data| {
                //     if first_iteration {
                //         ret += &TstpPrinter::general_data_to_concrete_syntax(data);
                //         first_iteration = false;
                //     } else {
                //         // { ! first_iteration }
                //         ret += ", ";
                //         ret += &TstpPrinter::general_data_to_concrete_syntax(data);
                //     }
                // });

                // ret += "], [";

                // TODO: a more idiomatic way of solving this
                let mut first_iteration = true;

                parents.iter().for_each(|parent| {
                    if first_iteration {
                        ret += &TstpPrinter::source_to_concrete_syntax(parent);
                        first_iteration = false;
                    } else {
                        // { ! first_iteration }
                        ret += ", ";
                        ret += &TstpPrinter::source_to_concrete_syntax(parent);
                    }
                });

                ret += "])";
            }

            TstpAnnotatedFormulaSource::DagSourceName(symbol) => {
                ret = symbol.to_owned();
            }
        }

        ret
    }

    fn internal_source_introduced_type_to_concrete_syntax(
        intro_type: &TstpInternalSourceIntroducedType,
    ) -> String {
        match intro_type {
            TstpInternalSourceIntroducedType::Name(symbol) => symbol.clone(),

            TstpInternalSourceIntroducedType::Definition => "definition".to_owned(),

            TstpInternalSourceIntroducedType::Tautology => "tautology".to_owned(),

            TstpInternalSourceIntroducedType::Assumption => "assumption".to_owned(),
        }
    }

    fn useful_info_to_concrete_syntax(useful_info: &TstpUsefulInfo) -> String {
        let mut ret: String;

        match useful_info {
            // TstpUsefulInfo::GeneralDataNewSymbols(symbols) => {
            //     ret = "new_symbols(".to_owned();

            //     let mut first_iteration = true;

            //     symbols.iter().for_each(|symbol| {
            //         if first_iteration {
            //             ret += symbol;
            //             first_iteration = false;
            //         } else {
            //             // { ! first_iteration }
            //             ret += &(", ".to_owned() + &symbol.clone());
            //         }
            //     });

            //     ret += ")";
            // }
            TstpUsefulInfo::GeneralList(general_datas) => {
                ret = "[".to_owned();

                let mut first_iteration = true;

                general_datas.iter().for_each(|general_data| {
                    if first_iteration {
                        ret += &TstpPrinter::general_data_to_concrete_syntax(general_data);
                        first_iteration = false;
                    } else {
                        // { ! first_iteration }
                        ret += &(", ".to_owned()
                            + &TstpPrinter::general_data_to_concrete_syntax(general_data));
                    }
                });

                ret += "]";
            }

            TstpUsefulInfo::InfoItems(info_items) => {
                ret = "[".to_owned();

                let mut first_iteration = true;

                info_items.iter().for_each(|info_item| {
                    if first_iteration {
                        ret += &TstpPrinter::info_item_to_concrete_syntax(info_item);
                        first_iteration = false;
                    } else {
                        // { ! first_iteration }
                        ret += &(", ".to_owned()
                            + &TstpPrinter::info_item_to_concrete_syntax(info_item));
                    }
                });

                ret += "]";
            }
        }

        ret
    }

    fn general_data_to_concrete_syntax(general_data: &TstpGeneralData) -> String {
        let mut ret: String;

        match general_data {
            TstpGeneralData::AtomicWord(symbol) => {
                ret = symbol.to_owned();
            }

            TstpGeneralData::GeneralFunction(atomic_word, params) => {
                ret = atomic_word.clone();

                ret += "(";

                // TODO: repeating code, and a more idiomatic way
                // to deal with this
                let mut first_iteration = true;

                params.iter().for_each(|param| {
                    if first_iteration {
                        ret += &TstpPrinter::formula_to_concrete_syntax(param);
                        first_iteration = false;
                    } else {
                        // { ! first_iteration }
                        ret += &(", ".to_owned() + &TstpPrinter::formula_to_concrete_syntax(param));
                    }
                });

                ret += ")";
            }
        }

        ret
    }

    fn info_item_to_concrete_syntax(info_item: &TstpInfoItem) -> String {
        let mut ret: String;

        match info_item {
            TstpInfoItem::InferenceItemInferenceStatusStatus(status) => {
                ret = "status(".to_owned();

                ret += &TstpPrinter::inference_status_to_concrete_syntax(status);

                ret += ")";
            }

            TstpInfoItem::InferenceItemInferenceStatusInferenceInfo(
                rule_name,
                general_list_qualifier,
                general_list,
            ) => {
                ret = TstpPrinter::inference_rule_name_to_concrete_syntax(rule_name);

                ret += "(";

                ret += &TstpPrinter::inference_info_general_list_qualifier_to_concrete_syntax(
                    general_list_qualifier,
                );

                ret += ", [";
                // TODO: abstract this into a single procedure
                // TODO: more idiomatic way to deal with this?
                let mut first_element = true;

                general_list.iter().for_each(|assumption| {
                    if first_element {
                        ret += assumption;
                        first_element = false;
                    } else {
                        // { ! first_element }
                        ret += &(", ".to_owned() + assumption);
                    }
                });

                ret += "])";
            }

            TstpInfoItem::InferenceItemAssumptionsRecord(assumptions) => {
                assert!(!assumptions.is_empty());

                ret = "assumptions([".to_owned();

                // TODO: more idiomatic way to deal with this?
                // TODO: abstract this into a single procedure
                let mut first_element = true;

                assumptions.iter().for_each(|assumption| {
                    if first_element {
                        ret += assumption;
                        first_element = false;
                    } else {
                        // { ! first_element }
                        ret += &(", ".to_owned() + assumption);
                    }
                });

                ret += "])";
            }
        }

        ret
    }

    fn inference_status_to_concrete_syntax(status: &TstpInferenceStatus) -> String {
        match status {
            TstpInferenceStatus::Thm => "thm".to_owned(),
        }
    }

    fn inference_info_general_list_qualifier_to_concrete_syntax(
        list_qualifier: &TstpInferenceInfoGeneralListQualifier,
    ) -> String {
        match list_qualifier {
            TstpInferenceInfoGeneralListQualifier::Discharge => "discharge".to_owned(),
        }
    }

    fn inference_rule_name_to_concrete_syntax(rule_name: &TstpInferenceRuleName) -> String {
        let mut ret: String;

        match rule_name {
            TstpInferenceRuleName::RuleName(name) => {
                ret = name.to_owned();
            }

            TstpInferenceRuleName::RuleWithArgs(name, args) => {
                ret = name.clone();

                ret += "(";

                // TODO: repeating code, and a more idiomatic way
                // to deal with this
                let mut first_iteration = true;

                args.iter().for_each(|arg| {
                    if first_iteration {
                        ret += &TstpPrinter::formula_to_concrete_syntax(arg);
                        first_iteration = false;
                    } else {
                        // { ! first_iteration }
                        ret += &(", ".to_owned() + &TstpPrinter::formula_to_concrete_syntax(arg));
                    }
                });

                ret += ")";
            }
        }

        ret
    }
}
