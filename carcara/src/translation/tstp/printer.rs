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
            TstpFormula::Typing(var, type_inhabited) => {
                ret = TstpPrinter::formula_to_concrete_syntax(var);
                ret += &(": ".to_owned() + &TstpPrinter::type_to_concrete_syntax(type_inhabited));
            }

            TstpFormula::Variable(name) => {
                ret = name.clone();
            }

            TstpFormula::NullaryOperatorApp(nullary_op) => {
                ret = TstpPrinter::operator_to_concrete_syntax(&TstpOperator::NullaryOperator(
                    nullary_op.clone(),
                ));
            }

            TstpFormula::UnaryOperatorApp(unary_op, operand) => {
                ret = TstpPrinter::operator_to_concrete_syntax(&TstpOperator::UnaryOperator(
                    unary_op.clone(),
                )) + " "
                    + &TstpPrinter::formula_to_concrete_syntax(operand);
            }

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

            _ => {
                println!("No defined translation for formula {:?}", formula);
                panic!();
            }
        }

        ret
    }

    fn type_to_concrete_syntax(type_term: &TstpType) -> String {
        match type_term {
            TstpType::UserDefined(name) => "\'".to_owned() + &name.clone() + "\'",

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

            TstpType::Universe => "$tType".to_owned(),

            _ => {
                panic!();
            }
        }
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

            TstpAnnotatedFormulaSource::Introduced(introduced_type, useful_info, parents) => {
                // TODO: mixing different concerns: balanced terms should be dealt
                // with elsewhere.
                ret = "introduced(".to_owned();

                ret += &TstpPrinter::source_introduced_type_to_concrete_syntax(introduced_type);

                ret += ", ";

                ret += &TstpPrinter::source_introduced_useful_info_to_concrete_syntax(useful_info);

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

            TstpAnnotatedFormulaSource::Inference(rule_name, general_data, parents) => {
                // TODO: mixing different concerns: balanced terms should be dealt
                // with elsewhere.
                ret = "inference(".to_owned();

                ret += rule_name;

                ret += ", [";

                // TODO: a more idiomatic way of solving this
                let mut first_iteration = true;

                general_data.iter().for_each(|data| {
                    if first_iteration {
                        ret += &TstpPrinter::general_data_to_concrete_syntax(data);
                        first_iteration = false;
                    } else {
                        // { ! first_iteration }
                        ret += ", ";
                        ret += &TstpPrinter::general_data_to_concrete_syntax(data);
                    }
                });

                ret += "], [";

                // TODO: a more idiomatic way of solving this
                first_iteration = true;

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
        }

        ret
    }

    fn source_introduced_type_to_concrete_syntax(intro_type: &TstpSourceIntroducedType) -> String {
        match intro_type {
            TstpSourceIntroducedType::Name(symbol) => symbol.clone(),

            TstpSourceIntroducedType::Definition => "definition".to_owned(),

            TstpSourceIntroducedType::Tautology => "tautology".to_owned(),

            TstpSourceIntroducedType::Assumption => "assumption".to_owned(),
        }
    }

    fn source_introduced_useful_info_to_concrete_syntax(
        useful_info: &TstpSourceIntroducedUsefulInfo,
    ) -> String {
        let mut ret: String;

        match useful_info {
            TstpSourceIntroducedUsefulInfo::NewSymbols(symbols) => {
                ret = "new_symbols(".to_owned();

                let mut first_iteration = true;

                symbols.iter().for_each(|symbol| {
                    if first_iteration {
                        ret += symbol;
                        first_iteration = false;
                    } else {
                        // { ! first_iteration }
                        ret += &(", ".to_owned() + &symbol.clone());
                    }
                });

                ret += ")";
            }

            TstpSourceIntroducedUsefulInfo::GeneralList(symbols) => {
                ret = "[".to_owned();

                let mut first_iteration = true;

                symbols.iter().for_each(|symbol| {
                    if first_iteration {
                        ret += symbol;
                        first_iteration = false;
                    } else {
                        // { ! first_iteration }
                        ret += &(", ".to_owned() + &symbol.clone());
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
            TstpGeneralData::Status(status) => {
                ret = "status(".to_owned();

                ret += &TstpPrinter::general_data_status_to_concrete_syntax(status);

                ret += ")";
            }
        }

        ret
    }

    fn general_data_status_to_concrete_syntax(status: &TstpGeneralDataStatus) -> String {
        match status {
            TstpGeneralDataStatus::Thm => "thm".to_owned(),
        }
    }
}
