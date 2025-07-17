//! A pretty printer for Tstp proofs.
use crate::translation::tstp::tstp_ast::*;
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

pub trait PrintProof {
    fn write_proof(&mut self, proof: &TstpProof) -> io::Result<()>;
}

impl<'a> PrintProof for TstpPrinter<'a> {
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
    ///      start with a lowercase letter or are 'single quoted', and variables start with an
    ///      uppercase letter."
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

            TstpFormula::OperatorApp(op, operands) => {
                if TstpPrinter::is_nullary_operator(op) {
                    assert!(operands.is_empty());

                    ret = TstpPrinter::operator_to_concrete_syntax(op);
                } else {
                    // { ! TstpPrinter::is_nullary_operator(op) }
                    if TstpPrinter::is_unary_operator(op) {
                        assert!(operands.len() == 1);

                        ret = TstpPrinter::operator_to_concrete_syntax(op)
                            + " "
                            + &TstpPrinter::formula_to_concrete_syntax(&operands[0]);
                    } else {
                        // { ! TstpPrinter::is_nullary_operator(op) /\
                        //   ! TstpPrinter::is_unary_operator(op)}
                        assert!(operands.len() == 2);

                        ret = "( ".to_owned()
                            + &TstpPrinter::formula_to_concrete_syntax(&operands[0])
                            + " "
                            + &TstpPrinter::operator_to_concrete_syntax(op)
                            + " "
                            + &TstpPrinter::formula_to_concrete_syntax(&operands[1])
                            + " )";
                    }
                }
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
            // Logic
            TstpOperator::Not => "~".to_owned(),

            TstpOperator::And => "&".to_owned(),

            TstpOperator::Or => "|".to_owned(),

            TstpOperator::True => "$true".to_owned(),

            TstpOperator::False => "$false".to_owned(),

            // Relations
            TstpOperator::Equality => "=".to_owned(),

            TstpOperator::Inequality => "!=".to_owned(),

            TstpOperator::Uminus => "-".to_owned(),

            _ => panic!(),
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
                ret = TstpPrinter::source_introduced_type_to_concrete_syntax(introduced_type);

                ret += "(";

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

    /// Query functions to help with the lack of expressiveness of the grammar
    /// being used to represent TPTP/TSTP.
    fn is_unary_operator(op: &TstpOperator) -> bool {
        match op {
            // Unary operators
            TstpOperator::Not => true,

            TstpOperator::Uminus => true,

            _ => false,
        }
    }

    fn is_nullary_operator(op: &TstpOperator) -> bool {
        match op {
            // Unary operators
            TstpOperator::True => true,

            TstpOperator::False => true,

            _ => false,
        }
    }
}
