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
                source: _,
                useful_info: _,
            } = command;
            {
                language_as_str = TstpPrinter::language_to_concrete_syntax(language);
                args = vec![
                    name.clone(),
                    TstpPrinter::role_to_concrete_syntax(role),
                    TstpPrinter::formula_to_concrete_syntax(formula),
                    // TODO: discarding source and useful_info
                    "".to_owned(),
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
        }
    }

    fn formula_to_concrete_syntax(term: &TstpFormula) -> String {
        let mut ret;

        match term {
            TstpFormula::Typing(var, type_inhabited) => {
                ret = TstpPrinter::formula_to_concrete_syntax(var);
                ret += &(": ".to_owned() + &TstpPrinter::type_to_concrete_syntax(type_inhabited));
            }

            TstpFormula::Variable(name) => {
                ret = name.clone();
            }

            _ => {
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

    // fn operator_to_concrete_syntax(op: &EunoiaOperator) -> String {
    //     match op {
    //         EunoiaOperator::Xor => "xor".to_owned(),

    //         EunoiaOperator::Not => "not".to_owned(),

    //         // NOTE: these are the symbols used in theory.eo
    //         EunoiaOperator::Eq => "=".to_owned(),

    //         EunoiaOperator::GreaterThan => ">".to_owned(),

    //         EunoiaOperator::GreaterEq => ">=".to_owned(),

    //         EunoiaOperator::LessThan => "<".to_owned(),

    //         EunoiaOperator::LessEq => "<=".to_owned(),
    //     }
    // }
}
