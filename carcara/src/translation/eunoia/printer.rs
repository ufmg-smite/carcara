//! A pretty printer for Eunoia proofs.
use crate::translation::eunoia::ast::*;
// Re-exporting ProofPrinter, to avoid conflicting import paths in other modules.
pub use crate::translation::ProofPrinter;
use std::io;

// TODO: struct for future actual formatting concerns
/// A formatter for S-expressions.
pub struct SExpFormatter<'a> {
    sink: &'a mut dyn io::Write,
}

impl<'a> SExpFormatter<'a> {
    pub fn new(sink: &'a mut dyn io::Write) -> Self {
        SExpFormatter { sink }
    }

    /// Print lists of arguments, separated just by spaces.
    fn print_sequence<T>(seq: &[T], func: fn(&T) -> String) -> String {
        if seq.is_empty() {
            "".to_owned()
        } else {
            // { !seq.is_empty() }
            let mut result = func(&seq[0]);
            for item in &seq[1..] {
                result += " ";
                result += &func(item);
            }
            result
        }
    }

    /// Prints an s-expression with properly formatted concrete syntax, and
    /// separating it from surrounding s-expressions.
    fn write_s_expr(&mut self, tag: &str, args: &[String]) -> io::Result<()> {
        if args.is_empty() {
            // S-expression is a constant
            write!(self.sink, "{}", tag)?;
        } else {
            // {not args.is_empty()}
            // S-expression has the form (tag arg1 ...)
            write!(self.sink, "(")?;
            write!(self.sink, "{}", tag)?;

            for arg in args {
                write!(self.sink, " {}", arg)?;
            }

            write!(self.sink, ")")?;
        };

        writeln!(self.sink)?;

        Ok(())
    }
}

pub struct EunoiaPrinter<'a> {
    formatted_sink: SExpFormatter<'a>,
}

impl<'a> ProofPrinter for EunoiaPrinter<'a> {
    type Proof = EunoiaProof;

    /// Formatted proof printing.
    fn write_proof(&mut self, proof: &EunoiaProof) -> io::Result<()> {
        let mut tag: String;
        let mut args: Vec<String>;

        // TODO: some generic way of doing this? maybe with macros?
        for command in proof {
            match command {
                EunoiaCommand::Include { path } => {
                    tag = "include".to_owned();
                    args = vec![format!(r#""{}""#, path)];
                }

                EunoiaCommand::Assume { name, term } => {
                    tag = "assume".to_owned();
                    args = vec![name.clone(), EunoiaPrinter::term_to_concrete_syntax(term)];
                }

                EunoiaCommand::AssumePush { name, term } => {
                    tag = "assume-push".to_owned();

                    args = vec![name.clone(), EunoiaPrinter::term_to_concrete_syntax(term)];
                }

                EunoiaCommand::DeclareConst { name, eunoia_type, attrs } => {
                    tag = "declare-const".to_owned();

                    args = Vec::new();

                    args.push(name.clone());
                    args.push(EunoiaPrinter::term_to_concrete_syntax(eunoia_type));

                    attrs.iter().for_each(|attr| {
                        args.push(EunoiaPrinter::cons_attr_to_concrete_syntax(attr));
                    });
                }

                EunoiaCommand::Define { name, typed_params, term, attrs } => {
                    tag = "define".to_owned();

                    args = Vec::new();

                    args.push(name.clone());

                    args.append(&mut EunoiaPrinter::eunoia_list_to_concrete_syntax(
                        typed_params,
                        &EunoiaPrinter::typed_param_to_concrete_syntax,
                    ));

                    args.push(EunoiaPrinter::term_to_concrete_syntax(term));

                    attrs.iter().for_each(|attr| {
                        args.push(EunoiaPrinter::define_attr_to_concrete_syntax(attr));
                    });
                }

                EunoiaCommand::Program {
                    name,
                    typed_params,
                    params,
                    ret,
                    body,
                } => {
                    tag = "program".to_owned();

                    args = Vec::new();
                    // Program name.
                    args.push(name.clone());
                    // Typed params.
                    args.append(&mut EunoiaPrinter::eunoia_list_to_concrete_syntax(
                        typed_params,
                        &EunoiaPrinter::typed_param_to_concrete_syntax,
                    ));
                    // Formal parameters.
                    args.append(&mut EunoiaPrinter::eunoia_list_to_concrete_syntax(
                        params,
                        &EunoiaPrinter::type_to_concrete_syntax,
                    ));
                    // Return type.
                    args.push(EunoiaPrinter::type_to_concrete_syntax(ret));
                    // Program's body.
                    args.append(&mut EunoiaPrinter::eunoia_list_to_concrete_syntax(
                        body,
                        &Box::new(|tuple: &(EunoiaTerm, EunoiaTerm)| {
                            format!(
                                "({} {})",
                                EunoiaPrinter::term_to_concrete_syntax(&tuple.0),
                                EunoiaPrinter::term_to_concrete_syntax(&tuple.1)
                            )
                        }),
                    ));
                }

                EunoiaCommand::SetLogic { name } => {
                    tag = "set-logic".to_owned();

                    args = vec![name.clone()];
                }

                EunoiaCommand::Step {
                    id,
                    conclusion_clause,
                    rule,
                    premises,
                    arguments,
                } => {
                    tag = "step".to_owned();

                    args = Vec::new();

                    args.push(id.clone());

                    if let Some(term) = conclusion_clause {
                        args.push(EunoiaPrinter::term_to_concrete_syntax(term));
                    };

                    args.push(":rule ".to_owned() + &rule.clone());

                    let EunoiaList { list } = premises;

                    if !list.is_empty() {
                        args.push(":premises".to_owned());
                        args.append(&mut EunoiaPrinter::eunoia_list_to_concrete_syntax(
                            premises,
                            &EunoiaPrinter::term_to_concrete_syntax,
                        ));
                    }

                    let EunoiaList { list } = arguments;
                    if !list.is_empty() {
                        args.push(":args".to_owned());
                        args.append(&mut EunoiaPrinter::eunoia_list_to_concrete_syntax(
                            arguments,
                            &EunoiaPrinter::term_to_concrete_syntax,
                        ));
                    }
                }

                EunoiaCommand::StepPop {
                    id,
                    conclusion_clause,
                    rule,
                    premises,
                    arguments,
                } => {
                    tag = "step-pop".to_owned();

                    args = Vec::new();

                    args.push(id.clone());

                    if let Some(term) = conclusion_clause {
                        args.push(EunoiaPrinter::term_to_concrete_syntax(term));
                    };

                    // TODO: rule names are not equal: let -> let_elim
                    args.push(":rule ".to_owned() + &rule.clone());

                    let EunoiaList { list } = premises;
                    if !list.is_empty() {
                        args.push(":premises".to_owned());
                        args.append(&mut EunoiaPrinter::eunoia_list_to_concrete_syntax(
                            premises,
                            &EunoiaPrinter::term_to_concrete_syntax,
                        ));
                    };

                    let EunoiaList { list } = arguments;

                    if !list.is_empty() {
                        args.push(":args".to_owned());
                        args.append(&mut EunoiaPrinter::eunoia_list_to_concrete_syntax(
                            arguments,
                            &EunoiaPrinter::term_to_concrete_syntax,
                        ));
                    }
                }

                EunoiaCommand::DeclareSort { .. } => {
                    tag = "declare-sort".to_owned();

                    args = vec![];
                }
            };

            self.formatted_sink.write_s_expr(&tag, &args)?;
        }

        Ok(())
    }
}

impl<'a> EunoiaPrinter<'a> {
    pub fn new(dest: SExpFormatter<'a>) -> Self {
        Self { formatted_sink: dest }
    }

    fn cons_attr_to_concrete_syntax(attr: &EunoiaConsAttr) -> String {
        match attr {
            EunoiaConsAttr::RightAssoc => ":right-assoc".to_owned(),

            _ => ":right-assoc".to_owned(),
        }
    }

    fn term_to_concrete_syntax(term: &EunoiaTerm) -> String {
        let mut ret;

        match term {
            EunoiaTerm::Numeral(n) => {
                ret = n.to_string();
            }

            EunoiaTerm::Decimal(r) => {
                ret = String::from("");

                if r.is_negative() {
                    ret += "(- ";
                }
                if r.is_integer() {
                    ret += &(r.clone().abs().to_string() + ".0");
                } else {
                    ret += &format!("/ {}.0 {}.0)", r.numer().clone().abs(), &r.denom());
                }
                if r.is_negative() {
                    ret += ")";
                }
            }

            EunoiaTerm::Rational(n, d) => {
                ret = format!("{}/{}", n, d);
            }

            EunoiaTerm::Id(name) => {
                ret = name.clone();
            }

            EunoiaTerm::Type(some_type) => {
                ret = EunoiaPrinter::type_to_concrete_syntax(some_type);
            }

            EunoiaTerm::True => {
                ret = "true".to_owned();
            }

            EunoiaTerm::False => {
                ret = "false".to_owned();
            }

            EunoiaTerm::App(symbol, params) => {
                if params.is_empty() {
                    ret = format!("({})", symbol.clone());
                } else {
                    // { not params.is_empty() }
                    ret = format!(
                        "({} {})",
                        symbol.clone(),
                        SExpFormatter::print_sequence(
                            params,
                            EunoiaPrinter::term_to_concrete_syntax
                        )
                    );
                }
            }

            EunoiaTerm::HOApp(function, params) => {
                ret = format!(
                    "( _ {} {})",
                    EunoiaPrinter::term_to_concrete_syntax(function),
                    SExpFormatter::print_sequence(params, EunoiaPrinter::term_to_concrete_syntax)
                );
            }

            EunoiaTerm::Op(operator, params) => {
                ret = format!(
                    "({} {})",
                    EunoiaPrinter::operator_to_concrete_syntax(operator),
                    SExpFormatter::print_sequence(params, EunoiaPrinter::term_to_concrete_syntax)
                );
            }

            EunoiaTerm::String(string) => {
                ret = format!("\"{}\"", string.clone());
            }

            EunoiaTerm::List(terms) => {
                ret = format!(
                    "( {} )",
                    SExpFormatter::print_sequence(terms, EunoiaPrinter::term_to_concrete_syntax)
                );
            }

            EunoiaTerm::Var(name, sort) => {
                ret = format!(
                    "( {} {} )",
                    name.clone(),
                    EunoiaPrinter::term_to_concrete_syntax(sort)
                );
            }
        }

        ret
    }

    fn type_to_concrete_syntax(some_type: &EunoiaType) -> String {
        match some_type {
            EunoiaType::Bool => "Bool".to_owned(),

            EunoiaType::Type => "Type".to_owned(),

            EunoiaType::Real => "Real".to_owned(),

            EunoiaType::Name(name) => name.clone(),

            EunoiaType::Fun(kind_params, dom, codom) => {
                format!(
                    "(-> {} {} {})",
                    SExpFormatter::print_sequence(
                        kind_params,
                        EunoiaPrinter::kind_param_to_concrete_syntax
                    ),
                    SExpFormatter::print_sequence(dom, EunoiaPrinter::type_to_concrete_syntax),
                    EunoiaPrinter::type_to_concrete_syntax(codom)
                )
            }
        }
    }

    fn typed_param_to_concrete_syntax(param: &EunoiaTypedParam) -> String {
        let EunoiaTypedParam { name, eunoia_type, attrs } = param;

        if attrs.is_empty() {
            format!(
                "({} {})",
                name.clone(),
                EunoiaPrinter::type_to_concrete_syntax(eunoia_type)
            )
        } else {
            // { not attrs.is_empty() }
            format!(
                "({} {} {})",
                name.clone(),
                EunoiaPrinter::type_to_concrete_syntax(eunoia_type),
                SExpFormatter::print_sequence(attrs, EunoiaPrinter::cons_attr_to_concrete_syntax)
            )
        }
    }

    fn define_attr_to_concrete_syntax(attr: &EunoiaDefineAttr) -> String {
        match attr {
            EunoiaDefineAttr::Type(some_type) => {
                ":type ".to_owned() + &EunoiaPrinter::type_to_concrete_syntax(some_type)
            }
        }
    }

    fn type_attr_to_concrete_syntax(attr: &EunoiaTypeAttr) -> String {
        match attr {
            EunoiaTypeAttr::Var(name) => ":var ".to_owned() + &name.clone(),

            EunoiaTypeAttr::Implicit => ":implicit".to_owned(),

            EunoiaTypeAttr::Requires(lhs, rhs) => {
                format!(
                    ":requires ({} {})",
                    EunoiaPrinter::term_to_concrete_syntax(lhs),
                    EunoiaPrinter::term_to_concrete_syntax(rhs)
                )
            }
        }
    }

    fn kind_param_to_concrete_syntax(attr: &EunoiaKindParam) -> String {
        match attr {
            EunoiaKindParam(some_type, attrs) => {
                format!(
                    "(! {} {})",
                    EunoiaPrinter::type_to_concrete_syntax(some_type),
                    SExpFormatter::print_sequence(
                        attrs,
                        EunoiaPrinter::type_attr_to_concrete_syntax
                    )
                )
            }
        }
    }

    fn operator_to_concrete_syntax(op: &EunoiaOperator) -> String {
        match op {
            EunoiaOperator::Xor => "xor".to_owned(),

            EunoiaOperator::Not => "not".to_owned(),

            // NOTE: these are the symbols used in theory.eo
            EunoiaOperator::Eq => "=".to_owned(),

            EunoiaOperator::GreaterThan => ">".to_owned(),

            EunoiaOperator::GreaterEq => ">=".to_owned(),

            EunoiaOperator::LessThan => "<".to_owned(),

            EunoiaOperator::LessEq => "<=".to_owned(),
        }
    }

    /// Pseudo-map over a `EunoiaList`<T>
    fn eunoia_list_to_concrete_syntax<T>(
        eunoia_list: &EunoiaList<T>,
        to_concrete: &dyn Fn(&T) -> String,
    ) -> Vec<String> {
        let mut ret = Vec::new();

        ret.push("(".to_owned());

        let EunoiaList { list } = eunoia_list;
        list.iter().for_each(|elem| ret.push(to_concrete(elem)));

        ret.push(")".to_owned());

        ret
    }
}
