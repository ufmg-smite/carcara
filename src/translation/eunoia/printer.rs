//! A pretty printer for Eunoia proofs.

use crate::translation::eunoia::ast::*;
use std::fmt;

pub struct DisplayEunoiaProof<'a>(pub &'a EunoiaProof);

impl<'a> fmt::Display for DisplayEunoiaProof<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for command in self.0 {
            match command {
                EunoiaCommand::Include { path } => writeln!(f, "(include \"{path}\")"),
                EunoiaCommand::Assume { name, term } => writeln!(f, "(assume {name} {term})"),
                EunoiaCommand::AssumePush { name, term } => {
                    writeln!(f, "(assume-push {name} {term})")
                }
                EunoiaCommand::Define { name, typed_params, term, attrs } => {
                    write!(
                        f,
                        "(define {name} ({}) {term}",
                        display_sequence(&typed_params.list),
                    )?;
                    for a in attrs {
                        write!(f, " {a}")?;
                    }
                    writeln!(f, ")")
                }
                EunoiaCommand::Program {
                    name,
                    typed_params,
                    params,
                    ret,
                    body,
                } => {
                    write!(
                        f,
                        "(program {name} ({}) ({}) {ret}",
                        display_sequence(&typed_params.list),
                        display_sequence(&params.list),
                    )?;
                    for (a, b) in &body.list {
                        write!(f, " ({a} {b})")?;
                    }
                    writeln!(f, ")")
                }
                EunoiaCommand::Step {
                    id,
                    conclusion_clause,
                    rule,
                    premises,
                    arguments,
                }
                | EunoiaCommand::StepPop {
                    id,
                    conclusion_clause,
                    rule,
                    premises,
                    arguments,
                } => {
                    let command_name = if matches!(command, EunoiaCommand::Step { .. }) {
                        "step"
                    } else {
                        "step-pop"
                    };
                    write!(f, "({command_name} {id}")?;
                    if let Some(c) = conclusion_clause {
                        write!(f, " {c}")?;
                    }
                    write!(f, " :rule {rule}")?;
                    if !premises.list.is_empty() {
                        write!(f, " :premises ({})", display_sequence(&premises.list))?;
                    }
                    if !arguments.list.is_empty() {
                        write!(f, " :args ({})", display_sequence(&arguments.list))?;
                    }
                    writeln!(f, ")")
                }
                EunoiaCommand::DeclareConst { name, eunoia_type, attrs } => {
                    write!(f, "(declare-const {name} {eunoia_type}")?;
                    for a in attrs {
                        write!(f, " {a}")?;
                    }
                    writeln!(f, ")")
                }
                EunoiaCommand::DeclareSort { name, arity } => {
                    writeln!(f, "(declare-sort {name} {arity})")
                }
                EunoiaCommand::SetLogic { name } => writeln!(f, "(set-logic {})", name),
            }?;
        }
        Ok(())
    }
}

impl fmt::Display for EunoiaTypedParam {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let EunoiaTypedParam { name, eunoia_type, attrs } = self;
        if attrs.is_empty() {
            write!(f, "({name} {eunoia_type})")
        } else {
            write!(f, "({name} {eunoia_type} {})", display_sequence(attrs))
        }
    }
}

impl fmt::Display for EunoiaDefineAttr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let EunoiaDefineAttr::Type(ty) = self;
        write!(f, ":type {ty}")
    }
}

impl fmt::Display for EunoiaConsAttr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EunoiaConsAttr::RightAssoc => write!(f, ":right-assoc"),
            EunoiaConsAttr::LeftAssoc => write!(f, ":left-assoc"),
            EunoiaConsAttr::RightAssocNil(nil) => write!(f, ":right-assoc-nil {nil}"),
            EunoiaConsAttr::Chainable => write!(f, ":chainable"),
            EunoiaConsAttr::Pairwise => write!(f, ":pairwise"),
            EunoiaConsAttr::Binder(b) => write!(f, ":binder {b}"),
        }
    }
}

impl fmt::Display for EunoiaTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EunoiaTerm::Numeral(n) => write!(f, "{}", n),
            EunoiaTerm::Decimal(r) => {
                if r.is_negative() {
                    write!(f, "(- ")?;
                }
                if r.is_integer() {
                    write!(f, "{}.0", r.as_abs())?;
                } else {
                    write!(f, "(/ {}.0 {}.0)", r.numer().as_abs(), r.denom())?;
                }
                if r.is_negative() {
                    write!(f, ")")?;
                }
                Ok(())
            }
            EunoiaTerm::Rational(n, d) => write!(f, "{}/{}", n, d),
            EunoiaTerm::Id(name) => write!(f, "{}", name),
            EunoiaTerm::Type(ty) => write!(f, "{}", ty),
            EunoiaTerm::True => write!(f, "true"),
            EunoiaTerm::False => write!(f, "false"),
            EunoiaTerm::App(symbol, args) => {
                write!(f, "({}", symbol)?;
                for a in args {
                    write!(f, " {}", a)?;
                }
                write!(f, ")")
            }
            EunoiaTerm::HOApp(func, args) => write!(f, "( _ {} {})", func, display_sequence(args)),
            EunoiaTerm::Op(op, args) => write!(f, "({} {})", op, display_sequence(args)),
            EunoiaTerm::String(string) => {
                // TODO: should we escape the string?
                write!(f, "\"{}\"", string)
            }
            EunoiaTerm::List(terms) => write!(f, "( {} )", display_sequence(terms)),
            EunoiaTerm::Var(name, sort) => write!(f, "( {} {} )", name, sort),
        }
    }
}

impl fmt::Display for EunoiaOperator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            EunoiaOperator::Xor => "xor",
            EunoiaOperator::Not => "not",
            EunoiaOperator::Eq => "=",
            EunoiaOperator::GreaterThan => ">",
            EunoiaOperator::GreaterEq => ">=",
            EunoiaOperator::LessThan => "<",
            EunoiaOperator::LessEq => "<=",
        };
        write!(f, "{}", s)
    }
}

impl fmt::Display for EunoiaType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EunoiaType::Bool => write!(f, "Bool"),
            EunoiaType::Type => write!(f, "Type"),
            EunoiaType::Real => write!(f, "Real"),
            EunoiaType::Name(name) => write!(f, "{}", name),
            EunoiaType::Fun(kind_params, args, result) => {
                write!(
                    f,
                    "(-> {} {} {})",
                    display_sequence(kind_params),
                    display_sequence(args),
                    result,
                )
            }
        }
    }
}

impl fmt::Display for EunoiaKindParam {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let EunoiaKindParam(ty, attrs) = self;
        write!(f, "(! {} {})", ty, display_sequence(attrs))
    }
}

impl fmt::Display for EunoiaTypeAttr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EunoiaTypeAttr::Var(name) => write!(f, ":var {}", name),
            EunoiaTypeAttr::Implicit => write!(f, ":implicit"),
            EunoiaTypeAttr::Requires(lhs, rhs) => write!(f, ":requires ({} {})", lhs, rhs),
        }
    }
}

/// Returns an object that displays a sequence of objects, separated by spaces
fn display_sequence<T: fmt::Display>(seq: &[T]) -> impl fmt::Display {
    struct DisplaySequence<'a, T>(&'a [T]);
    impl<'a, T: fmt::Display> fmt::Display for DisplaySequence<'a, T> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self.0 {
                [] => Ok(()),
                [head, tail @ ..] => {
                    write!(f, "{}", head)?;
                    for elem in tail {
                        write!(f, " {}", elem)?;
                    }
                    Ok(())
                }
            }
        }
    }
    DisplaySequence(seq)
}
