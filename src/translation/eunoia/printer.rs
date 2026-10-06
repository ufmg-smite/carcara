//! A pretty printer for Eunoia proofs.

use indexmap::IndexMap;

use crate::{ast::Rc, translation::eunoia::ast::*};
use std::fmt;

const SHARING_THRESHOLD: usize = 2;
const SHARING_PREFIX: &str = "@t";

/// Maps each shared term to the index used in its name. The terms are in the order they must be
/// defined.
type SharingNames = Option<IndexMap<Rc<EunoiaTerm>, usize>>;

pub struct DisplayEunoiaProof<'a>(pub &'a EunoiaProof, pub bool);

impl<'a> fmt::Display for DisplayEunoiaProof<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let names: SharingNames = self.1.then(|| {
            proof_usage(self.0)
                .into_iter()
                .filter(|(_, count)| *count >= SHARING_THRESHOLD)
                .enumerate()
                .map(|(i, (term, _))| (term, i))
                .collect()
        });

        // The definitions are printed at the top, outside of any `assume-push` scope, since the
        // definitions made inside one are discarded by the closing `step-pop`
        if let Some(map) = &names {
            for (term, i) in map {
                writeln!(
                    f,
                    "(define {SHARING_PREFIX}{i} () {})",
                    DisplayTerm(term.as_ref(), &names)
                )?;
            }
        }

        for command in self.0 {
            match command {
                EunoiaCommand::Include { path } => writeln!(f, "(include \"{path}\")"),
                EunoiaCommand::Assume { name, term } => {
                    writeln!(f, "(assume {name} {})", term.display(&names))
                }
                EunoiaCommand::AssumePush { name, term } => {
                    writeln!(f, "(assume-push {name} {})", term.display(&names))
                }
                EunoiaCommand::Define { name, typed_params, term, attrs } => {
                    write!(
                        f,
                        "(define {name} ({}) {}",
                        display_sequence(&typed_params.list),
                        term.display(&names)
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
                        write!(f, " ({} {})", a.display(&None), b.display(&None))?;
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
                        write!(f, " {}", c.display(&names))?;
                    }
                    write!(f, " :rule {rule}")?;
                    if !premises.list.is_empty() {
                        write!(f, " :premises ({})", display_terms(&premises.list, &names))?;
                    }
                    if !arguments.list.is_empty() {
                        write!(f, " :args ({})", display_terms(&arguments.list, &names))?;
                    }
                    writeln!(f, ")")
                }
                EunoiaCommand::DeclareConst { name, eunoia_type, attrs } => {
                    write!(f, "(declare-const {name} {}", eunoia_type.display(&None))?;
                    for a in attrs {
                        write!(f, " {a}")?;
                    }
                    writeln!(f, ")")
                }
                EunoiaCommand::DeclareSort { name, arity } => {
                    writeln!(f, "(declare-sort {name} {})", arity.display(&None))
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
            EunoiaConsAttr::RightAssocNil(nil) => {
                write!(f, ":right-assoc-nil {}", nil.display(&None))
            }
            EunoiaConsAttr::Chainable => write!(f, ":chainable"),
            EunoiaConsAttr::Pairwise => write!(f, ":pairwise"),
            EunoiaConsAttr::Binder(b) => write!(f, ":binder {b}"),
        }
    }
}

impl Rc<EunoiaTerm> {
    fn display<'a>(&'a self, names: &'a SharingNames) -> impl fmt::Display {
        struct DisplayShared<'a>(&'a Rc<EunoiaTerm>, &'a SharingNames);
        impl<'a> fmt::Display for DisplayShared<'a> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                match self.1.as_ref().and_then(|names| names.get(self.0)) {
                    Some(i) => write!(f, "{SHARING_PREFIX}{i}"),
                    None => write!(f, "{}", DisplayTerm(self.0.as_ref(), self.1)),
                }
            }
        }
        DisplayShared(self, names)
    }
}

struct DisplayTerm<'a>(&'a EunoiaTerm, &'a SharingNames);

impl<'a> fmt::Display for DisplayTerm<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let DisplayTerm(term, names) = self;
        match term {
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
                    write!(f, " {}", a.display(names))?;
                }
                write!(f, ")")
            }
            EunoiaTerm::HOApp(func, args) => {
                write!(
                    f,
                    "( _ {} {})",
                    func.display(names),
                    display_terms(args, names)
                )
            }
            EunoiaTerm::Op(op, args) => {
                write!(f, "({} {})", op, display_terms(args, names))
            }
            EunoiaTerm::String(string) => {
                // TODO: should we escape the string?
                write!(f, "\"{}\"", string)
            }
            EunoiaTerm::List(terms) => write!(f, "( {} )", display_terms(terms, names)),
            EunoiaTerm::Var(name, sort) => write!(f, "( {} {} )", name, sort.display(names)),
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
            EunoiaTypeAttr::Requires(lhs, rhs) => write!(
                f,
                ":requires ({} {})",
                lhs.display(&None),
                rhs.display(&None),
            ),
        }
    }
}

/// Returns an object that displays a sequence of terms, separated by spaces
fn display_terms<'a>(terms: &'a [Rc<EunoiaTerm>], names: &'a SharingNames) -> impl fmt::Display {
    display_sequence(terms.iter().map(move |term| term.display(names)))
}

/// Returns an object that displays a sequence of objects, separated by spaces
fn display_sequence<I>(seq: I) -> impl fmt::Display
where
    I: IntoIterator + Clone,
    I::Item: fmt::Display,
{
    struct DisplaySequence<T>(T);
    impl<T> fmt::Display for DisplaySequence<T>
    where
        T: IntoIterator + Clone,
        T::Item: fmt::Display,
    {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let mut iter = self.0.clone().into_iter();
            if let Some(head) = iter.next() {
                write!(f, "{}", head)?;
                for elem in iter {
                    write!(f, " {}", elem)?;
                }
            }
            Ok(())
        }
    }
    DisplaySequence(seq)
}

fn proof_usage(proof: &EunoiaProof) -> IndexMap<Rc<EunoiaTerm>, usize> {
    let mut usage = IndexMap::new();
    for command in proof {
        match command {
            EunoiaCommand::Assume { term, .. }
            | EunoiaCommand::AssumePush { term, .. }
            | EunoiaCommand::Define { term, .. } => count_term_usage(&mut usage, term),
            EunoiaCommand::Step {
                conclusion_clause,
                premises,
                arguments,
                ..
            }
            | EunoiaCommand::StepPop {
                conclusion_clause,
                premises,
                arguments,
                ..
            } => {
                let terms = conclusion_clause
                    .iter()
                    .chain(&premises.list)
                    .chain(&arguments.list);
                for t in terms {
                    count_term_usage(&mut usage, t);
                }
            }
            _ => (),
        }
    }
    usage
}

fn count_term_usage(usage: &mut IndexMap<Rc<EunoiaTerm>, usize>, term: &Rc<EunoiaTerm>) {
    // If we've already seen this term we don't have to process its children
    if let Some(count) = usage.get_mut(term) {
        *count += 1;
        return;
    }

    // It's important to process the children before inserting the parent term to ensure the
    // resulting `IndexMap` is correctly sorted
    match term.as_ref() {
        EunoiaTerm::App(_, args) | EunoiaTerm::Op(_, args) => {
            for a in args {
                count_term_usage(usage, a);
            }
            usage.insert(term.clone(), 1);
        }
        EunoiaTerm::HOApp(func, args) => {
            count_term_usage(usage, func);
            for a in args {
                count_term_usage(usage, a);
            }
            usage.insert(term.clone(), 1);
        }
        _ => (),
    }
}
