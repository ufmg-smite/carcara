use crate::ast::*;
use std::fmt;

fn write_s_expr<H, T>(f: &mut fmt::Formatter, head: H, tail: &[T]) -> fmt::Result
where
    H: fmt::Display,
    T: fmt::Display,
{
    write!(f, "({}", head)?;
    for e in tail {
        write!(f, " {}", e)?;
    }
    write!(f, ")")
}

fn write_bindings(f: &mut fmt::Formatter, bindigns: &[(String, Rc<Term>)]) -> fmt::Result {
    match bindigns {
        [] => write!(f, "()"),
        [head, tail @ ..] => {
            write!(f, "(({} {})", head.0, head.1)?;
            for (var, term) in tail {
                write!(f, " ({} {})", var, term)?;
            }
            write!(f, ")")
        }
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> fmt::Result {
        match self {
            Term::Terminal(t) => write!(f, "{}", t),
            Term::App(func, args) => write_s_expr(f, func, args),
            Term::Op(op, args) => write_s_expr(f, op, args),
            Term::Sort(sort) => write!(f, "{}", sort),
            Term::Quant(quantifier, bindings, term) => {
                write!(f, "({} ", quantifier)?;
                write_bindings(f, bindings)?;
                write!(f, " {})", term)
            }
            Term::Choice((symbol, sort), term) => {
                write!(f, "(choice (({} {})) {})", symbol, sort, term)
            }
            Term::Let(bindings, term) => {
                write!(f, "(let ")?;
                write_bindings(f, bindings)?;
                write!(f, " {})", term)
            }
        }
    }
}

impl fmt::Display for Terminal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Terminal::Integer(i) => write!(f, "{}", i),
            Terminal::Real(r) => write!(
                f,
                "{}",
                (r.numer().to_f64().unwrap() / r.denom().to_f64().unwrap())
            ),
            Terminal::String(s) => write!(f, "\"{}\"", s),
            Terminal::Var(iden, _) => write!(f, "{}", iden),
        }
    }
}

impl fmt::Display for Identifier {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Identifier::Simple(s) => write!(f, "{}", s),
            Identifier::Indexed(s, indices) => write_s_expr(f, format!("_ {}", s), indices),
        }
    }
}

impl fmt::Display for Index {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Index::Numeral(n) => write!(f, "{}", n),
            Index::Symbol(s) => write!(f, "{}", s),
        }
    }
}

impl fmt::Display for Quantifier {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Quantifier::Forall => "forall",
                Quantifier::Exists => "exists",
            }
        )
    }
}

impl fmt::Display for Sort {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            // Function sorts should never be displayed, so the exact format we use is of little
            // importance
            Sort::Function(args) => write_s_expr(f, "Func", args),
            Sort::Atom(name, args) => match args.len() {
                0 => write!(f, "{}", name),
                _ => write_s_expr(f, name, args),
            },
            Sort::Bool => write!(f, "Bool"),
            Sort::Int => write!(f, "Int"),
            Sort::Real => write!(f, "Real"),
            Sort::String => write!(f, "String"),
            Sort::Array(x, y) => write_s_expr(f, "Array", &[x, y]),
        }
    }
}
