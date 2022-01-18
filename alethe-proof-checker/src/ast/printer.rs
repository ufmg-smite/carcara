use crate::ast::*;
use std::{fmt, io};

pub fn print_proof(commands: &[ProofCommand]) -> io::Result<()> {
    let mut stdout = io::stdout();
    (AlethePrinter { inner: &mut stdout }).write_proof(commands)
}

trait PrettyPrint {
    fn write_proof(&mut self, commands: &[ProofCommand]) -> io::Result<()>;
}

struct AlethePrinter<'a> {
    inner: &'a mut dyn io::Write,
}

impl<'a> PrettyPrint for AlethePrinter<'a> {
    fn write_proof(&mut self, commands: &[ProofCommand]) -> io::Result<()> {
        let mut iter = ProofIter::new(commands);
        while let Some(command) = iter.next() {
            match command {
                ProofCommand::Assume { index, term } => {
                    write!(self.inner, "(assume {} {})", index, term)?;
                }
                ProofCommand::Step(s) => self.write_step(&mut iter, s)?,
                ProofCommand::Subproof(s) => {
                    let end_step_index = s
                        .commands
                        .last()
                        .and_then(|s| match s {
                            ProofCommand::Step(s) => Some(s.index.clone()),
                            _ => None,
                        })
                        .unwrap();
                    write!(self.inner, "(anchor :step {}", end_step_index)?;

                    if !s.variable_args.is_empty() || !s.assignment_args.is_empty() {
                        write!(self.inner, " :args (")?;
                        let mut is_first = true;
                        for (name, sort) in &s.variable_args {
                            if !is_first {
                                write!(self.inner, " ")?;
                            }
                            is_first = false;
                            write!(self.inner, "({} {})", name, sort)?;
                        }
                        for (name, value) in &s.assignment_args {
                            if !is_first {
                                write!(self.inner, " ")?;
                            }
                            is_first = false;
                            write!(self.inner, "(:= ({} {}) {})", name, value.raw_sort(), value)?;
                        }
                        write!(self.inner, ")")?;
                    }
                    write!(self.inner, ")")?;
                }
            }
            writeln!(self.inner)?;
        }

        Ok(())
    }
}

impl<'a> AlethePrinter<'a> {
    fn write_step(&mut self, iter: &mut ProofIter, step: &ProofStep) -> io::Result<()> {
        write!(self.inner, "(step {} (cl", step.index)?;

        for t in &step.clause {
            write!(self.inner, " {}", t)?;
        }
        write!(self.inner, ")")?;

        write!(self.inner, " :rule {}", step.rule)?;

        if let [head, tail @ ..] = step.premises.as_slice() {
            write!(
                self.inner,
                " :premises ({}",
                iter.get_premise(*head).index()
            )?;
            for premise in tail {
                write!(self.inner, " {}", iter.get_premise(*premise).index())?;
            }
            write!(self.inner, ")")?;
        }

        if let [head, tail @ ..] = step.args.as_slice() {
            write!(self.inner, " :args (")?;
            self.write_proof_arg(head)?;
            for arg in tail {
                write!(self.inner, " ")?;
                self.write_proof_arg(arg)?;
            }
            write!(self.inner, ")")?;
        }

        if let [head, tail @ ..] = step.discharge.as_slice() {
            write!(self.inner, " :discharge ({}", head)?;
            for index in tail {
                write!(self.inner, " {}", index)?;
            }
            write!(self.inner, ")")?;
        }

        write!(self.inner, ")")?;
        Ok(())
    }

    fn write_proof_arg(&mut self, arg: &ProofArg) -> io::Result<()> {
        match arg {
            ProofArg::Term(t) => write!(self.inner, "{}", t),
            ProofArg::Assign(name, value) => {
                write!(self.inner, "(:= {} {})", name, value)
            }
        }
    }
}

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

impl fmt::Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> fmt::Result {
        match self {
            Term::Terminal(t) => write!(f, "{}", t),
            Term::App(func, args) => write_s_expr(f, func, args),
            Term::Op(op, args) => write_s_expr(f, op, args),
            Term::Sort(sort) => write!(f, "{}", sort),
            Term::Quant(quantifier, bindings, term) => {
                write!(f, "({} {} {})", quantifier, bindings, term)
            }
            Term::Choice((symbol, sort), term) => {
                write!(f, "(choice (({} {})) {})", symbol, sort, term)
            }
            Term::Let(bindings, term) => {
                write!(f, "(let {} {})", bindings, term)
            }
            Term::Lambda(bindings, term) => {
                write!(f, "(lambda {} {})", bindings, term)
            }
        }
    }
}

impl fmt::Debug for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl fmt::Display for Terminal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Terminal::Integer(i) => write!(f, "{}", i),
            Terminal::Real(r) => write!(f, "{}", DisplayRatio(r)),
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

impl fmt::Display for BindingList {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.as_slice() {
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

/// A wrapper struct that implements `fmt::Display` for `BigRational`s.
pub struct DisplayRatio<'a>(pub &'a BigRational);

impl<'a> fmt::Display for DisplayRatio<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let float_value = self.0.numer().to_f64().unwrap() / self.0.denom().to_f64().unwrap();

        // We use the `Debug` (that is, "{:?}") representation because it sets a minimum precision
        // of 1 digit. That means we always print 1.0 as `1.0`, instead of as `1`
        write!(f, "{:?}", float_value)
    }
}
