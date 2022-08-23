use crate::{ast::*, utils::is_symbol_character};
use ahash::AHashMap;
use std::{borrow::Cow, fmt, io};

pub fn print_proof(commands: &[ProofCommand], use_sharing: bool) -> io::Result<()> {
    let mut stdout = io::stdout();
    let mut printer = AlethePrinter {
        inner: &mut stdout,
        term_indices: use_sharing.then(AHashMap::new),
    };
    printer.write_proof(commands)
}

trait PrintProof {
    fn write_proof(&mut self, commands: &[ProofCommand]) -> io::Result<()>;
}

trait PrintWithSharing {
    fn print_with_sharing(&self, p: &mut AlethePrinter) -> io::Result<()>;
}

impl<T: PrintWithSharing> PrintWithSharing for &T {
    fn print_with_sharing(&self, p: &mut AlethePrinter) -> io::Result<()> {
        PrintWithSharing::print_with_sharing(*self, p)
    }
}

impl PrintWithSharing for Rc<Term> {
    fn print_with_sharing(&self, p: &mut AlethePrinter) -> io::Result<()> {
        if let Some(indices) = &mut p.term_indices {
            // There are three cases where we don't use sharing when printing a term:
            //
            // - Terminal terms (e.g., integers, reals, variables, etc.) could in theory be shared,
            // but, since they are very small, it's not worth it to give them a name.
            //
            // - Sorts are represented as terms, but they are not actually terms in the grammar, so
            // we can't use the `(! ... :named ...)` syntax to give them a name.
            //
            // - If a term is only used once in the proof, there is no reason to give it a name. We
            // detect this case by checking if the number of references to it's `Rc` is exaclty 1.
            if !self.is_terminal() && !self.is_sort() && Rc::strong_count(self) > 1 {
                return if let Some(i) = indices.get(self) {
                    write!(p.inner, "@p_{}", i)
                } else {
                    let i = indices.len();
                    indices.insert(self.clone(), i);
                    write!(p.inner, "(! ")?;
                    p.write_raw_term(self)?;
                    write!(p.inner, " :named @p_{})", i)
                };
            }
        }
        p.write_raw_term(self)
    }
}

impl PrintWithSharing for SortedVar {
    fn print_with_sharing(&self, p: &mut AlethePrinter) -> io::Result<()> {
        let (name, value) = self;
        write!(p.inner, "({} ", quote_symbol(name))?;
        value.print_with_sharing(p)?;
        write!(p.inner, ")")
    }
}

impl PrintWithSharing for BindingList {
    fn print_with_sharing(&self, p: &mut AlethePrinter) -> io::Result<()> {
        match self.as_slice() {
            [] => write!(p.inner, "()"),
            [head, tail @ ..] => p.write_s_expr(head, tail),
        }
    }
}

impl PrintWithSharing for Operator {
    fn print_with_sharing(&self, p: &mut AlethePrinter) -> io::Result<()> {
        write!(p.inner, "{}", self)
    }
}

struct AlethePrinter<'a> {
    inner: &'a mut dyn io::Write,
    term_indices: Option<AHashMap<Rc<Term>, usize>>,
}

impl<'a> PrintProof for AlethePrinter<'a> {
    fn write_proof(&mut self, commands: &[ProofCommand]) -> io::Result<()> {
        let mut iter = ProofIter::new(commands);
        while let Some(command) = iter.next() {
            match command {
                ProofCommand::Assume { id, term } => {
                    write!(self.inner, "(assume {} ", id)?;
                    term.print_with_sharing(self)?;
                    write!(self.inner, ")")?;
                }
                ProofCommand::Step(s) => self.write_step(&mut iter, s)?,
                ProofCommand::Subproof(s) => {
                    write!(self.inner, "(anchor :step {}", command.id())?;

                    if !s.variable_args.is_empty() || !s.assignment_args.is_empty() {
                        write!(self.inner, " :args (")?;
                        let mut is_first = true;
                        for var in &s.variable_args {
                            if !is_first {
                                write!(self.inner, " ")?;
                            }
                            is_first = false;
                            var.print_with_sharing(self)?;
                        }
                        for (name, value) in &s.assignment_args {
                            if !is_first {
                                write!(self.inner, " ")?;
                            }
                            is_first = false;
                            write!(self.inner, "(:= {} ", name)?;
                            value.print_with_sharing(self)?;
                            write!(self.inner, ")")?;
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
    fn write_s_expr<H, T>(&mut self, head: &H, tail: &[T]) -> io::Result<()>
    where
        H: PrintWithSharing + ?Sized,
        T: PrintWithSharing,
    {
        write!(self.inner, "(")?;
        head.print_with_sharing(self)?;
        for t in tail {
            write!(self.inner, " ")?;
            t.print_with_sharing(self)?;
        }
        write!(self.inner, ")")
    }

    fn write_raw_term(&mut self, term: &Rc<Term>) -> io::Result<()> {
        match term.as_ref() {
            Term::Terminal(t) => write!(self.inner, "{}", t),
            Term::App(func, args) => self.write_s_expr(func, args),
            Term::Op(op, args) => self.write_s_expr(op, args),
            Term::Sort(sort) => write!(self.inner, "{}", sort),
            Term::Quant(quantifier, bindings, term) => {
                write!(self.inner, "({} ", quantifier)?;
                bindings.print_with_sharing(self)?;
                write!(self.inner, " ")?;
                term.print_with_sharing(self)?;
                write!(self.inner, ")")
            }
            Term::Choice(var, term) => {
                write!(self.inner, "(choice (")?;
                var.print_with_sharing(self)?;
                write!(self.inner, ") ")?;
                term.print_with_sharing(self)?;
                write!(self.inner, ")")
            }
            Term::Let(bindings, term) => {
                write!(self.inner, "(let ")?;
                bindings.print_with_sharing(self)?;
                write!(self.inner, " ")?;
                term.print_with_sharing(self)?;
                write!(self.inner, ")")
            }
            Term::Lambda(bindings, term) => {
                write!(self.inner, "(lambda ")?;
                bindings.print_with_sharing(self)?;
                write!(self.inner, " ")?;
                term.print_with_sharing(self)?;
                write!(self.inner, ")")
            }
        }
    }

    fn write_step(&mut self, iter: &mut ProofIter, step: &ProofStep) -> io::Result<()> {
        write!(self.inner, "(step {} (cl", step.id)?;

        for t in &step.clause {
            write!(self.inner, " ")?;
            t.print_with_sharing(self)?;
        }
        write!(self.inner, ")")?;

        write!(self.inner, " :rule {}", step.rule)?;

        if let [head, tail @ ..] = step.premises.as_slice() {
            write!(self.inner, " :premises ({}", iter.get_premise(*head).id())?;
            for premise in tail {
                write!(self.inner, " {}", iter.get_premise(*premise).id())?;
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
            write!(self.inner, " :discharge ({}", iter.get_premise(*head).id())?;
            for id in tail {
                write!(self.inner, " {}", iter.get_premise(*id).id())?;
            }
            write!(self.inner, ")")?;
        }

        write!(self.inner, ")")?;
        Ok(())
    }

    fn write_proof_arg(&mut self, arg: &ProofArg) -> io::Result<()> {
        match arg {
            ProofArg::Term(t) => t.print_with_sharing(self),
            ProofArg::Assign(name, value) => {
                write!(self.inner, "(:= {} ", name)?;
                value.print_with_sharing(self)?;
                write!(self.inner, ")")
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

fn quote_symbol(symbol: &str) -> Cow<str> {
    use crate::parser::Reserved;
    use std::str::FromStr;

    assert!(symbol.chars().all(|c| c != '|'));

    // Any symbol that:
    // - is an empty string,
    // - starts with a digit,
    // - is a reserved word, or
    // - contains non-symbol characters
    // must be quoted
    if symbol.is_empty()
        || symbol.chars().next().unwrap().is_ascii_digit()
        || Reserved::from_str(symbol).is_ok()
        || symbol.chars().any(|c| !is_symbol_character(c))
    {
        Cow::Owned(format!("|{}|", symbol))
    } else {
        Cow::Borrowed(symbol)
    }
}

fn escape_string(string: &str) -> Cow<str> {
    if string.contains('"') {
        Cow::Owned(string.replace('"', "\"\""))
    } else {
        Cow::Borrowed(string)
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
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
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl fmt::Display for Terminal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Terminal::Integer(i) => write!(f, "{}", i),
            Terminal::Real(r) => write!(f, "{:?}", r.to_f64()),
            Terminal::String(s) => write!(f, "\"{}\"", escape_string(s)),
            Terminal::Var(iden, _) => write!(f, "{}", iden),
        }
    }
}

impl fmt::Display for Identifier {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Identifier::Simple(s) => write!(f, "{}", quote_symbol(s)),
            Identifier::Indexed(s, indices) => {
                write_s_expr(f, format!("_ {}", quote_symbol(s)), indices)
            }
        }
    }
}

impl fmt::Display for Index {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Index::Numeral(n) => write!(f, "{}", n),
            Index::Symbol(s) => write!(f, "{}", quote_symbol(s)),
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
                write!(f, "(({} {})", quote_symbol(&head.0), head.1)?;
                for (var, term) in tail {
                    write!(f, " ({} {})", quote_symbol(var), term)?;
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
                0 => write!(f, "{}", quote_symbol(name)),
                _ => write_s_expr(f, quote_symbol(name), args),
            },
            Sort::Bool => write!(f, "Bool"),
            Sort::Int => write!(f, "Int"),
            Sort::Real => write!(f, "Real"),
            Sort::String => write!(f, "String"),
            Sort::Array(x, y) => write_s_expr(f, "Array", &[x, y]),
        }
    }
}
