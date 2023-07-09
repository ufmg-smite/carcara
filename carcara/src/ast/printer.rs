//! A pretty printer for Alethe proofs.

use crate::{
    ast::*,
    parser::Token,
    utils::{is_symbol_character, DedupIterator},
};
use ahash::AHashMap;
use std::{borrow::Cow, fmt, io};

/// Prints a proof to the standard output.
///
/// If `use_sharing` is `true`, terms that are used multiple times will make use of sharing. The
/// first time a novel term appears, it receives a unique name using the `:named` attribute. After
/// that, any occurrence of that term will simply use this name, instead of printing the whole term.
pub fn print_proof(commands: &[ProofCommand], use_sharing: bool) -> io::Result<()> {
    let mut stdout = io::stdout();
    let mut printer = AlethePrinter {
        inner: &mut stdout,
        term_indices: use_sharing.then(AHashMap::new),
        term_sharing_variable_prefix: "@p_",
    };
    printer.write_proof(commands)
}

/// Given the conclusion clause of a `lia_generic` step, this method will write to `dest` the
/// corresponding SMT problem instance.
pub fn write_lia_smt_instance(
    dest: &mut dyn io::Write,
    clause: &[Rc<Term>],
    use_sharing: bool,
) -> io::Result<()> {
    let mut printer = AlethePrinter {
        inner: dest,
        term_indices: use_sharing.then(AHashMap::new),
        term_sharing_variable_prefix: "p_",
    };
    printer.write_lia_smt_instance(clause)
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
            // - Terminal terms (i.e., constants or variables) could in theory be shared,
            // but, since they are very small, it's not worth it to give them a name.
            //
            // - Sorts are represented as terms, but they are not actually terms in the grammar, so
            // we can't use the `(! ... :named ...)` syntax to give them a name.
            //
            // - If a term is only used once in the proof, there is no reason to give it a name. We
            // detect this case by checking if the number of references to it's `Rc` is exactly 1.
            if !self.is_terminal() && !self.is_sort() && Rc::strong_count(self) > 1 {
                return if let Some(i) = indices.get(self) {
                    write!(p.inner, "{}{}", p.term_sharing_variable_prefix, i)
                } else {
                    let i = indices.len();
                    indices.insert(self.clone(), i);
                    write!(p.inner, "(! ")?;
                    p.write_raw_term(self)?;
                    write!(p.inner, " :named {}{})", p.term_sharing_variable_prefix, i)
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
    term_sharing_variable_prefix: &'static str,
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
                ProofCommand::Closing => {}
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

    fn write_raw_term(&mut self, term: &Term) -> io::Result<()> {
        match term {
            Term::Const(c) => write!(self.inner, "{}", c),
            Term::Var(iden, _) => write!(self.inner, "{}", iden),
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

    fn write_lia_smt_instance(&mut self, clause: &[Rc<Term>]) -> io::Result<()> {
        for term in clause.iter().dedup() {
            write!(self.inner, "(assert (not ")?;
            term.print_with_sharing(self)?;
            writeln!(self.inner, "))")?;
        }
        Ok(())
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
        // If the alternate flag (`#`) is passed, we disable printing with sharing
        let use_sharing = !f.alternate();
        let mut buf = Vec::new();
        let mut printer = AlethePrinter {
            inner: &mut buf,
            term_indices: use_sharing.then(AHashMap::new),
            term_sharing_variable_prefix: "@p_",
        };
        printer.write_raw_term(self).unwrap();
        let result = std::str::from_utf8(&buf).unwrap();
        write!(f, "{}", result)
    }
}

impl fmt::Debug for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl fmt::Display for Constant {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Constant::Integer(i) => write!(f, "{}", i),
            Constant::Real(r) => {
                if r.is_integer() {
                    write!(f, "{:?}.0", r.numer())
                } else {
                    write!(f, "{:?}", r.to_f64())
                }
            }
            Constant::String(s) => write!(f, "\"{}\"", escape_string(s)),
        }
    }
}

impl fmt::Display for Ident {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Ident::Simple(s) => write!(f, "{}", quote_symbol(s)),
            Ident::Indexed(s, indices) => {
                write_s_expr(f, format!("_ {}", quote_symbol(s)), indices)
            }
        }
    }
}

impl fmt::Display for IdentIndex {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            IdentIndex::Numeral(n) => write!(f, "{}", n),
            IdentIndex::Symbol(s) => write!(f, "{}", quote_symbol(s)),
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

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Token::OpenParen => write!(f, "("),
            Token::CloseParen => write!(f, ")"),
            Token::Symbol(s) => write!(f, "{}", quote_symbol(s)),
            Token::Keyword(k) => write!(f, ":{}", k),
            Token::Numeral(n) => write!(f, "{}", n),
            Token::Decimal(r) => write!(f, "{}", r),
            Token::String(s) => write!(f, "\"{}\"", escape_string(s)),
            Token::ReservedWord(r) => write!(f, "{}", r),
            Token::Eof => write!(f, "EOF"),
        }
    }
}

impl fmt::Display for ProblemPrelude {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "(set-logic {})", self.logic.as_deref().unwrap_or("ALL"))?;

        for (name, arity) in &self.sort_declarations {
            writeln!(f, "(declare-sort {} {})", name, arity)?;
        }

        for (name, sort) in &self.function_declarations {
            write!(f, "(declare-fun {} ", name)?;
            if let Sort::Function(sorts) = sort.as_sort().unwrap() {
                write_s_expr(f, &sorts[0], &sorts[1..sorts.len() - 1])?;
                writeln!(f, " {})", sorts.last().unwrap())?;
            } else {
                writeln!(f, "() {})", sort)?;
            }
        }
        Ok(())
    }
}
