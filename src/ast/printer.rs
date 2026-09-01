//! A pretty printer for Alethe proofs.

use crate::{
    ast::{
        AnchorArg, Binder, BindingList, Constant, MatchCase, MatchPattern, Operator,
        ProblemPrelude, Proof, ProofCommand, Rc, Sort, SortedVar, Term,
    },
    parser::Token,
    utils::{DedupIterator, is_symbol_character},
};
use carcara_macros::GenerateSetters;
use std::{
    borrow::Cow,
    collections::HashMap,
    fmt,
    sync::atomic::{AtomicBool, Ordering},
};

/// A global variable that controls whether the default implementation of [`fmt::Display`] should
/// make use of term sharing or not.
pub static USE_SHARING_IN_TERM_DISPLAY: AtomicBool = AtomicBool::new(false);

/// The minimum number of times a term must appear in the proof for it to be shared when printing
/// with sharing enabled.
const SHARING_THRESHOLD: usize = 2;

#[derive(Debug, Clone, GenerateSetters)]
pub struct DisplayOptions {
    use_sharing: bool,
    sharing_prefix: String,
    smt_lib_strict: bool,
}

impl DisplayOptions {
    /// Creates a new [`DisplayOptions`].
    pub fn new() -> Self {
        Self {
            use_sharing: false,
            sharing_prefix: "@p_".to_owned(),
            smt_lib_strict: false,
        }
    }
}

impl Default for DisplayOptions {
    fn default() -> Self {
        Self::new()
    }
}

impl Proof {
    pub fn display(&self, options: DisplayOptions) -> impl fmt::Display {
        struct DisplayProof<'a>(&'a Proof, DisplayOptions);

        impl fmt::Display for DisplayProof<'_> {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                let mut printer = Printer::new(&self.1);
                if self.1.use_sharing {
                    printer.term_usage = count_proof_term_usage(self.0);
                }
                self.0.print(f, &mut printer)
            }
        }

        DisplayProof(self, options)
    }
}

impl Term {
    pub fn display(&self, options: DisplayOptions) -> impl fmt::Display {
        struct DisplayTerm<'a>(&'a Term, DisplayOptions);

        impl fmt::Display for DisplayTerm<'_> {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                let mut printer = Printer::new(&self.1);
                if self.1.use_sharing {
                    let mut counts = HashMap::new();
                    count_subterms_usage(self.0, &mut counts);
                    printer.term_usage = counts;
                }
                self.0.print(f, &mut printer)
            }
        }

        DisplayTerm(self, options)
    }
}

pub fn display_asserts(assertions: &[Rc<Term>], options: DisplayOptions) -> impl fmt::Display {
    struct DisplayAsserts<'a>(&'a [Rc<Term>], DisplayOptions);

    impl fmt::Display for DisplayAsserts<'_> {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            let mut printer = Printer::new(&self.1);
            if self.1.use_sharing {
                let mut counts = HashMap::new();
                for term in self.0 {
                    count_term_usage(term, &mut counts);
                }
                printer.term_usage = counts;
            }
            for assertion in self.0 {
                write!(f, "(assert ")?;
                assertion.print(f, &mut printer)?;
                writeln!(f, ")")?;
            }
            Ok(())
        }
    }

    DisplayAsserts(assertions, options)
}

pub(crate) fn display_clause_smt_problem(
    clause: &[Rc<Term>],
    options: DisplayOptions,
) -> impl fmt::Display {
    struct DisplayClauseProblem<'a>(&'a [Rc<Term>], DisplayOptions);

    impl fmt::Display for DisplayClauseProblem<'_> {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            let mut printer = Printer::new(&self.1);
            if self.1.use_sharing {
                let mut counts = HashMap::new();
                for term in self.0 {
                    count_term_usage(term, &mut counts);
                }
                printer.term_usage = counts;
            }
            for term in self.0.iter().dedup() {
                write!(f, "(assert (not ")?;
                term.print(f, &mut printer)?;
                writeln!(f, "))")?;
            }
            Ok(())
        }
    }

    DisplayClauseProblem(clause, options)
}

struct Printer<'a> {
    options: &'a DisplayOptions,
    term_indices: Option<HashMap<Rc<Term>, usize>>,
    term_usage: HashMap<Rc<Term>, usize>,
    defined_constants: HashMap<Rc<Term>, String>,

    /// The number of nested binder terms which we are currently inside of.
    ///
    /// This is used to disable term sharing in non-closed terms.
    binder_depth: usize,
}

impl<'a> Printer<'a> {
    pub fn new(options: &'a DisplayOptions) -> Self {
        Self {
            options,
            term_indices: options.use_sharing.then(HashMap::new),
            term_usage: HashMap::new(),
            defined_constants: HashMap::new(),
            binder_depth: 0,
        }
    }

    fn s_expr<H, T>(&mut self, f: &mut fmt::Formatter, head: &H, tail: &[T]) -> fmt::Result
    where
        H: Print + ?Sized,
        T: Print,
    {
        write!(f, "(")?;
        head.print(f, self)?;
        self.s_expr_tail(f, tail)
    }

    fn s_expr_tail<T: Print>(&mut self, f: &mut fmt::Formatter, tail: &[T]) -> fmt::Result {
        for t in tail {
            write!(f, " ")?;
            t.print(f, self)?;
        }
        write!(f, ")")
    }
}

/// Counts the number of times each term appears in `proof`.
fn count_proof_term_usage(proof: &Proof) -> HashMap<Rc<Term>, usize> {
    fn count_commands_term_usage(commands: &[ProofCommand], counts: &mut HashMap<Rc<Term>, usize>) {
        for command in commands {
            match command {
                ProofCommand::Assume { term, .. } => count_term_usage(term, counts),
                ProofCommand::Step(step) => {
                    for term in &step.clause {
                        count_term_usage(term, counts);
                    }
                    for arg in &step.args {
                        count_term_usage(arg, counts);
                    }
                }
                ProofCommand::Subproof(subproof) => {
                    for arg in &subproof.args {
                        if let AnchorArg::Assign(_, value) = arg {
                            count_term_usage(value, counts);
                        }
                    }
                    count_commands_term_usage(&subproof.commands, counts);
                }
            }
        }
    }

    let mut counts = HashMap::new();
    for (_, term, _) in &proof.constant_definitions {
        count_term_usage(term, &mut counts);
    }
    count_commands_term_usage(&proof.commands, &mut counts);
    counts
}

/// Counts the occurrences of `term` and its subterms.
///
/// Once a term reaches the sharing threshold, we know it will be shared, so we stop counting it
/// (and don't traverse its subterms again, since they'll only appear once, inside the shared term's
/// definition).
fn count_term_usage(term: &Rc<Term>, counts: &mut HashMap<Rc<Term>, usize>) {
    if term.is_const() || term.is_var() {
        return;
    }
    let entry = counts.entry(term.clone()).or_insert(0);
    if *entry >= SHARING_THRESHOLD {
        return;
    }
    *entry += 1;
    if *entry >= SHARING_THRESHOLD {
        return;
    }
    count_subterms_usage(term, counts);
}

/// Counts the occurrences of the subterms of `term`, but not `term` itself.
fn count_subterms_usage(term: &Term, counts: &mut HashMap<Rc<Term>, usize>) {
    match term {
        Term::App(f, args) => {
            count_term_usage(f, counts);
            for arg in args {
                count_term_usage(arg, counts);
            }
        }
        Term::Op(_, args) | Term::AsOp(_, _, args) => {
            for arg in args {
                count_term_usage(arg, counts);
            }
        }
        Term::ParamOp { op_args, args, .. } => {
            for arg in op_args {
                count_term_usage(arg, counts);
            }
            for arg in args {
                count_term_usage(arg, counts);
            }
        }
        // The scrutinee is printed outside the binder scope, but the case bodies bind variables.
        Term::Match(scrutinee, _) => count_term_usage(scrutinee, counts),
        // Terms inside binders can't be shared, so we don't count them.
        Term::Binder(..) | Term::Let(..) => {}
        Term::Const(_) | Term::Var(..) => {}
    }
}

trait Print {
    fn print(&self, f: &mut fmt::Formatter, p: &mut Printer) -> fmt::Result;
}

impl<T: Print> Print for &T {
    fn print(&self, f: &mut fmt::Formatter, p: &mut Printer) -> fmt::Result {
        Print::print(*self, f, p)
    }
}

impl Print for str {
    fn print(&self, f: &mut fmt::Formatter, _: &mut Printer) -> fmt::Result {
        write!(f, "{}", self)
    }
}

impl Print for Proof {
    fn print(&self, f: &mut fmt::Formatter, p: &mut Printer) -> fmt::Result {
        for (name, value, sort) in &self.constant_definitions {
            write!(f, "(define-fun {} () {} ", quote_symbol(name), sort)?;
            value.print(f, p)?;
            writeln!(f, ")")?;
        }
        p.defined_constants = self
            .constant_definitions
            .iter()
            .cloned()
            .map(|(name, term, _)| (term, name))
            .collect();
        let mut iter = self.iter();
        while let Some(command) = iter.next() {
            match command {
                ProofCommand::Assume { id, term } => {
                    write!(f, "(assume {} ", quote_symbol(id))?;
                    term.print(f, p)?;
                    write!(f, ")")?;
                }
                ProofCommand::Step(step) => {
                    write!(f, "(step {} ", quote_symbol(&step.id))?;
                    p.s_expr(f, "cl", &step.clause)?;

                    write!(f, " :rule {}", step.rule)?;

                    if let [head, tail @ ..] = step.premises.as_slice() {
                        let id = iter.get_premise(*head).id();
                        write!(f, " :premises ({}", quote_symbol(id))?;
                        for premise in tail {
                            let id = iter.get_premise(*premise).id();
                            write!(f, " {}", quote_symbol(id))?;
                        }
                        write!(f, ")")?;
                    }

                    if let [head, tail @ ..] = step.args.as_slice() {
                        write!(f, " :args ")?;
                        p.s_expr(f, head, tail)?;
                    }

                    if let [head, tail @ ..] = step.discharge.as_slice() {
                        let id = iter.get_premise(*head).id();
                        write!(f, " :discharge ({}", id)?;
                        for discharge in tail {
                            let id = iter.get_premise(*discharge).id();
                            write!(f, " {}", quote_symbol(id))?;
                        }
                        write!(f, ")")?;
                    }

                    write!(f, ")")?;
                }
                ProofCommand::Subproof(s) => {
                    write!(f, "(anchor :step {}", quote_symbol(command.id()))?;
                    if let [head, tail @ ..] = s.args.as_slice() {
                        write!(f, " :args ")?;
                        p.s_expr(f, head, tail)?;
                    }
                    write!(f, ")")?;
                }
            }
            writeln!(f)?;
        }
        p.defined_constants.clear();
        Ok(())
    }
}

impl Print for AnchorArg {
    fn print(&self, f: &mut fmt::Formatter, p: &mut Printer) -> fmt::Result {
        match self {
            AnchorArg::Variable(var) => var.print(f, p),
            AnchorArg::Assign(var, value) => {
                write!(f, "(:= ")?;
                var.print(f, p)?;
                write!(f, " ")?;
                value.print(f, p)?;
                write!(f, ")")
            }
        }
    }
}

impl Print for Rc<Term> {
    fn print(&self, f: &mut fmt::Formatter, p: &mut Printer) -> fmt::Result {
        if let Some(name) = p.defined_constants.get(self) {
            return write!(f, "{}", quote_symbol(name));
        }
        if let Some(indices) = &mut p.term_indices {
            // If there is already a name for this term, use it
            if let Some(i) = indices.get(self) {
                return write!(f, "{}{}", p.options.sharing_prefix, i);
            }

            // There are a few cases where we cannot use `:named` when printing a term:
            let cannot_use_sharing =
                // - We are inside of a binder, so this term might not be closed. It would be more
                // accurate to compute if the term is actually closed (if it has any free variables
                // besides the problem's global variables), but this is expensive to do, so we
                // conservatively disable sharing based on the binder depth instead.
                p.binder_depth > 0
                // - Terminal terms (i.e., constants or variables) could in theory be shared,
                // but, since they are very small, it's not worth it to give them a name.
                || self.is_const() || self.is_var()
                // - If a term does not appear often enough in the proof, there is no reason to
                // give it a name. The usage counts are precomputed when the printer is created.
                || p.term_usage.get(self).copied().unwrap_or(0) < SHARING_THRESHOLD;

            if !cannot_use_sharing {
                let i = indices.len();
                indices.insert(self.clone(), i);
                write!(f, "(! ")?;
                self.as_ref().print(f, p)?;
                return write!(f, " :named {}{})", p.options.sharing_prefix, i);
            }
        }
        self.as_ref().print(f, p)
    }
}

impl Print for Term {
    fn print(&self, f: &mut fmt::Formatter, p: &mut Printer) -> fmt::Result {
        match self {
            Term::Const(c) => {
                if p.options.smt_lib_strict {
                    if let Constant::Integer(i) = c {
                        if i.is_negative() {
                            write!(f, "(- {})", i.clone().abs())
                        } else {
                            write!(f, "{}", i)
                        }
                    } else if let Constant::Real(r) = c {
                        if r.is_negative() {
                            write!(f, "(- ")?;
                        }
                        if r.is_integer() {
                            write!(f, "{}.0", r.clone().abs())?;
                        } else {
                            write!(f, "(/ {}.0 {}.0)", r.numer().clone().abs(), r.denom())?;
                        }
                        if r.is_negative() {
                            write!(f, ")")?;
                        }
                        Ok(())
                    } else {
                        write!(f, "{}", c)
                    }
                } else {
                    write!(f, "{}", c)
                }
            }
            Term::Var(name, _) => write!(f, "{}", quote_symbol(name)),
            Term::App(func, args) => p.s_expr(f, func, args),
            Term::Op(op, args) => {
                if args.is_empty() {
                    write!(f, "{}", op)
                } else {
                    p.s_expr(f, op, args)
                }
            }
            Term::Binder(binder, bindings, term) => {
                p.binder_depth += 1;
                write!(f, "({} ", binder)?;
                bindings.print(f, p)?;
                write!(f, " ")?;
                term.print(f, p)?;
                p.binder_depth -= 1;
                write!(f, ")")
            }
            Term::Let(bindings, term) => {
                write!(f, "(let ")?;
                bindings.print(f, p)?;
                write!(f, " ")?;
                p.binder_depth += 1;
                term.print(f, p)?;
                p.binder_depth -= 1;
                write!(f, ")")
            }
            Term::Match(term, cases) => {
                write!(f, "(match {} ", term)?;
                p.binder_depth += 1;
                match cases.as_slice() {
                    [head, tail @ ..] => p.s_expr(f, head, tail)?,
                    [] => write!(f, "()")?,
                }
                p.binder_depth -= 1;
                write!(f, ")")
            }
            Term::ParamOp { op, op_args, args } => {
                if !args.is_empty() {
                    write!(f, "(")?;
                }
                write!(f, "(_ {}", op)?;
                p.s_expr_tail(f, op_args)?;
                if !args.is_empty() {
                    p.s_expr_tail(f, args)?;
                }
                Ok(())
            }
            Term::AsOp(op, sort, args) => {
                if !args.is_empty() {
                    write!(f, "(")?;
                }
                write!(f, "(as {} {})", op, sort)?;
                if !args.is_empty() {
                    p.s_expr_tail(f, args)?;
                }
                Ok(())
            }
        }
    }
}

impl Print for SortedVar {
    fn print(&self, f: &mut fmt::Formatter, _: &mut Printer) -> fmt::Result {
        let (name, sort) = self;
        write!(f, "({} {})", quote_symbol(name), sort.as_ref())
    }
}

impl Print for (String, Rc<Term>) {
    fn print(&self, f: &mut fmt::Formatter, p: &mut Printer) -> fmt::Result {
        let (name, value) = self;
        write!(f, "({} ", quote_symbol(name))?;
        value.print(f, p)?;
        write!(f, ")")
    }
}

impl<T> Print for BindingList<T>
where
    (String, T): Print,
{
    fn print(&self, f: &mut fmt::Formatter, p: &mut Printer) -> fmt::Result {
        match self.as_slice() {
            [] => write!(f, "()"),
            [head, tail @ ..] => p.s_expr(f, head, tail),
        }
    }
}

impl Print for Operator {
    fn print(&self, f: &mut fmt::Formatter, _: &mut Printer) -> fmt::Result {
        write!(f, "{}", self)
    }
}

impl Print for MatchCase {
    fn print(&self, f: &mut fmt::Formatter, p: &mut Printer) -> fmt::Result {
        write!(f, "({} ", self.pattern)?;
        self.body.print(f, p)?;
        write!(f, ")")
    }
}

fn write_s_expr<H, T>(
    f: &mut fmt::Formatter,
    head: H,
    tail: impl IntoIterator<Item = T>,
) -> fmt::Result
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

fn quote_symbol(symbol: &str) -> Cow<'_, str> {
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

fn escape_string(string: &str) -> Cow<'_, str> {
    if string.contains('"') {
        Cow::Owned(string.replace('"', "\"\""))
    } else {
        Cow::Borrowed(string)
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // If the alternate flag (`#`) is passed, or the global `USE_SHARING_IN_TERM_DISPLAY` is
        // false, we disable printing with sharing
        let use_sharing = USE_SHARING_IN_TERM_DISPLAY.load(Ordering::Relaxed) && !f.alternate();
        let options = DisplayOptions::new().use_sharing(use_sharing);
        write!(f, "{}", self.display(options))
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
                // TODO: add option to control whether we use GMP notation
                if r.is_integer() && !r.is_negative() {
                    write!(f, "{}.0", r.numer())
                } else {
                    write!(f, "{}/{}", r.numer(), r.denom())
                }
            }
            Constant::String(s) => write!(f, "\"{}\"", escape_string(s)),
            Constant::RegLan(s, _) => write!(f, "(re.from_automaton \"{}\")", s),
            Constant::BitVec(val, width) => write!(f, "(_ bv{} {})", val, width), // TODO: comeback to this
        }
    }
}

impl fmt::Display for Binder {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let s = match self {
            Binder::Forall => "forall",
            Binder::Exists => "exists",
            Binder::Choice => "choice",
            Binder::Lambda => "lambda",
        };
        write!(f, "{}", s)
    }
}

impl<T: fmt::Display> fmt::Display for BindingList<T> {
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
            Sort::Function(args) => write_s_expr(f, "->", args),
            Sort::Atom(name, args) => match args.len() {
                0 => write!(f, "{}", quote_symbol(name)),
                _ => write_s_expr(f, quote_symbol(name), args),
            },
            Sort::Bool => write!(f, "Bool"),
            Sort::Int => write!(f, "Int"),
            Sort::Real => write!(f, "Real"),
            Sort::String => write!(f, "String"),
            Sort::RegLan => write!(f, "RegLan"),
            Sort::Datatype { name, args, .. } if args.is_empty() => {
                write!(f, "{}", quote_symbol(name))
            }
            Sort::Datatype { name, args, .. } => write_s_expr(f, quote_symbol(name), args),
            Sort::Var(name) => write!(f, "{}", name),
            Sort::Par(args, s) => {
                write!(f, "(par ")?;
                write_s_expr(f, &args[0], &args[1..])?;
                write!(f, " {})", s)
            }
            Sort::Array(x, y) => write_s_expr(f, "Array", [x, y]),
            Sort::BitVec(w) => write!(f, "(_ BitVec {})", w),
            Sort::ParamBitVec => write!(f, "(_ BitVec ?)"),
            Sort::Type => write!(f, "Type"),
            Sort::Set(s) => write!(f, "(Set {})", s),
            Sort::Tuple(sorts) if sorts.is_empty() => write!(f, "UnitTuple"),
            Sort::Tuple(sorts) => write_s_expr(f, "Tuple", sorts),
        }
    }
}

impl fmt::Display for MatchPattern {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            MatchPattern::Wildcard => write!(f, "_"),
            MatchPattern::Variable((var, _)) => write!(f, "{}", quote_symbol(var)),
            MatchPattern::Cons(cons, args) => write_s_expr(
                f,
                quote_symbol(cons),
                args.iter().map(|(var, _)| quote_symbol(var)),
            ),
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
            Token::Bitvector(value, width) => {
                write!(f, "#b{v:0>w$b}", v = value, w = { *width })
            }
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
            writeln!(f, "(declare-sort {} {})", quote_symbol(name), arity)?;
        }

        for (name, sort) in &self.function_declarations {
            write!(f, "(declare-fun {} ", quote_symbol(name))?;
            if let Sort::Function(sorts) = sort.as_ref() {
                write_s_expr(f, &sorts[0], &sorts[1..sorts.len() - 1])?;
                writeln!(f, " {})", sorts.last().unwrap())?;
            } else {
                writeln!(f, "() {})", sort)?;
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        ast::pool::Pool,
        parser::tests::{parse_proof, parse_terms},
    };
    use std::fmt::Write;

    fn display(definitions: &str, input: &str, options: DisplayOptions) -> String {
        let mut pool = Pool::new();
        let [term] = parse_terms(&mut pool, definitions, [input]);
        format!("{}", term.display(options))
    }

    #[test]
    fn test_sort_display() {
        let mut pool = Pool::new();
        let int = pool.add_sort(Sort::Int);
        let real = pool.add_sort(Sort::Real);
        let bool_sort = pool.add_sort(Sort::Bool);

        let cases = [
            (Sort::Bool, "Bool"),
            (Sort::Int, "Int"),
            (Sort::Real, "Real"),
            (Sort::String, "String"),
            (Sort::RegLan, "RegLan"),
            (Sort::Type, "Type"),
            (Sort::Atom("T".into(), Box::new([])), "T"),
            (
                Sort::Atom("f".into(), Box::new([int.clone(), bool_sort.clone()])),
                "(f Int Bool)",
            ),
            (
                Sort::Function(vec![int.clone(), real.clone(), bool_sort.clone()]),
                "(-> Int Real Bool)",
            ),
            (Sort::Var("?x".into()), "?x"),
            (Sort::Array(int.clone(), real.clone()), "(Array Int Real)"),
            (Sort::BitVec(4), "(_ BitVec 4)"),
            (Sort::ParamBitVec, "(_ BitVec ?)"),
            (Sort::Set(int.clone()), "(Set Int)"),
            (Sort::Tuple(vec![]), "UnitTuple"),
            (
                Sort::Tuple(vec![int.clone(), bool_sort.clone()]),
                "(Tuple Int Bool)",
            ),
            (Sort::Par(vec!["X".into()], int.clone()), "(par (X) Int)"),
            (
                Sort::Par(vec!["X".into(), "Y".into()], int.clone()),
                "(par (X Y) Int)",
            ),
            (Sort::Datatype { name: "List".into(), args: vec![] }, "List"),
            (
                Sort::Datatype {
                    name: "List".into(),
                    args: vec![int.clone()],
                },
                "(List Int)",
            ),
        ];
        for (sort, expected) in cases {
            assert_eq!(expected, format!("{}", sort), "sort: {sort:?}");
        }
    }

    #[test]
    fn test_term_display() {
        let definitions = "
            (declare-fun f (Int Int) Int)
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-const x Int)
            (declare-datatype List (par (T) ((nil) (cons (head T) (tail (List T))))))
            (declare-const l (List Int))
        ";
        let options = DisplayOptions::new();
        let cases = [
            ("42", "42"),
            ("\"foo\"", "\"foo\""),
            ("(_ bv1 4)", "(_ bv1 4)"),
            ("1.0", "1.0"),
            ("0.5", "1/2"),
            ("x", "x"),
            ("(f 1 2)", "(f 1 2)"),
            ("true", "true"),
            ("false", "false"),
            ("(and p q)", "(and p q)"),
            ("(= 1 2)", "(= 1 2)"),
            ("(forall ((x Int)) (= x 0))", "(forall ((x Int)) (= x 0))"),
            ("(exists ((x Int)) (= x 0))", "(exists ((x Int)) (= x 0))"),
            ("(choice ((x Int)) (= x 0))", "(choice ((x Int)) (= x 0))"),
            ("(lambda ((x Int)) (+ x 1))", "(lambda ((x Int)) (+ x 1))"),
            ("(let ((x 1)) (+ x 1))", "(let ((x 1)) (+ x 1))"),
            ("((_ zero_extend 2) #b100)", "((_ zero_extend 2) (_ bv4 3))"),
            (
                "((as const (Array Int Int)) 0)",
                "((as const (Array Int Int)) 0)",
            ),
            (
                "(match l (((cons h t) false) (_ true)))",
                "(match l (((cons h t) false) (_ true)))",
            ),
        ];
        for (input, expected) in cases {
            assert_eq!(
                expected,
                display(definitions, input, options.clone()),
                "term: {input}"
            );
        }
    }

    #[test]
    fn test_term_display_smt_lib_strict() {
        let mut pool = Pool::new();
        let options = DisplayOptions::new().smt_lib_strict(true);

        let neg_int = pool.add(Term::new_int(-5));
        assert_eq!("(- 5)", format!("{}", neg_int.display(options.clone())));

        let real_int = pool.add(Term::new_real(2));
        assert_eq!("2.0", format!("{}", real_int.display(options.clone())));

        let real_frac = pool.add(Term::new_real((1, 2)));
        assert_eq!(
            "(/ 1.0 2.0)",
            format!("{}", real_frac.display(options.clone()))
        );

        let neg_real = pool.add(Term::new_real((-3, 2)));
        assert_eq!("(- (/ 3.0 2.0))", format!("{}", neg_real.display(options)));
    }

    #[test]
    fn test_term_display_sharing() {
        let options = DisplayOptions::new().use_sharing(true);
        // A repeated subterm is shared.
        assert_eq!(
            "(and (! (= 1 2) :named @p_0) @p_0)",
            display("", "(and (= 1 2) (= 1 2))", options.clone())
        );
        // Subterms inside a binder are not shared.
        assert_eq!(
            "(forall ((x Int)) (= (+ x 1) (+ x 1)))",
            display(
                "",
                "(forall ((x Int)) (= (+ x 1) (+ x 1)))",
                options.clone()
            )
        );
        // A once-used term is not shared.
        assert_eq!(
            "(and (= 1 2) true)",
            display("", "(and (= 1 2) true)", options.clone())
        );
        // The sharing prefix can be customized.
        let options = options.sharing_prefix("x_".into());
        assert_eq!(
            "(and (! (= 1 2) :named x_0) x_0)",
            display("", "(and (= 1 2) (= 1 2))", options)
        );
    }

    #[test]
    fn test_proof_display() {
        let mut pool = Pool::new();
        let input = "
            (define-fun five () Int 5)
            (assume h1 (not true))
            (step t1 (cl (= (+ 1 2) 3)) :rule refl)
            (step t2 (cl) :rule resolution :premises (h1 t1))
            (anchor :step t3 :args ((x Int) (:= (y Int) 5)))
            (assume t3.h1 (= x y))
            (step t3.t2 (cl (= x y)) :rule refl)
            (step t3 (cl) :rule hole :premises (t3.t2) :discharge (t3.h1))
            (step t4 (cl) :rule hole)
        ";
        let proof = parse_proof(&mut pool, input);
        let expected = "\
            (define-fun five () Int 5)\n\
            (assume h1 (not true))\n\
            (step t1 (cl (= (+ 1 2) 3)) :rule refl)\n\
            (step t2 (cl) :rule resolution :premises (h1 t1))\n\
            (anchor :step t3 :args ((x Int) (:= (y Int) five)))\n\
            (assume t3.h1 (= x y))\n\
            (step t3.t2 (cl (= x y)) :rule refl)\n\
            (step t3 (cl) :rule hole :premises (t3.t2) :discharge (t3.h1))\n\
            (step t4 (cl) :rule hole)\n\
        ";
        assert_eq!(
            expected,
            format!("{}", proof.display(DisplayOptions::new()))
        );
    }

    #[test]
    fn test_display_asserts_clause() {
        let mut pool = Pool::new();
        let definitions = "(declare-fun p () Bool)";
        let [a, b] = parse_terms(&mut pool, definitions, ["p", "(not p)"]);

        let options = DisplayOptions::new();
        let asserts = format!(
            "{}",
            display_asserts(&[a.clone(), b.clone()], options.clone())
        );
        assert_eq!("(assert p)\n(assert (not p))\n", asserts);

        // The clause problem negates each literal and deduplicates the clause.
        let clause = format!(
            "{}",
            display_clause_smt_problem(&[a.clone(), a.clone(), b], options)
        );
        assert_eq!("(assert (not p))\n(assert (not (not p)))\n", clause);
    }

    #[test]
    fn test_sharing() {
        use crate::parser;

        let definitions = "
            (declare-const a Bool)
            (declare-const b Bool)
            (declare-const y Bool)
            (declare-const z Bool)
        ";
        let proof = "
            (step t1 (cl (and (= 1 2) (= 1 2))) :rule hole)
            (step t2 (cl (and (or a b) (not (or a b)))) :rule hole)
            (step t3 (cl (and (forall ((x Int)) (or (= x 2) (= 2 3))) (= 2 3))) :rule hole)
            (step t4 (cl (forall ((x Int)) (= (+ x 2) (+ x 2)))) :rule hole)
            (step t5 (cl (and (forall ((p Bool)) p) (forall ((p Bool)) p))) :rule hole)
            (anchor :step t6 :args ((x Int)))
            (step t6.t1 (cl (= (+ x 2) (+ x 2))) :rule hole)
            (step t6 (cl) :rule hole)
        ";
        let expected = "\
            (step t1 (cl (and (! (= 1 2) :named @p_0) @p_0)) :rule hole)\n\
            (step t2 (cl (and (! (or a b) :named @p_1) (not @p_1))) :rule hole)\n\
            (step t3 (cl (and (forall ((x Int)) (or (= x 2) (= 2 3))) (= 2 3))) :rule hole)\n\
            (step t4 (cl (forall ((x Int)) (= (+ x 2) (+ x 2)))) :rule hole)\n\
            (step t5 (cl (and (! (forall ((p Bool)) p) :named @p_2) @p_2)) :rule hole)\n\
            (anchor :step t6 :args ((x Int)))\n\
            (step t6.t1 (cl (= (! (+ x 2) :named @p_3) @p_3)) :rule hole)\n\
            (step t6 (cl) :rule hole)\n\
        ";
        let (_, proof, _, _) = parser::parse_instance(
            definitions.into(),
            proof.into(),
            None,
            parser::Config::new(),
        )
        .unwrap();

        let mut buf = String::new();
        let options = DisplayOptions::new().use_sharing(true);
        write!(buf, "{}", proof.display(options)).unwrap();
        assert_eq!(expected, buf);
    }
}
