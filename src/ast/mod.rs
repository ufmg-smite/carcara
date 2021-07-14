//! The abstract syntax tree (AST) for the veriT Proof Format.

#[macro_use]
mod macros;
mod subterms;
#[cfg(test)]
mod tests;

pub use subterms::Subterms;

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::ToPrimitive;
use std::{
    borrow::Borrow,
    collections::{HashMap, HashSet},
    fmt::Debug,
    hash::Hash,
    ops::Deref,
    rc,
    str::FromStr,
};

/// An `Rc` where equality and hashing are done by reference, instead of by value
#[derive(Clone, Eq)]
pub struct ByRefRc<T>(rc::Rc<T>);

impl<T> PartialEq for ByRefRc<T> {
    fn eq(&self, other: &Self) -> bool {
        rc::Rc::ptr_eq(&self.0, &other.0)
    }
}

impl<T> Hash for ByRefRc<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        rc::Rc::as_ptr(&self.0).hash(state)
    }
}

impl<T> Deref for ByRefRc<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.0.as_ref()
    }
}

impl<T> AsRef<T> for ByRefRc<T> {
    fn as_ref(&self) -> &T {
        self.0.as_ref()
    }
}

impl<T> Borrow<T> for ByRefRc<T> {
    fn borrow(&self) -> &T {
        self.0.as_ref()
    }
}

impl<T> From<T> for ByRefRc<T> {
    fn from(value: T) -> Self {
        ByRefRc::new(value)
    }
}

impl<T: Debug> Debug for ByRefRc<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

impl<T> ByRefRc<T> {
    pub fn new(value: T) -> Self {
        Self(rc::Rc::new(value))
    }
}

pub struct TermPool {
    pub terms: HashMap<Term, ByRefRc<Term>>,
    pub free_vars_cache: HashMap<ByRefRc<Term>, HashSet<String>>,
    bool_true: ByRefRc<Term>,
    bool_false: ByRefRc<Term>,
}

impl Default for TermPool {
    fn default() -> Self {
        Self::new()
    }
}

impl TermPool {
    pub fn new() -> Self {
        let mut terms = HashMap::new();
        let bool_sort = Self::add_term_to_map(&mut terms, Term::BOOL_SORT.clone());
        let bool_true = Self::add_term_to_map(
            &mut terms,
            Term::Terminal(Terminal::Var(
                Identifier::Simple("true".into()),
                bool_sort.clone(),
            )),
        );
        let bool_false = Self::add_term_to_map(
            &mut terms,
            Term::Terminal(Terminal::Var(Identifier::Simple("false".into()), bool_sort)),
        );
        Self {
            terms,
            free_vars_cache: HashMap::new(),
            bool_true,
            bool_false,
        }
    }

    pub fn bool_true(&self) -> ByRefRc<Term> {
        self.bool_true.clone()
    }

    pub fn bool_false(&self) -> ByRefRc<Term> {
        self.bool_false.clone()
    }

    fn add_term_to_map(terms_map: &mut HashMap<Term, ByRefRc<Term>>, term: Term) -> ByRefRc<Term> {
        use std::collections::hash_map::Entry;

        match terms_map.entry(term.clone()) {
            Entry::Occupied(occupied_entry) => occupied_entry.get().clone(),
            Entry::Vacant(vacant_entry) => vacant_entry.insert(ByRefRc::new(term)).clone(),
        }
    }

    /// Takes a term and returns a `ByRefRc` referencing it. If the term was not originally in the
    /// terms hash map, it is added to it.
    pub fn add_term(&mut self, term: Term) -> ByRefRc<Term> {
        Self::add_term_to_map(&mut self.terms, term)
    }

    // Takes a vector of terms and calls `add_term` on each.
    pub fn add_all(&mut self, terms: Vec<Term>) -> Vec<ByRefRc<Term>> {
        terms.into_iter().map(|t| self.add_term(t)).collect()
    }

    /// Takes a term and a hash map of variables to terms and substitutes every ocurrence of those
    /// variables with the associated term. This method uses the given substitutions hash map as a
    /// cache, and will therefore mutate it.
    pub fn apply_substitutions<'a>(
        &mut self,
        term: &'a ByRefRc<Term>,
        substitutions: &mut HashMap<ByRefRc<Term>, ByRefRc<Term>>,
    ) -> ByRefRc<Term> {
        macro_rules! apply_to_sequence {
            ($sequence:expr) => {
                $sequence
                    .iter()
                    .map(|a| self.apply_substitutions(a, substitutions))
                    .collect()
            };
        }

        if let Some(t) = substitutions.get(term) {
            return t.clone();
        }

        let result = match term.as_ref() {
            Term::App(func, args) => {
                let new_args = apply_to_sequence!(args);
                let new_func = self.apply_substitutions(func, substitutions);
                Term::App(new_func, new_args)
            }
            Term::Op(op, args) => {
                let new_args = apply_to_sequence!(args);
                Term::Op(*op, new_args)
            }
            Term::Quant(q, b, t) => {
                let new_term = self.apply_substitutions(t, substitutions);
                Term::Quant(*q, b.clone(), new_term)
            }
            other => other.clone(),
        };
        let result = self.add_term(result);

        // Since frequently a term will have more than one identical subterms, we insert the
        // calculated substitution in the substitutions hash map so it may be reused later. This
        // means we don't re-visit already seen terms, so this method traverses the term as a DAG,
        // not as a tree
        if *term != result {
            substitutions.insert(term.clone(), result.clone());
        }
        result
    }

    /// Returns a `HashSet` containing all the free variables in this term.
    pub fn free_vars<'t>(&mut self, term: &'t ByRefRc<Term>) -> &HashSet<String> {
        // Here, I would like to do
        // ```
        // if let Some(vars) = self.free_vars_cache.get(term) {
        //     return vars;
        // }
        // ```
        // However, because of a limitation in the borrow checker, the compiler thinks that
        // this immutable borrow of `cache` has to live until the end of the function, even
        // though the code immediately returns. This would stop me from mutating `cache` in the
        // rest of the function. Because of that, I have to check if the hash map contains
        // `term` as a key, and then get the value associated with it, meaning I have to access
        // the hash map twice, which is a bit slower. This is an example of problem case #3
        // from the non-lexical lifetimes RFC:
        // https://github.com/rust-lang/rfcs/blob/master/text/2094-nll.md
        if self.free_vars_cache.contains_key(term) {
            return self.free_vars_cache.get(term).unwrap();
        }
        let set = match term.as_ref() {
            Term::App(f, args) => {
                let mut set = args
                    .iter()
                    .fold(HashSet::new(), |acc, next| &acc | self.free_vars(next));
                set.extend(self.free_vars(f).iter().map(Clone::clone));
                set
            }
            Term::Op(_, args) => args
                .iter()
                .fold(HashSet::new(), |acc, next| &acc | self.free_vars(next)),
            Term::Quant(_, bindings, inner) | Term::Let(bindings, inner) => {
                let mut vars = self.free_vars(inner).clone();
                for (s, _) in bindings {
                    vars.remove(s.as_str());
                }
                vars
            }
            Term::Choice((bound_var, _), inner) => {
                let mut vars = self.free_vars(inner).clone();
                vars.remove(bound_var.as_str());
                vars
            }
            Term::Terminal(Terminal::Var(Identifier::Simple(var), _)) => {
                let mut set = HashSet::with_capacity(1);
                set.insert(var.clone());
                set
            }
            Term::Terminal(_) | Term::Sort(_, _) => HashSet::new(),
        };
        self.free_vars_cache.insert(term.clone(), set);
        self.free_vars_cache.get(term).unwrap()
    }
}

/// A proof in the veriT Proof Format.
#[derive(Debug)]
pub struct Proof(pub Vec<ProofCommand>);

/// A proof command.
#[derive(Debug, PartialEq)]
pub enum ProofCommand {
    /// An "assume" command, of the form "(assume <symbol> <term>)".
    Assume(ByRefRc<Term>),

    /// A "step" command.
    Step(ProofStep),

    /// A subproof.
    Subproof {
        commands: Vec<ProofCommand>,
        assignment_args: Vec<(String, ByRefRc<Term>)>,
        variable_args: Vec<SortedVar>,
    },
}

/// A "step" command, of the form `(step <symbol> <clause> :rule <symbol> [:premises (<symbol>+)]?
/// [:args <proof_args>]?)`.
#[derive(Debug, PartialEq)]
pub struct ProofStep {
    pub clause: Vec<ByRefRc<Term>>,
    pub rule: String,
    pub premises: Vec<usize>,
    pub args: Vec<ProofArg>,
}

/// An argument for a "step" or "anchor" command.
#[derive(Debug, PartialEq)]
pub enum ProofArg {
    /// An argument that is just a term.
    Term(ByRefRc<Term>),

    /// An argument of the form `(:= <symbol> <term>)`.
    Assign(String, ByRefRc<Term>),
}

/// A function definition. Functions are defined using the "function-def" command, of the form
/// `(define-fun <symbol> (<sorted_var>*) <sort> <term>)`. These definitions are substituted in
/// during parsing, so these commands don't appear in the final AST.
pub struct FunctionDef {
    pub params: Vec<SortedVar>,
    pub body: ByRefRc<Term>,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Operator {
    // Logic
    Not,
    Implies,
    And,
    Or,
    Xor,
    Equals,
    Distinct,
    Ite,

    // Arithmetic
    Add,
    Sub,
    Mult,
    Div,
    LessThan,
    GreaterThan,
    LessEq,
    GreaterEq,
}

impl_str_conversion_traits!(Operator {
    Not: "not",
    Implies: "=>",
    And: "and",
    Or: "or",
    Xor: "xor",
    Equals: "=",
    Distinct: "distinct",
    Ite: "ite",

    Add: "+",
    Sub: "-",
    Mult: "*",
    Div: "/",
    LessThan: "<",
    GreaterThan: ">",
    LessEq: "<=",
    GreaterEq: ">=",
});

pub type SortedVar = (String, ByRefRc<Term>);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SortKind {
    Function,
    Atom,
    Bool,
    Int,
    Real,
    String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Quantifier {
    Forall,
    Exists,
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Term {
    /// A terminal. This can be a constant or a variable.
    Terminal(Terminal),

    /// An application of a function to one or more terms.
    App(ByRefRc<Term>, Vec<ByRefRc<Term>>),

    /// An application of a bulit-in operator to one or more terms.
    Op(Operator, Vec<ByRefRc<Term>>),

    /// A sort.
    Sort(SortKind, Vec<ByRefRc<Term>>),

    /// A quantifier binder term.
    Quant(Quantifier, Vec<SortedVar>, ByRefRc<Term>),

    /// A "choice" term.
    Choice(SortedVar, ByRefRc<Term>),

    /// A "let" binder term.
    Let(Vec<SortedVar>, ByRefRc<Term>),
    // TODO: "match" binder terms
}

impl From<SortedVar> for Term {
    fn from(var: SortedVar) -> Self {
        Term::Terminal(Terminal::Var(Identifier::Simple(var.0), var.1))
    }
}

impl Term {
    /// The "Bool" built-in sort.
    pub const BOOL_SORT: &'static Term = &Term::Sort(SortKind::Bool, Vec::new());

    /// The "Int" built-in sort.
    pub const INT_SORT: &'static Term = &Term::Sort(SortKind::Int, Vec::new());

    /// The "Real" built-in sort.
    pub const REAL_SORT: &'static Term = &Term::Sort(SortKind::Real, Vec::new());

    /// The "String" built-in sort.
    pub const STRING_SORT: &'static Term = &Term::Sort(SortKind::String, Vec::new());

    /// Returns the sort of this term. For operations and application terms, this method assumes that
    /// the arguments' sorts have already been checked, and are correct. If `self` is a sort, this
    /// method does nothing and returns `self`.
    pub fn sort(&self) -> &Term {
        match self {
            Term::Terminal(t) => match t {
                Terminal::Integer(_) => Term::INT_SORT,
                Terminal::Real(_) => Term::REAL_SORT,
                Terminal::String(_) => Term::STRING_SORT,
                Terminal::Var(_, sort) => sort.as_ref(),
            },
            Term::Op(op, args) => match op {
                Operator::Not
                | Operator::Implies
                | Operator::And
                | Operator::Or
                | Operator::Xor
                | Operator::Equals
                | Operator::Distinct
                | Operator::LessThan
                | Operator::GreaterThan
                | Operator::LessEq
                | Operator::GreaterEq => Term::BOOL_SORT,
                Operator::Ite => args[1].sort(),
                Operator::Add | Operator::Sub | Operator::Mult | Operator::Div => args[0].sort(),
            },
            Term::App(f, _) => {
                let function_sort = f.sort();
                if let Term::Sort(SortKind::Function, sorts) = function_sort {
                    sorts.last().unwrap()
                } else {
                    unreachable!() // We assume that the function is correctly sorted
                }
            }
            sort @ Term::Sort(_, _) => sort,
            Term::Quant(_, _, _) => Term::BOOL_SORT,
            Term::Choice((_, sort), _) => sort,
            Term::Let(_, inner) => inner.sort(),
        }
    }

    /// Returns an iterator over this term and all its subterms, in topological ordering. For
    /// example, calling this method on the term (+ (f a b) 2) would return an iterator over the
    /// terms (+ (f a b) 2), (f a b), f, a, b and 2. This method traverses the term as a DAG, and
    /// the resulting iterator will not contain any duplicate terms. This ignores sort terms.
    pub fn subterms(&self) -> Subterms {
        Subterms::new(self)
    }

    /// Removes a leading negation from the term, if it exists. Same thing as `match_term!((not t)
    /// = term)`.
    pub fn remove_negation(&self) -> Option<&Self> {
        match_term!((not t) = self)
    }

    /// Removes all leading negations from the term, and returns how many there were.
    pub fn remove_all_negations(&self) -> (u32, &Term) {
        let mut term = self;
        let mut n = 0;
        while let Some(t) = term.remove_negation() {
            term = t;
            n += 1;
        }
        (n, term)
    }

    /// Removes all leading negations from the term, and returns a boolean representing the term
    /// polarity.
    pub fn remove_all_negations_with_polarity(&self) -> (bool, &Term) {
        let (n, term) = self.remove_all_negations();
        (n % 2 == 0, term)
    }

    /// Returns `true` if the term is an integer or real constant.
    pub fn is_constant(&self) -> bool {
        matches!(
            self,
            Term::Terminal(Terminal::Real(_) | Terminal::Integer(_))
        )
    }

    /// Returns `true` if the term is an integer or real constant, or one such constant negated
    /// with the "-" operator.
    pub fn is_signed_constant(&self) -> bool {
        match match_term!((-x) = self) {
            Some(x) => x.is_constant(),
            None => self.is_constant(),
        }
    }

    /// Tries to extract a `BigRational` from a term. Returns `Some` if the term is an integer or
    /// real constant.
    pub fn try_as_ratio(&self) -> Option<BigRational> {
        match self {
            Term::Terminal(Terminal::Real(r)) => Some(r.clone()),
            Term::Terminal(Terminal::Integer(i)) => Some(BigRational::from_integer(i.clone())),
            _ => None,
        }
    }

    /// Tries to extract a `BigRational` from a term, allowing negative values represented with the
    /// unary "-" operator. Returns `Some` if the term is an integer or real constant, or one such
    /// constant negated with the "-" operator.
    pub fn try_as_signed_ratio(&self) -> Option<BigRational> {
        match match_term!((-x) = self) {
            Some(x) => x.try_as_ratio().map(|r| -r),
            None => self.try_as_ratio(),
        }
    }

    /// Tries to extract the variable name from a term. Returns `Some` if the term is a variable
    /// with a simple identifier.
    pub fn try_as_var(&self) -> Option<&str> {
        match self {
            Term::Terminal(Terminal::Var(Identifier::Simple(var), _)) => Some(var.as_str()),
            _ => None,
        }
    }

    /// Tries to unwrap a quantifier term, returning the `Quantifier`, the bindings and the inner
    /// term. Returns `None` if term is not a quantifier term.
    pub fn unwrap_quant(&self) -> Option<(Quantifier, &Vec<SortedVar>, &ByRefRc<Term>)> {
        match self {
            Term::Quant(q, b, t) => Some((*q, b, t)),
            _ => None,
        }
    }

    /// Returns `true` if the term is the boolean constant "true".
    pub fn is_bool_true(&self) -> bool {
        self.sort() == Term::BOOL_SORT && self.try_as_var() == Some("true")
    }

    /// Returns `true` if the term is the boolean constant "false".
    pub fn is_bool_false(&self) -> bool {
        self.sort() == Term::BOOL_SORT && self.try_as_var() == Some("false")
    }
}

impl Debug for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Term::Terminal(t) => write!(f, "{:?}", t),
            Term::App(func, args) => {
                write!(f, "({:?}", func)?;
                for a in args {
                    write!(f, " {:?}", a)?;
                }
                write!(f, ")")
            }
            Term::Op(op, args) => {
                write!(f, "({:?}", op)?;
                for a in args {
                    write!(f, " {:?}", a)?;
                }
                write!(f, ")")
            }
            Term::Sort(sort_kind, args) => match sort_kind {
                SortKind::Atom => {
                    if let Term::Terminal(Terminal::String(s)) = args[0].as_ref() {
                        write!(f, "{}", s)
                    } else {
                        panic!()
                    }
                }
                SortKind::Bool => write!(f, "Bool"),
                SortKind::Int => write!(f, "Int"),
                SortKind::Real => write!(f, "Real"),
                SortKind::String => write!(f, "String"),
                SortKind::Function => panic!(),
            },
            Term::Quant(quantifier, bindings, term) => {
                let quantifier = match quantifier {
                    Quantifier::Forall => "forall",
                    Quantifier::Exists => "exists",
                };
                write!(f, "({} (", quantifier)?;

                for (i, (symbol, sort)) in bindings.iter().enumerate() {
                    if i != 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "({} {:?})", symbol, sort.as_ref())?;
                }
                write!(f, ") {:?})", term)
            }
            Term::Choice((symbol, sort), term) => {
                write!(f, "(choice (({} {:?})) {:?})", symbol, sort, term)
            }
            Term::Let(bindings, term) => {
                write!(f, "(let (")?;

                for (i, (symbol, value)) in bindings.iter().enumerate() {
                    if i != 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "({} {:?})", symbol, value.as_ref())?;
                }
                write!(f, ") {:?})", term)
            }
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Terminal {
    Integer(BigInt),
    Real(BigRational),
    String(String),
    Var(Identifier, ByRefRc<Term>),
}

impl Debug for Terminal {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Terminal::Integer(i) => write!(f, "{}", i),
            Terminal::Real(r) => write!(
                f,
                "{}",
                (r.numer().to_f64().unwrap() / r.denom().to_f64().unwrap())
            ),
            Terminal::String(s) => write!(f, "\"{}\"", s),
            Terminal::Var(Identifier::Simple(s), _) => write!(f, "{}", s),
            Terminal::Var(_, _) => todo!(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Identifier {
    Simple(String),
    Indexed(String, Vec<Index>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Index {
    Numeral(u64),
    Symbol(String),
}

/// A trait that implements less strict definitions of equality for terms. This trait represents
/// two definitions of equality that differ from `PartialEq`:
/// - `DeepEq::eq` implements a "deep" equality, meaning that it compares `ByRefRc`s by value,
/// instead of by reference
/// - `DeepEq::eq_modulo_reordering` is also a "deep" equality, but it considers "=" terms that are
/// "reflections" of each other as equal, meaning the terms (= a b) and (= b a) are considered
/// equal by this method
pub trait DeepEq {
    fn eq(a: &Self, b: &Self) -> bool {
        DeepEq::eq_impl(a, b, false)
    }

    fn eq_modulo_reordering(a: &Self, b: &Self) -> bool {
        DeepEq::eq_impl(a, b, true)
    }

    fn eq_impl(a: &Self, b: &Self, is_mod_reordering: bool) -> bool;
}

impl DeepEq for Term {
    fn eq_impl(a: &Self, b: &Self, is_mod_reordering: bool) -> bool {
        match (a, b) {
            (Term::App(f_a, args_a), Term::App(f_b, args_b)) => {
                DeepEq::eq_impl(f_a.as_ref(), f_b.as_ref(), is_mod_reordering)
                    && DeepEq::eq_impl(args_a, args_b, is_mod_reordering)
            }
            (Term::Op(op_a, args_a), Term::Op(op_b, args_b)) => {
                if is_mod_reordering {
                    if let (Operator::Equals, [a_1, a_2], Operator::Equals, [b_1, b_2]) =
                        (op_a, args_a.as_slice(), op_b, args_b.as_slice())
                    {
                        // If the term is an equality of two terms, we also check if they would be
                        // equal if one of them was flipped
                        return DeepEq::eq_impl(&(a_1, a_2), &(b_1, b_2), true)
                            || DeepEq::eq_impl(&(a_1, a_2), &(b_2, b_1), true);
                    }
                }
                // General case
                op_a == op_b && DeepEq::eq_impl(args_a, args_b, is_mod_reordering)
            }
            (Term::Sort(kind_a, args_a), Term::Sort(kind_b, args_b)) => {
                kind_a == kind_b && DeepEq::eq_impl(args_a, args_b, is_mod_reordering)
            }
            (Term::Terminal(a), Term::Terminal(b)) => match (a, b) {
                (Terminal::Var(iden_a, sort_a), Terminal::Var(iden_b, sort_b)) => {
                    iden_a == iden_b && DeepEq::eq_impl(sort_a, sort_b, is_mod_reordering)
                }
                (a, b) => a == b,
            },
            (Term::Quant(q_a, binds_a, a), Term::Quant(q_b, binds_b, b)) => {
                q_a == q_b
                    && DeepEq::eq_impl(binds_a, binds_b, is_mod_reordering)
                    && DeepEq::eq_impl(a, b, is_mod_reordering)
            }
            (Term::Choice(var_a, a), Term::Choice(var_b, b)) => {
                DeepEq::eq_impl(var_a, var_b, is_mod_reordering)
                    && DeepEq::eq_impl(a, b, is_mod_reordering)
            }
            (Term::Let(binds_a, a), Term::Let(binds_b, b)) => {
                DeepEq::eq_impl(binds_a, binds_b, is_mod_reordering)
                    && DeepEq::eq_impl(a, b, is_mod_reordering)
            }
            _ => false,
        }
    }
}

impl DeepEq for ProofArg {
    fn eq_impl(a: &Self, b: &Self, is_mod_reordering: bool) -> bool {
        match (a, b) {
            (ProofArg::Term(a), ProofArg::Term(b)) => DeepEq::eq_impl(a, b, is_mod_reordering),
            (ProofArg::Assign(sa, ta), ProofArg::Assign(sb, tb)) => {
                sa == sb && DeepEq::eq_impl(ta, tb, is_mod_reordering)
            }
            _ => false,
        }
    }
}

impl DeepEq for ProofCommand {
    fn eq_impl(a: &Self, b: &Self, is_mod_reordering: bool) -> bool {
        match (a, b) {
            (ProofCommand::Assume(a), ProofCommand::Assume(b)) => {
                DeepEq::eq_impl(a, b, is_mod_reordering)
            }
            (ProofCommand::Step(a), ProofCommand::Step(b)) => {
                DeepEq::eq_impl(a, b, is_mod_reordering)
            }
            _ => false,
        }
    }
}

impl DeepEq for ProofStep {
    fn eq_impl(a: &Self, b: &Self, is_mod_reordering: bool) -> bool {
        DeepEq::eq_impl(&a.clause, &b.clause, is_mod_reordering)
            && a.rule == b.rule
            && a.premises == b.premises
            && DeepEq::eq_impl(&a.args, &b.args, is_mod_reordering)
    }
}

impl<T: DeepEq> DeepEq for &T {
    fn eq_impl(a: &Self, b: &Self, is_mod_reordering: bool) -> bool {
        DeepEq::eq_impl(*a, *b, is_mod_reordering)
    }
}

impl<T: DeepEq> DeepEq for ByRefRc<T> {
    fn eq_impl(a: &Self, b: &Self, is_mod_reordering: bool) -> bool {
        a == b || DeepEq::eq_impl(a.as_ref(), b.as_ref(), is_mod_reordering)
    }
}

impl<T: DeepEq> DeepEq for Vec<T> {
    fn eq_impl(a: &Self, b: &Self, is_mod_reordering: bool) -> bool {
        a.len() == b.len()
            && a.iter()
                .zip(b.iter())
                .all(|(a, b)| DeepEq::eq_impl(a, b, is_mod_reordering))
    }
}

impl<T: DeepEq> DeepEq for (T, T) {
    fn eq_impl(a: &Self, b: &Self, is_mod_reordering: bool) -> bool {
        DeepEq::eq_impl(&a.0, &b.0, is_mod_reordering)
            && DeepEq::eq_impl(&a.1, &b.1, is_mod_reordering)
    }
}

impl DeepEq for SortedVar {
    fn eq_impl(a: &Self, b: &Self, is_mod_reordering: bool) -> bool {
        a.0 == b.0 && DeepEq::eq_impl(&a.1, &b.1, is_mod_reordering)
    }
}
