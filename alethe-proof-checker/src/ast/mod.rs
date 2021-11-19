//! The abstract syntax tree (AST) for the Alethe Proof Format.

#[macro_use]
mod macros;
pub(crate) mod printer;
mod rc;
mod subterms;
#[cfg(test)]
mod tests;

pub use printer::print_proof;
pub use rc::Rc;
pub use subterms::Subterms;

use crate::checker::error::CheckerError;
use ahash::{AHashMap, AHashSet};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::ToPrimitive;
use std::hash::Hash;

pub struct TermPool {
    pub terms: AHashMap<Term, Rc<Term>>,
    pub free_vars_cache: AHashMap<Rc<Term>, AHashSet<String>>,
    bool_true: Rc<Term>,
    bool_false: Rc<Term>,
}

impl Default for TermPool {
    fn default() -> Self {
        Self::new()
    }
}

impl TermPool {
    pub fn new() -> Self {
        let mut terms = AHashMap::new();
        let bool_sort = Self::add_term_to_map(&mut terms, Term::Sort(Sort::Bool));
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
            free_vars_cache: AHashMap::new(),
            bool_true,
            bool_false,
        }
    }

    pub fn bool_true(&self) -> Rc<Term> {
        self.bool_true.clone()
    }

    pub fn bool_false(&self) -> Rc<Term> {
        self.bool_false.clone()
    }

    pub fn bool_constant(&self, value: bool) -> Rc<Term> {
        match value {
            true => self.bool_true(),
            false => self.bool_false(),
        }
    }

    fn add_term_to_map(terms_map: &mut AHashMap<Term, Rc<Term>>, term: Term) -> Rc<Term> {
        use std::collections::hash_map::Entry;

        match terms_map.entry(term) {
            Entry::Occupied(occupied_entry) => occupied_entry.get().clone(),
            Entry::Vacant(vacant_entry) => {
                let term = vacant_entry.key().clone();
                vacant_entry.insert(Rc::new(term)).clone()
            }
        }
    }

    /// Takes a term and returns an `Rc` referencing it. If the term was not originally in the
    /// terms hash map, it is added to it.
    pub fn add_term(&mut self, term: Term) -> Rc<Term> {
        Self::add_term_to_map(&mut self.terms, term)
    }

    /// Takes a vector of terms and calls `add_term` on each.
    pub fn add_all(&mut self, terms: Vec<Term>) -> Vec<Rc<Term>> {
        terms.into_iter().map(|t| self.add_term(t)).collect()
    }

    fn apply_substitutions_rec<'a>(
        &mut self,
        term: &'a Rc<Term>,
        substitutions: &AHashMap<Rc<Term>, Rc<Term>>,
        cache: &mut AHashMap<Rc<Term>, Rc<Term>>,
    ) -> Rc<Term> {
        macro_rules! apply_to_sequence {
            ($sequence:expr) => {
                $sequence
                    .iter()
                    .map(|a| self.apply_substitutions_rec(a, substitutions, cache))
                    .collect()
            };
        }

        if let Some(t) = cache.get(term) {
            return t.clone();
        }
        if let Some(t) = substitutions.get(term) {
            return t.clone();
        }

        let result = match term.as_ref() {
            Term::App(func, args) => {
                let new_args = apply_to_sequence!(args);
                let new_func = self.apply_substitutions_rec(func, substitutions, cache);
                self.add_term(Term::App(new_func, new_args))
            }
            Term::Op(op, args) => {
                let new_args = apply_to_sequence!(args);
                self.add_term(Term::Op(*op, new_args))
            }
            Term::Quant(q, b, t) => {
                for var in b {
                    let term = self.add_term(var.clone().into());
                    if substitutions.contains_key(&term) {
                        log::error!("trying to substitute bound variable: {}", var.0);
                        panic!();
                    }
                }
                let new_term = self.apply_substitutions_rec(t, substitutions, cache);
                self.add_term(Term::Quant(*q, b.clone(), new_term))
            }
            _ => term.clone(),
        };

        // Since frequently a term will have more than one identical subterms, we insert the
        // calculated substitution in the cache hash map so it may be reused later. This means we
        // don't re-visit already seen terms, so this method traverses the term as a DAG, not as a
        // tree
        cache.insert(term.clone(), result.clone());
        result
    }

    /// Takes a term and a hash map of variables to terms and substitutes every ocurrence of those
    /// variables with the associated term.
    pub fn apply_substitutions<'a>(
        &mut self,
        term: &'a Rc<Term>,
        substitutions: &AHashMap<Rc<Term>, Rc<Term>>,
    ) -> Rc<Term> {
        self.apply_substitutions_rec(term, substitutions, &mut AHashMap::new())
    }

    /// Returns an `AHashSet` containing all the free variables in this term.
    pub fn free_vars<'t>(&mut self, term: &'t Rc<Term>) -> &AHashSet<String> {
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
                    .fold(AHashSet::new(), |acc, next| &acc | self.free_vars(next));
                set.extend(self.free_vars(f).iter().map(Clone::clone));
                set
            }
            Term::Op(_, args) => args
                .iter()
                .fold(AHashSet::new(), |acc, next| &acc | self.free_vars(next)),
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
                let mut set = AHashSet::with_capacity(1);
                set.insert(var.clone());
                set
            }
            Term::Terminal(_) | Term::Sort(_) => AHashSet::new(),
        };
        self.free_vars_cache.insert(term.clone(), set);
        self.free_vars_cache.get(term).unwrap()
    }
}

/// A proof in the Alethe Proof Format.
#[derive(Debug)]
pub struct Proof {
    pub premises: AHashSet<Rc<Term>>,
    pub commands: Vec<ProofCommand>,
}

/// A proof command.
#[derive(Debug, PartialEq)]
pub enum ProofCommand {
    /// An "assume" command, of the form "(assume <symbol> <term>)".
    Assume { index: String, term: Rc<Term> },

    /// A "step" command.
    Step(ProofStep),

    /// A subproof.
    Subproof {
        commands: Vec<ProofCommand>,
        assignment_args: Vec<(String, Rc<Term>)>,
        variable_args: Vec<SortedVar>,
    },
}

impl ProofCommand {
    pub fn index(&self) -> &str {
        match self {
            ProofCommand::Assume { index, .. } => index,
            ProofCommand::Step(s) => &s.index,
            ProofCommand::Subproof { commands, .. } => commands.last().unwrap().index(),
        }
    }
}

/// A "step" command, of the form `(step <symbol> <clause> :rule <symbol> [:premises (<symbol>+)]?
/// [:args <proof_args>]?)`.
#[derive(Debug, PartialEq)]
pub struct ProofStep {
    pub index: String,
    pub clause: Vec<Rc<Term>>,
    pub rule: String,

    /// Premises are indexed with two indices: The first indicates the depth of the subproof (where
    /// 0 is the root proof) and the second is the index of the command in that subproof.
    pub premises: Vec<(usize, usize)>,

    pub args: Vec<ProofArg>,

    // Currently, there is an issue with the ":discharge" attribute that is used by the "subproof"
    // rule in which assumptions that should be printed as, e.g., "t1.h1", are printed as simply
    // "h1". Because of that, we currently ignore the values of this attribute for the purpose of
    // actually checking the rule. However, to be able to print it correctly, we need to parse and
    // record these values. For now, they are simply stored as strings -- eventually, they will be
    // stored using indices similarly to the ":premises" attribute
    pub discharge: Vec<String>,
}

/// An argument for a "step" or "anchor" command.
#[derive(Debug, PartialEq)]
pub enum ProofArg {
    /// An argument that is just a term.
    Term(Rc<Term>),

    /// An argument of the form `(:= <symbol> <term>)`.
    Assign(String, Rc<Term>),
}

/// A function definition. Functions are defined using the "function-def" command, of the form
/// `(define-fun <symbol> (<sorted_var>*) <sort> <term>)`. These definitions are substituted in
/// during parsing, so these commands don't appear in the final AST.
pub struct FunctionDef {
    pub params: Vec<SortedVar>,
    pub body: Rc<Term>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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
    IntDiv,
    RealDiv,
    LessThan,
    GreaterThan,
    LessEq,
    GreaterEq,

    // Arrays
    Select,
    Store,
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
    IntDiv: "div",
    RealDiv: "/",
    LessThan: "<",
    GreaterThan: ">",
    LessEq: "<=",
    GreaterEq: ">=",

    Select: "select",
    Store: "store",
});

pub type SortedVar = (String, Rc<Term>);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Sort {
    Function(Vec<Rc<Term>>),
    Atom(String, Vec<Rc<Term>>),
    Bool,
    Int,
    Real,
    String,
    Array(Rc<Term>, Rc<Term>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Quantifier {
    Forall,
    Exists,
}

impl std::ops::Not for Quantifier {
    type Output = Self;

    fn not(self) -> Self::Output {
        match self {
            Quantifier::Forall => Quantifier::Exists,
            Quantifier::Exists => Quantifier::Forall,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BindingList(pub Vec<SortedVar>);

impl<'a> IntoIterator for &'a BindingList {
    type Item = &'a SortedVar;

    type IntoIter = std::slice::Iter<'a, SortedVar>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl BindingList {
    pub const EMPTY: &'static Self = &BindingList(Vec::new());

    pub fn iter(&self) -> std::slice::Iter<SortedVar> {
        self.0.iter()
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn as_slice(&self) -> &[SortedVar] {
        self.0.as_slice()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Term {
    /// A terminal. This can be a constant or a variable.
    Terminal(Terminal),

    /// An application of a function to one or more terms.
    App(Rc<Term>, Vec<Rc<Term>>),

    /// An application of a bulit-in operator to one or more terms.
    Op(Operator, Vec<Rc<Term>>),

    /// A sort.
    Sort(Sort),

    /// A quantifier binder term.
    Quant(Quantifier, BindingList, Rc<Term>),

    /// A "choice" term.
    Choice(SortedVar, Rc<Term>),

    /// A "let" binder term.
    Let(BindingList, Rc<Term>),
    // TODO: "match" binder terms
}

impl From<SortedVar> for Term {
    fn from(var: SortedVar) -> Self {
        Term::Terminal(Terminal::Var(Identifier::Simple(var.0), var.1))
    }
}

impl Term {
    /// Returns the sort of this term. For operations and application terms, this method assumes that
    /// the arguments' sorts have already been checked, and are correct. If `self` is a sort, this
    /// method does nothing and returns `self`.
    pub fn sort(&self) -> &Sort {
        match self {
            Term::Terminal(t) => match t {
                Terminal::Integer(_) => &Sort::Int,
                Terminal::Real(_) => &Sort::Real,
                Terminal::String(_) => &Sort::String,
                Terminal::Var(_, sort) => sort.as_sort().unwrap(),
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
                | Operator::GreaterEq => &Sort::Bool,
                Operator::Ite => args[1].sort(),
                Operator::Add
                | Operator::Sub
                | Operator::Mult
                | Operator::IntDiv
                | Operator::RealDiv => args[0].sort(),
                Operator::Select => match args[0].sort() {
                    Sort::Array(_, y) => y.as_sort().unwrap(),
                    _ => unreachable!(),
                },
                Operator::Store => args[0].sort(),
            },
            Term::App(f, _) => {
                let function_sort = f.sort();
                match function_sort {
                    Sort::Function(sorts) => sorts.last().unwrap().as_sort().unwrap(),
                    _ => unreachable!(), // We assume that the function is correctly sorted
                }
            }
            Term::Sort(sort) => sort,
            Term::Quant(_, _, _) => &Sort::Bool,
            Term::Choice((_, sort), _) => sort.as_sort().unwrap(),
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

    /// Returns `true` if the term is an integer or real constant.
    pub fn is_number(&self) -> bool {
        matches!(
            self,
            Term::Terminal(Terminal::Real(_) | Terminal::Integer(_))
        )
    }

    /// Returns `true` if the term is an integer or real constant, or one such constant negated
    /// with the "-" operator.
    pub fn is_signed_number(&self) -> bool {
        match match_term!((-x) = self) {
            Some(x) => x.is_number(),
            None => self.is_number(),
        }
    }

    /// Tries to extract a `BigRational` from a term. Returns `Some` if the term is an integer or
    /// real constant.
    pub fn as_number(&self) -> Option<BigRational> {
        match self {
            Term::Terminal(Terminal::Real(r)) => Some(r.clone()),
            Term::Terminal(Terminal::Integer(i)) => Some(BigRational::from_integer(i.clone())),
            _ => None,
        }
    }

    /// Tries to extract a `BigRational` from a term, allowing negative values represented with the
    /// unary "-" operator. Returns `Some` if the term is an integer or real constant, or one such
    /// constant negated with the "-" operator.
    pub fn as_signed_number(&self) -> Option<BigRational> {
        match match_term!((-x) = self) {
            Some(x) => x.as_number().map(|r| -r),
            None => self.as_number(),
        }
    }

    /// Tries to extract a `BigRational` from a term, allowing fractions. This method will return
    /// `Some` if the term is:
    /// * A real or integer constant
    /// * An application of the "/" or "div" operators on two real or integer constants
    /// * An application of the unary "-" operator on one of the two previous cases
    pub fn as_fraction(&self) -> Option<BigRational> {
        fn as_unsigned_fraction(term: &Term) -> Option<BigRational> {
            match term {
                Term::Op(Operator::IntDiv | Operator::RealDiv, args) if args.len() == 2 => {
                    Some(args[0].as_signed_number()? / args[1].as_signed_number()?)
                }
                _ => term.as_number(),
            }
        }

        match match_term!((-x) = self) {
            Some(x) => as_unsigned_fraction(x).map(|r| -r),
            None => as_unsigned_fraction(self),
        }
    }

    /// Tries to extract the variable name from a term. Returns `Some` if the term is a variable
    /// with a simple identifier.
    pub fn as_var(&self) -> Option<&str> {
        match self {
            Term::Terminal(Terminal::Var(Identifier::Simple(var), _)) => Some(var.as_str()),
            _ => None,
        }
    }

    pub fn as_sort(&self) -> Option<&Sort> {
        match self {
            Term::Sort(s) => Some(s),
            _ => None,
        }
    }

    /// Tries to unwrap a quantifier term, returning the `Quantifier`, the bindings and the inner
    /// term. Returns `None` if term is not a quantifier term.
    pub fn unwrap_quant(&self) -> Option<(Quantifier, &BindingList, &Rc<Term>)> {
        match self {
            Term::Quant(q, b, t) => Some((*q, b, t)),
            _ => None,
        }
    }

    /// Returns `true` if the term is the boolean constant "true".
    pub fn is_bool_true(&self) -> bool {
        *self.sort() == Sort::Bool && self.as_var() == Some("true")
    }

    /// Returns `true` if the term is the boolean constant "false".
    pub fn is_bool_false(&self) -> bool {
        *self.sort() == Sort::Bool && self.as_var() == Some("false")
    }

    /// Returns `true` if the term is the given boolean constant `b`.
    pub fn is_bool_constant(&self, b: bool) -> bool {
        match b {
            true => self.is_bool_true(),
            false => self.is_bool_false(),
        }
    }
}

impl Rc<Term> {
    /// Removes a leading negation from the term, if it exists. Same thing as `match_term!((not t)
    /// = term)`.
    pub fn remove_negation(&self) -> Option<&Self> {
        match_term!((not t) = self)
    }

    /// Removes a leading negation from the term, if it exists. If it doesn't, returns a
    /// `CheckerError::TermOfWrongForm` error. Same thing as `match_term_err!((not t) = term)`.
    pub fn remove_negation_err(&self) -> Result<&Self, CheckerError> {
        match_term_err!((not t) = self)
    }
    /// Removes all leading negations from the term, and returns how many there were.
    pub fn remove_all_negations(&self) -> (u32, &Self) {
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
    pub fn remove_all_negations_with_polarity(&self) -> (bool, &Self) {
        let (n, term) = self.remove_all_negations();
        (n % 2 == 0, term)
    }

    /// Similar to `Term::as_number`, but returns a `CheckerError` on failure.
    pub fn as_number_err(&self) -> Result<BigRational, CheckerError> {
        self.as_number()
            .ok_or_else(|| CheckerError::ExpectedAnyNumber(self.clone()))
    }

    /// Similar to `Term::as_signed_number`, but returns a `CheckerError` on failure.
    pub fn as_signed_number_err(&self) -> Result<BigRational, CheckerError> {
        self.as_signed_number()
            .ok_or_else(|| CheckerError::ExpectedAnyNumber(self.clone()))
    }

    /// Similar to `Term::as_fraction`, but returns a `CheckerError` on failure.
    pub fn as_fraction_err(&self) -> Result<BigRational, CheckerError> {
        self.as_fraction()
            .ok_or_else(|| CheckerError::ExpectedAnyNumber(self.clone()))
    }

    /// Tries to unwrap a quantifier term, returning the `Quantifier`, the bindings and the inner
    /// term. Returns a `CheckerError` if term is not a quantifier term.
    pub fn unwrap_quant_err(&self) -> Result<(Quantifier, &BindingList, &Rc<Term>), CheckerError> {
        use crate::checker::error::QuantifierError;
        self.unwrap_quant()
            .ok_or_else(|| QuantifierError::ExpectedQuantifierTerm(self.clone()).into())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Terminal {
    Integer(BigInt),
    Real(BigRational),
    String(String),
    Var(Identifier, Rc<Term>),
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
/// - `DeepEq::eq` implements a "deep" equality, meaning that it compares `ast::Rc`s by value,
/// instead of by reference
/// - `DeepEq::eq_modulo_reordering` is also a "deep" equality, but it considers "=" terms that are
/// "reflections" of each other as equal, meaning the terms "(= a b)" and "(= b a)" are considered
/// equal by this method
pub trait DeepEq {
    fn eq(a: &Self, b: &Self) -> bool {
        DeepEq::eq_impl(a, b, false, &mut AHashSet::new())
    }

    fn eq_modulo_reordering(a: &Self, b: &Self) -> bool {
        DeepEq::eq_impl(a, b, true, &mut AHashSet::new())
    }

    fn eq_impl(
        a: &Self,
        b: &Self,
        is_mod_reordering: bool,
        cache: &mut AHashSet<(Rc<Term>, Rc<Term>)>,
    ) -> bool;
}

impl DeepEq for Rc<Term> {
    fn eq_impl(
        a: &Self,
        b: &Self,
        is_mod_reordering: bool,
        cache: &mut AHashSet<(Rc<Term>, Rc<Term>)>,
    ) -> bool {
        a == b || cache.contains(&(a.clone(), b.clone())) || {
            let result = DeepEq::eq_impl(a.as_ref(), b.as_ref(), is_mod_reordering, cache);
            if result {
                cache.insert((a.clone(), b.clone()));
            }
            result
        }
    }
}

impl DeepEq for Term {
    fn eq_impl(
        a: &Self,
        b: &Self,
        is_mod_reordering: bool,
        cache: &mut AHashSet<(Rc<Term>, Rc<Term>)>,
    ) -> bool {
        match (a, b) {
            (Term::App(f_a, args_a), Term::App(f_b, args_b)) => {
                DeepEq::eq_impl(f_a.as_ref(), f_b.as_ref(), is_mod_reordering, cache)
                    && DeepEq::eq_impl(args_a, args_b, is_mod_reordering, cache)
            }
            (Term::Op(op_a, args_a), Term::Op(op_b, args_b)) => {
                if is_mod_reordering {
                    if let (Operator::Equals, [a_1, a_2], Operator::Equals, [b_1, b_2]) =
                        (op_a, args_a.as_slice(), op_b, args_b.as_slice())
                    {
                        // If the term is an equality of two terms, we also check if they would be
                        // equal if one of them was flipped
                        return DeepEq::eq_impl(&(a_1, a_2), &(b_1, b_2), true, cache)
                            || DeepEq::eq_impl(&(a_1, a_2), &(b_2, b_1), true, cache);
                    }
                }
                // General case
                op_a == op_b && DeepEq::eq_impl(args_a, args_b, is_mod_reordering, cache)
            }
            (Term::Sort(a), Term::Sort(b)) => DeepEq::eq_impl(a, b, is_mod_reordering, cache),
            (Term::Terminal(a), Term::Terminal(b)) => match (a, b) {
                (Terminal::Var(iden_a, sort_a), Terminal::Var(iden_b, sort_b)) => {
                    iden_a == iden_b && DeepEq::eq_impl(sort_a, sort_b, is_mod_reordering, cache)
                }
                (a, b) => a == b,
            },
            (Term::Quant(q_a, binds_a, a), Term::Quant(q_b, binds_b, b)) => {
                q_a == q_b
                    && DeepEq::eq_impl(binds_a, binds_b, is_mod_reordering, cache)
                    && DeepEq::eq_impl(a, b, is_mod_reordering, cache)
            }
            (Term::Choice(var_a, a), Term::Choice(var_b, b)) => {
                DeepEq::eq_impl(var_a, var_b, is_mod_reordering, cache)
                    && DeepEq::eq_impl(a, b, is_mod_reordering, cache)
            }
            (Term::Let(binds_a, a), Term::Let(binds_b, b)) => {
                DeepEq::eq_impl(binds_a, binds_b, is_mod_reordering, cache)
                    && DeepEq::eq_impl(a, b, is_mod_reordering, cache)
            }
            _ => false,
        }
    }
}

impl DeepEq for Sort {
    fn eq_impl(
        a: &Self,
        b: &Self,
        is_mod_reordering: bool,
        cache: &mut AHashSet<(Rc<Term>, Rc<Term>)>,
    ) -> bool {
        match (a, b) {
            (Sort::Function(sorts_a), Sort::Function(sorts_b)) => {
                DeepEq::eq_impl(sorts_a, sorts_b, is_mod_reordering, cache)
            }
            (Sort::Atom(a, sorts_a), Sort::Atom(b, sorts_b)) => {
                a == b && DeepEq::eq_impl(sorts_a, sorts_b, is_mod_reordering, cache)
            }
            (Sort::Bool, Sort::Bool)
            | (Sort::Int, Sort::Int)
            | (Sort::Real, Sort::Real)
            | (Sort::String, Sort::String) => true,
            (Sort::Array(x_a, y_a), Sort::Array(x_b, y_b)) => {
                DeepEq::eq_impl(x_a, x_b, is_mod_reordering, cache)
                    && DeepEq::eq_impl(y_a, y_b, is_mod_reordering, cache)
            }
            _ => false,
        }
    }
}

impl DeepEq for BindingList {
    fn eq_impl(
        a: &Self,
        b: &Self,
        is_mod_reordering: bool,
        cache: &mut AHashSet<(Rc<Term>, Rc<Term>)>,
    ) -> bool {
        DeepEq::eq_impl(&a.0, &b.0, is_mod_reordering, cache)
    }
}

impl DeepEq for ProofArg {
    fn eq_impl(
        a: &Self,
        b: &Self,
        is_mod_reordering: bool,
        cache: &mut AHashSet<(Rc<Term>, Rc<Term>)>,
    ) -> bool {
        match (a, b) {
            (ProofArg::Term(a), ProofArg::Term(b)) => {
                DeepEq::eq_impl(a, b, is_mod_reordering, cache)
            }
            (ProofArg::Assign(sa, ta), ProofArg::Assign(sb, tb)) => {
                sa == sb && DeepEq::eq_impl(ta, tb, is_mod_reordering, cache)
            }
            _ => false,
        }
    }
}

impl DeepEq for ProofCommand {
    fn eq_impl(
        a: &Self,
        b: &Self,
        is_mod_reordering: bool,
        cache: &mut AHashSet<(Rc<Term>, Rc<Term>)>,
    ) -> bool {
        match (a, b) {
            (
                ProofCommand::Assume { index: a_index, term: a_term },
                ProofCommand::Assume { index: b_index, term: b_term },
            ) => a_index == b_index && DeepEq::eq_impl(a_term, b_term, is_mod_reordering, cache),
            (ProofCommand::Step(a), ProofCommand::Step(b)) => {
                DeepEq::eq_impl(a, b, is_mod_reordering, cache)
            }
            _ => false,
        }
    }
}

impl DeepEq for ProofStep {
    fn eq_impl(
        a: &Self,
        b: &Self,
        is_mod_reordering: bool,
        cache: &mut AHashSet<(Rc<Term>, Rc<Term>)>,
    ) -> bool {
        DeepEq::eq_impl(&a.clause, &b.clause, is_mod_reordering, cache)
            && a.rule == b.rule
            && a.premises == b.premises
            && DeepEq::eq_impl(&a.args, &b.args, is_mod_reordering, cache)
    }
}

impl<T: DeepEq> DeepEq for &T {
    fn eq_impl(
        a: &Self,
        b: &Self,
        is_mod_reordering: bool,
        cache: &mut AHashSet<(Rc<Term>, Rc<Term>)>,
    ) -> bool {
        DeepEq::eq_impl(*a, *b, is_mod_reordering, cache)
    }
}

impl<T: DeepEq> DeepEq for Vec<T> {
    fn eq_impl(
        a: &Self,
        b: &Self,
        is_mod_reordering: bool,
        cache: &mut AHashSet<(Rc<Term>, Rc<Term>)>,
    ) -> bool {
        a.len() == b.len()
            && a.iter()
                .zip(b.iter())
                .all(|(a, b)| DeepEq::eq_impl(a, b, is_mod_reordering, cache))
    }
}

impl<T: DeepEq> DeepEq for (T, T) {
    fn eq_impl(
        a: &Self,
        b: &Self,
        is_mod_reordering: bool,
        cache: &mut AHashSet<(Rc<Term>, Rc<Term>)>,
    ) -> bool {
        DeepEq::eq_impl(&a.0, &b.0, is_mod_reordering, cache)
            && DeepEq::eq_impl(&a.1, &b.1, is_mod_reordering, cache)
    }
}

impl DeepEq for SortedVar {
    fn eq_impl(
        a: &Self,
        b: &Self,
        is_mod_reordering: bool,
        cache: &mut AHashSet<(Rc<Term>, Rc<Term>)>,
    ) -> bool {
        a.0 == b.0 && DeepEq::eq_impl(&a.1, &b.1, is_mod_reordering, cache)
    }
}
