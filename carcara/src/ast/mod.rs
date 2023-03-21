//! The abstract syntax tree (AST) for the Alethe proof format.
//!
//! This module also contains various utilities for manipulating Alethe proofs and terms.

#[macro_use]
mod macros;
mod deep_eq;
mod iter;
mod pool;
pub(crate) mod printer;
mod rc;
mod substitution;
#[cfg(test)]
mod tests;

pub use deep_eq::{are_alpha_equivalent, deep_eq, tracing_deep_eq};
pub use iter::ProofIter;
pub use pool::TermPool;
pub use printer::print_proof;
pub use rc::Rc;
pub use substitution::{Substitution, SubstitutionError};

pub(crate) use deep_eq::{DeepEq, DeepEqualityChecker};

use crate::checker::error::CheckerError;
use ahash::AHashSet;
use rug::Integer;
use rug::Rational;
use std::hash::Hash;

pub use pool::SingleThreadPool;
pub use pool::TPool;

/// The prelude of an SMT-LIB problem instance.
///
/// This stores the sort declarations, function declarations and the problem's logic string.
#[derive(Debug, Clone, Default)]
pub struct ProblemPrelude {
    pub(crate) sort_declarations: Vec<(String, usize)>,
    pub(crate) function_declarations: Vec<(String, Rc<Term>)>,
    pub(crate) logic: Option<String>,
}

/// A proof in the Alethe format.
#[derive(Debug, Clone)]
pub struct Proof {
    pub premises: AHashSet<Rc<Term>>,
    pub commands: Vec<ProofCommand>,
}

impl Proof {
    /// Returns an iterator over the proof commands. See [`ProofIter`].
    pub fn iter(&self) -> ProofIter {
        ProofIter::new(&self.commands)
    }
}

/// A proof command.
#[derive(Debug, Clone, PartialEq)]
pub enum ProofCommand {
    /// An `assume` command, of the form `(assume <symbol> <term>)`.
    Assume { id: String, term: Rc<Term> },

    /// A `step` command.
    Step(ProofStep),

    /// A subproof.
    Subproof(Subproof),

    /// A closing subproof step
    Closing,
}

impl ProofCommand {
    /// Returns the unique identifier of this command.
    ///
    /// For subproofs, this is the identifier of the last step in the subproof.
    pub fn id(&self) -> &str {
        match self {
            ProofCommand::Assume { id, .. } => id,
            ProofCommand::Step(s) => &s.id,
            ProofCommand::Subproof(s) => s.commands.last().unwrap().id(),
            ProofCommand::Closing => "",
        }
    }

    /// Returns the clause of this command.
    ///
    /// For `assume` commands, this is a unit clause containing the assumed term; for steps, it's
    /// the conclusion clause; and for subproofs, it's the conclusion clause of the last step in the
    /// subproof.
    pub fn clause(&self) -> &[Rc<Term>] {
        match self {
            ProofCommand::Assume { id: _, term } => std::slice::from_ref(term),
            ProofCommand::Step(ProofStep { clause, .. }) => clause,
            ProofCommand::Subproof(s) => s.commands.last().unwrap().clause(),
            ProofCommand::Closing => &[],
        }
    }

    /// Returns `true` if the command is an `assume` command.
    pub fn is_assume(&self) -> bool {
        matches!(self, ProofCommand::Assume { .. })
    }

    /// Returns `true` if the command is a `step` command.
    pub fn is_step(&self) -> bool {
        matches!(self, ProofCommand::Step(_))
    }

    /// Returns `true` if the command is a subproof.
    pub fn is_subproof(&self) -> bool {
        matches!(self, ProofCommand::Subproof(_))
    }
}

/// A `step` command.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProofStep {
    /// The step identifier.
    pub id: String,

    /// The conclusion clause.
    pub clause: Vec<Rc<Term>>,

    /// The rule used by the step.
    pub rule: String,

    /// The premises of the step, given via the `:premises` attribute.
    ///
    /// Each premise references a command, indexed using two indices: The first indicates the depth
    /// of the subproof where the command is located, in the stack of currently open subproofs. The
    /// second is the index of the command in that subproof.
    pub premises: Vec<(usize, usize)>,

    /// The step arguments, given via the `:args` attribute.
    pub args: Vec<ProofArg>,

    /// The local premises that this step discharges, given via the `:discharge` attribute, and
    /// indexed similarly to premises.
    pub discharge: Vec<(usize, usize)>,
}

/// A subproof.
///
/// Subproofs are started by `anchor` commands, and contain a series of steps, possibly including
/// nested subproofs. A subproof must end in a `step`, which is indicated in the anchor via the
/// `:step` attribute.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct Subproof {
    pub commands: Vec<ProofCommand>,
    pub assignment_args: Vec<(String, Rc<Term>)>,
    pub variable_args: Vec<SortedVar>,
}

/// An argument for a `step` command.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProofArg {
    /// An argument that is just a term.
    Term(Rc<Term>),

    /// An argument of the form `(:= <symbol> <term>)`.
    Assign(String, Rc<Term>),
}

impl ProofArg {
    /// If this argument is a "term style" argument, extracts that term from it. Otherwise, returns
    /// an error.
    pub fn as_term(&self) -> Result<&Rc<Term>, CheckerError> {
        match self {
            ProofArg::Term(t) => Ok(t),
            ProofArg::Assign(s, t) => Err(CheckerError::ExpectedTermStyleArg(s.clone(), t.clone())),
        }
    }

    /// If this argument is an "assign style" argument, extracts the variable name and the value
    /// term from it. Otherwise, returns an error.
    pub fn as_assign(&self) -> Result<(&String, &Rc<Term>), CheckerError> {
        match self {
            ProofArg::Assign(s, t) => Ok((s, t)),
            ProofArg::Term(t) => Err(CheckerError::ExpectedAssignStyleArg(t.clone())),
        }
    }
}

/// The operator of an operation term.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Operator {
    // Logic
    /// The `not` operator.
    Not,

    /// The `=>` operator.
    Implies,

    /// The `and` operator.
    And,

    /// The `or` operator.
    Or,

    /// The `xor` operator.
    Xor,

    /// The `=` operator.
    Equals,

    /// The `distinct` operator.
    Distinct,

    /// The `ite` operator.
    Ite,

    // Arithmetic
    /// The `+` operator.
    Add,

    /// The `-` operator.
    Sub,

    /// The `*` operator.
    Mult,

    /// The `div` operator.
    IntDiv,

    /// The `/` operator.
    RealDiv,

    /// The `mod` operator.
    Mod,

    /// The `abs` operator.
    Abs,

    /// The `<` operator.
    LessThan,

    /// The `>` operator.
    GreaterThan,

    /// The `<=` operator.
    LessEq,

    /// The `>=` operator.
    GreaterEq,

    /// The `to_real` operator.
    ToReal,

    /// The `to_int` operator.
    ToInt,

    /// The `is_int` operator.
    IsInt,

    // Arrays
    /// The `select` operator.
    Select,

    /// The `store` operator.
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
    Mod: "mod",
    Abs: "abs",
    LessThan: "<",
    GreaterThan: ">",
    LessEq: "<=",
    GreaterEq: ">=",
    ToReal: "to_real",
    ToInt: "to_int",
    IsInt: "is_int",

    Select: "select",
    Store: "store",
});

/// A variable and an associated sort.
pub type SortedVar = (String, Rc<Term>);

/// The sort of a term.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Sort {
    /// A function sort.
    ///
    /// The last term indicates the return sort of the function. The remaining terms are the sorts
    /// of the parameters of the function.
    Function(Vec<Rc<Term>>),

    /// A user-declared sort, from a `declare-sort` command.
    ///
    /// The associated string is the sort name, and the associated terms are the sort arguments for
    /// this sort.
    Atom(String, Vec<Rc<Term>>),

    /// The `Bool` primitive sort.
    Bool,

    /// The `Int` primitive sort.
    Int,

    /// The `Real` primitive sort.
    Real,

    /// The `String` primitive sort.
    String,

    /// An `Array` sort.
    ///
    /// The two associated terms are the sort arguments for this sort.
    Array(Rc<Term>, Rc<Term>),
}

/// A quantifier, either `forall` or `exists`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Quantifier {
    /// The `forall` quantifier.
    Forall,

    /// The `exists` quantifier.
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

/// A list of bindings, where each binding is a variable associated with a term.
///
/// Depending on the context, it can be a "sort" binding list (like the ones present in quantifier
/// terms) where the associated term of each variable is its sort; or a "value" binding list (like
/// the ones present in `let` terms) where the associated term of each variable is its bound value.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BindingList(pub Vec<SortedVar>);

impl AsRef<[SortedVar]> for BindingList {
    fn as_ref(&self) -> &[SortedVar] {
        &self.0
    }
}

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

/// A term.
#[derive(Clone, PartialEq, Eq, Hash)]
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

    /// A `choice` term.
    Choice(SortedVar, Rc<Term>),

    /// A `let` binder term.
    Let(BindingList, Rc<Term>),

    /// A `lambda` term.
    Lambda(BindingList, Rc<Term>),
    // TODO: `match` binder terms
}

impl From<SortedVar> for Term {
    fn from(var: SortedVar) -> Self {
        Term::Terminal(Terminal::Var(Identifier::Simple(var.0), var.1))
    }
}

impl Term {
    /// Constructs a new integer term.
    pub fn integer(value: impl Into<Integer>) -> Self {
        Term::Terminal(Terminal::Integer(value.into()))
    }

    /// Constructs a new real term.
    pub fn real(value: impl Into<Rational>) -> Self {
        Term::Terminal(Terminal::Real(value.into()))
    }

    /// Constructs a new string term.
    pub fn string(value: impl Into<String>) -> Self {
        Term::Terminal(Terminal::String(value.into()))
    }

    /// Constructs a new variable term.
    pub fn var(name: impl Into<String>, sort: Rc<Term>) -> Self {
        Term::Terminal(Terminal::Var(Identifier::Simple(name.into()), sort))
    }

    /// Returns the sort of this term. This does not make use of a cache -- if possible, prefer to
    /// use `TermPool::sort`.
    pub fn raw_sort(&self) -> Sort {
        let mut pool = TermPool::new();
        let added = pool.add(self.clone());
        pool.sort(&added).clone()
    }

    /// Returns `true` if the term is a terminal.
    pub fn is_terminal(&self) -> bool {
        matches!(self, Term::Terminal(_))
    }

    /// Returns `true` if the term is an integer or real constant.
    pub fn is_number(&self) -> bool {
        matches!(
            self,
            Term::Terminal(Terminal::Real(_) | Terminal::Integer(_))
        )
    }

    /// Returns `true` if the term is an integer or real constant, or one such constant negated
    /// with the `-` operator.
    pub fn is_signed_number(&self) -> bool {
        match match_term!((-x) = self) {
            Some(x) => x.is_number(),
            None => self.is_number(),
        }
    }

    /// Tries to extract a `Rational` from a term. Returns `Some` if the term is an integer or real
    /// constant.
    pub fn as_number(&self) -> Option<Rational> {
        match self {
            Term::Terminal(Terminal::Real(r)) => Some(r.clone()),
            Term::Terminal(Terminal::Integer(i)) => Some(i.clone().into()),
            _ => None,
        }
    }

    /// Tries to extract a `Rational` from a term, allowing negative values represented with the
    /// unary `-` operator. Returns `Some` if the term is an integer or real constant, or one such
    /// constant negated with the `-` operator.
    pub fn as_signed_number(&self) -> Option<Rational> {
        match match_term!((-x) = self) {
            Some(x) => x.as_number().map(|r| -r),
            None => self.as_number(),
        }
    }

    /// Tries to extract a `Rational` from a term, allowing fractions. This method will return
    /// `Some` if the term is:
    ///
    /// - A real or integer constant
    /// - An application of the `/` or `div` operators on two real or integer constants
    /// - An application of the unary `-` operator on one of the two previous cases
    pub fn as_fraction(&self) -> Option<Rational> {
        fn as_unsigned_fraction(term: &Term) -> Option<Rational> {
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

    /// Returns `true` if the term is a variable.
    pub fn is_var(&self) -> bool {
        matches!(
            self,
            Term::Terminal(Terminal::Var(Identifier::Simple(_), _))
        )
    }

    /// Tries to extract the variable name from a term. Returns `Some` if the term is a variable
    /// with a simple identifier.
    pub fn as_var(&self) -> Option<&str> {
        match self {
            Term::Terminal(Terminal::Var(Identifier::Simple(var), _)) => Some(var.as_str()),
            _ => None,
        }
    }

    /// Returns `true` if the term is a sort.
    pub fn is_sort(&self) -> bool {
        matches!(self, Term::Sort(_))
    }

    /// Tries to extract a sort from a term. Returns `Some` if the term is a sort.
    pub fn as_sort(&self) -> Option<&Sort> {
        match self {
            Term::Sort(s) => Some(s),
            _ => None,
        }
    }

    /// Tries to unwrap an operation term, returning the `Operator` and the arguments. Returns
    /// `None` if the term is not an operation term.
    pub fn unwrap_op(&self) -> Option<(Operator, &[Rc<Term>])> {
        match self {
            Term::Op(op, args) => Some((*op, args.as_slice())),
            _ => None,
        }
    }

    /// Tries to unwrap a quantifier term, returning the `Quantifier`, the bindings and the inner
    /// term. Returns `None` if the term is not a quantifier term.
    pub fn unwrap_quant(&self) -> Option<(Quantifier, &BindingList, &Rc<Term>)> {
        match self {
            Term::Quant(q, b, t) => Some((*q, b, t)),
            _ => None,
        }
    }

    /// Tries to unwrap a `let` term, returning the bindings and the inner term. Returns `None` if
    /// the term is not a `let` term.
    pub fn unwrap_let(&self) -> Option<(&BindingList, &Rc<Term>)> {
        match self {
            Term::Let(b, t) => Some((b, t)),
            _ => None,
        }
    }

    /// Returns `true` if the term is the boolean constant `true`.
    pub fn is_bool_true(&self) -> bool {
        if let Term::Terminal(Terminal::Var(Identifier::Simple(name), sort)) = self {
            sort.as_sort() == Some(&Sort::Bool) && name == "true"
        } else {
            false
        }
    }

    /// Returns `true` if the term is the boolean constant `false`.
    pub fn is_bool_false(&self) -> bool {
        if let Term::Terminal(Terminal::Var(Identifier::Simple(name), sort)) = self {
            sort.as_sort() == Some(&Sort::Bool) && name == "false"
        } else {
            false
        }
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
    pub fn as_number_err(&self) -> Result<Rational, CheckerError> {
        self.as_number()
            .ok_or_else(|| CheckerError::ExpectedAnyNumber(self.clone()))
    }

    /// Similar to `Term::as_signed_number`, but returns a `CheckerError` on failure.
    pub fn as_signed_number_err(&self) -> Result<Rational, CheckerError> {
        self.as_signed_number()
            .ok_or_else(|| CheckerError::ExpectedAnyNumber(self.clone()))
    }

    /// Similar to `Term::as_fraction`, but returns a `CheckerError` on failure.
    pub fn as_fraction_err(&self) -> Result<Rational, CheckerError> {
        self.as_fraction()
            .ok_or_else(|| CheckerError::ExpectedAnyNumber(self.clone()))
    }

    /// Tries to unwrap an operation term, returning the `Operator` and the arguments. Returns a
    /// `CheckerError` if the term is not an operation term.
    pub fn unwrap_op_err(&self) -> Result<(Operator, &[Rc<Term>]), CheckerError> {
        self.unwrap_op()
            .ok_or_else(|| CheckerError::ExpectedOperationTerm(self.clone()))
    }

    /// Tries to unwrap a quantifier term, returning the `Quantifier`, the bindings and the inner
    /// term. Returns a `CheckerError` if the term is not a quantifier term.
    pub fn unwrap_quant_err(&self) -> Result<(Quantifier, &BindingList, &Rc<Term>), CheckerError> {
        self.unwrap_quant()
            .ok_or_else(|| CheckerError::ExpectedQuantifierTerm(self.clone()))
    }

    /// Tries to unwrap a `let` term, returning the bindings and the inner
    /// term. Returns a `CheckerError` if the term is not a `let` term.
    pub fn unwrap_let_err(&self) -> Result<(&BindingList, &Rc<Term>), CheckerError> {
        self.unwrap_let()
            .ok_or_else(|| CheckerError::ExpectedLetTerm(self.clone()))
    }
}

/// A terminal term.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Terminal {
    /// An integer constant term.
    Integer(Integer),

    /// A real constant term.
    Real(Rational),

    /// A string literal term.
    String(String),

    /// A variable, consisting of an identifier and a sort.
    Var(Identifier, Rc<Term>),
}

/// An identifier.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Identifier {
    /// A simple identifier, consisting of a symbol.
    Simple(String),

    /// An indexed identifier, consisting of a symbol and one or more indices.
    Indexed(String, Vec<IdentifierIndex>),
}

/// An index for an indexed identifier. This can be either a numeral or a symbol.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum IdentifierIndex {
    Numeral(u64),
    Symbol(String),
}
