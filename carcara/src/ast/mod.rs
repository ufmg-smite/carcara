//! The abstract syntax tree (AST) for the Alethe proof format.
//!
//! This module also contains various utilities for manipulating Alethe proofs and terms.

#[macro_use]
mod macros;
mod context;
mod iter;
mod polyeq;
pub mod pool;
pub(crate) mod printer;
mod rc;
mod substitution;
#[cfg(test)]
mod tests;

pub use context::{Context, ContextStack};
pub use iter::ProofIter;
pub use polyeq::{alpha_equiv, polyeq, tracing_polyeq};
pub use pool::{PrimitivePool, TermPool};
pub use printer::print_proof;
pub use rc::Rc;
pub use substitution::{Substitution, SubstitutionError};

pub(crate) use polyeq::{Polyeq, PolyeqComparator};

use crate::checker::error::CheckerError;
use indexmap::IndexSet;
use rug::Integer;
use rug::Rational;
use std::{hash::Hash, ops::Deref};

/// The prelude of an SMT-LIB problem instance.
///
/// This stores the sort declarations, function declarations and the problem's logic string.
#[derive(Debug, Clone, Default)]
pub struct ProblemPrelude {
    /// The sort declarations, each represented by its name and arity.
    pub(crate) sort_declarations: Vec<(String, usize)>,

    /// The function declarations, each represented by its name and body.
    pub(crate) function_declarations: Vec<(String, Rc<Term>)>,

    /// The problem's logic string, if it exists.
    pub(crate) logic: Option<String>,
}

/// A proof in the Alethe format.
#[derive(Debug, Clone)]
pub struct Proof {
    /// The proof's premises.
    ///
    /// Those are the terms introduced in the original problem's `assert` commands.
    pub premises: IndexSet<Rc<Term>>,

    /// The proof commands.
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
    /// An `assume` command.
    Assume { id: String, term: Rc<Term> },

    /// A `step` command.
    Step(ProofStep),

    /// A subproof.
    Subproof(Subproof),
}

impl ProofCommand {
    /// Returns the unique id of this command.
    ///
    /// For subproofs, this is the id of the last step in the subproof.
    pub fn id(&self) -> &str {
        match self {
            ProofCommand::Assume { id, .. } => id,
            ProofCommand::Step(s) => &s.id,
            ProofCommand::Subproof(s) => s.commands.last().unwrap().id(),
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
    /// The step id.
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
    /// The proof commands inside the subproof.
    pub commands: Vec<ProofCommand>,

    /// The "assignment" style arguments of the subproof, of the form `(:= <symbol> <term>)`.
    pub assignment_args: Vec<(String, Rc<Term>)>,

    /// The "variable" style arguments of the subproof, of the form `(<symbol> <sort>)`.
    pub variable_args: Vec<SortedVar>,

    /// Subproof id used for context hashing purpose
    pub context_id: usize,
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

    // Strings
    /// The `str.++` operator.
    StrConcat,

    /// The `str.len` operator.
    StrLen,

    /// The `str.<` operator.
    StrLessThan,

    /// The `str.<=` operator.
    StrLessEq,

    /// The `str.at` operator.
    CharAt,

    /// The `str.substr` operator.
    Substring,

    /// The `str.prefixof` operator.
    PrefixOf,

    /// The `str.suffixof` operator.
    SuffixOf,

    /// The `str.contains` operator.
    Contains,

    /// The `str.indexof` operator.
    IndexOf,

    /// The `str.replace` operator.
    Replace,

    /// The `str.replace_all` operator.
    ReplaceAll,

    /// The `str.replace_re` operator.
    ReplaceRe,

    /// The `str.replace_re_all` operator.
    ReplaceReAll,

    /// The `str.is_digit` operator.
    StrIsDigit,

    /// The `str.to_code` operator.
    StrToCode,

    /// The `str.from_code` operator.
    StrFromCode,

    /// The `str.to_int` operator.
    StrToInt,

    /// The `str.from_int` operator.
    StrFromInt,

    // Regular Expressions
    /// The `str.to_re` operator.
    StrToRe,

    /// The `str.in_re` operator.
    StrInRe,

    /// The `re.none` operator.
    ReNone,

    /// The `re.all` operator.
    ReAll,

    /// The `re.allchar` operator.
    ReAllChar,

    /// The `re.++` operator.
    ReConcat,

    /// The `re.union` operator.
    ReUnion,

    /// The `re.inter` operator.
    ReIntersection,

    /// The `re.*` operator.
    ReKleeneClosure,

    /// The `re.comp` operator.
    ReComplement,

    /// The `re.diff` operator.
    ReDiff,

    /// The `re.+` operator.
    ReKleeneCross,

    /// The `re.opt` operator.
    ReOption,

    /// The `re.range` operator.
    ReRange,

    // BV operators (unary)
    BvNot,
    BvNeg,
    // BV operators (binary, left-assoc)
    BvAnd,
    BvOr,
    BvAdd,
    BvMul,
    // BV operators (binary)
    BvUDiv,
    BvURem,
    BvShl,
    BvLShr,
    BvULt,

    BvConcat,
    BvNAnd,
    BvNOr,
    BvXor,
    BvXNor,
    BvComp,
    BvSub,
    BvSDiv,
    BvSRem,
    BvSMod,
    BvAShr,

    BvULe,
    BvUGt,
    BvUGe,
    BvSLt,
    BvSLe,
    BvSGt,
    BvSGe,
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

    StrConcat: "str.++",
    StrLen: "str.len",
    StrLessThan: "str.<",
    StrLessEq: "str.<=",
    CharAt: "str.at",
    Substring: "str.substr",
    PrefixOf: "str.prefixof",
    SuffixOf: "str.suffixof",
    Contains: "str.contains",
    IndexOf: "str.indexof",
    Replace: "str.replace",
    ReplaceAll: "str.replace_all",
    ReplaceRe: "str.replace_re",
    ReplaceReAll: "str.replace_re_all",
    StrIsDigit: "str.is_digit",
    StrToCode: "str.to_code",
    StrFromCode: "str.from_code",
    StrToInt: "str.to_int",
    StrFromInt: "str.from_int",

    StrToRe: "str.to_re",
    StrInRe: "str.in_re",
    ReNone: "re.none",
    ReAll: "re.all",
    ReAllChar: "re.allchar",
    ReConcat: "re.++",
    ReUnion: "re.union",
    ReIntersection: "re.inter",
    ReKleeneClosure: "re.*",
    ReComplement: "re.comp",
    ReDiff: "re.diff",
    ReKleeneCross: "re.+",
    ReOption: "re.opt",
    ReRange: "re.range",
    BvNot: "bvnot",
    BvNeg: "bvneg",
    BvAnd: "bvand",
    BvOr: "bvor",
    BvAdd: "bvadd",
    BvMul: "bvmul",
    BvUDiv: "bvudiv",
    BvURem: "bvurem",
    BvShl: "bvshl",
    BvLShr: "bvlshr",
    BvULt: "bvult",

    BvConcat: "concat",
    BvNAnd: "bvnand",
    BvNOr: "bvnor",
    BvXor: "bvxor",
    BvXNor: "bvxnor",
    BvComp: "bvcomp",
    BvSub: "bvsub",
    BvSDiv: "bvsdiv",
    BvSRem: "bvsrem",
    BvSMod: "bvsmod",
    BvAShr: "bvashr",

    BvULe: "bvule",
    BvUGt: "bvugt",
    BvUGe: "bvuge",
    BvSLt: "bvslt",
    BvSLe: "bvsle",
    BvSGt: "bvsgt",
    BvSGe: "bvsge",
    // ! watch out bv extract
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

    /// The `RegLan` primitive sort.
    RegLan,

    /// An `Array` sort.
    ///
    /// The two associated terms are the sort arguments for this sort.
    Array(Rc<Term>, Rc<Term>),
    ///  `BitVec` sort.
    ///
    /// The associated term is the BV width of this sort.
    BitVec(Integer),
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

impl Deref for BindingList {
    type Target = Vec<SortedVar>;

    fn deref(&self) -> &Self::Target {
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
}

/// A term.
///
/// Many additional methods are implemented in [`Rc<Term>`].
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Term {
    /// A constant term.
    Const(Constant),

    /// A variable, consisting of an identifier and a sort.
    Var(String, Rc<Term>),

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
}

impl From<SortedVar> for Term {
    fn from(var: SortedVar) -> Self {
        Term::Var(var.0, var.1)
    }
}

impl Term {
    /// Constructs a new integer term.
    pub fn new_int(value: impl Into<Integer>) -> Self {
        Term::Const(Constant::Integer(value.into()))
    }

    /// Constructs a new real term.
    pub fn new_real(value: impl Into<Rational>) -> Self {
        Term::Const(Constant::Real(value.into()))
    }

    /// Constructs a new string term.
    pub fn new_string(value: impl Into<String>) -> Self {
        Term::Const(Constant::String(value.into()))
    }

    /// Constructs a new bv term.
    pub fn new_bv(value: impl Into<Integer>, widht: impl Into<Integer>) -> Self {
        Term::Const(Constant::BitVec(value.into(), widht.into()))
    }

    /// Constructs a new variable term.
    pub fn new_var(name: impl Into<String>, sort: Rc<Term>) -> Self {
        Term::Var(name.into(), sort)
    }

    /// Returns the sort of this term. This does not make use of a cache --- if possible, prefer to
    /// use `TermPool::sort`.
    pub fn raw_sort(&self) -> Sort {
        let mut pool = PrimitivePool::new();
        let added = pool.add(self.clone());
        pool.sort(&added).as_sort().unwrap().clone()
    }

    /// Returns `true` if the term is a terminal, that is, if it is a constant or a variable.
    pub fn is_terminal(&self) -> bool {
        matches!(self, Term::Const(_) | Term::Var(..))
    }

    /// Returns `true` if the term is an integer or real constant.
    pub fn is_number(&self) -> bool {
        matches!(self, Term::Const(Constant::Real(_) | Constant::Integer(_)))
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
            Term::Const(Constant::Real(r)) => Some(r.clone()),
            Term::Const(Constant::Integer(i)) => Some(i.clone().into()),
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
        matches!(self, Term::Var(_, _))
    }

    /// Tries to extract the variable name from a term. Returns `Some` if the term is a variable.
    pub fn as_var(&self) -> Option<&str> {
        match self {
            Term::Var(var, _) => Some(var.as_str()),
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
    pub fn as_op(&self) -> Option<(Operator, &[Rc<Term>])> {
        match self {
            Term::Op(op, args) => Some((*op, args.as_slice())),
            _ => None,
        }
    }

    /// Tries to unwrap a quantifier term, returning the `Quantifier`, the bindings and the inner
    /// term. Returns `None` if the term is not a quantifier term.
    pub fn as_quant(&self) -> Option<(Quantifier, &BindingList, &Rc<Term>)> {
        match self {
            Term::Quant(q, b, t) => Some((*q, b, t)),
            _ => None,
        }
    }

    /// Tries to unwrap a `let` term, returning the bindings and the inner term. Returns `None` if
    /// the term is not a `let` term.
    pub fn as_let(&self) -> Option<(&BindingList, &Rc<Term>)> {
        match self {
            Term::Let(b, t) => Some((b, t)),
            _ => None,
        }
    }

    /// Returns `true` if the term is the boolean constant `true`.
    pub fn is_bool_true(&self) -> bool {
        if let Term::Var(name, sort) = self {
            sort.as_sort() == Some(&Sort::Bool) && name == "true"
        } else {
            false
        }
    }

    /// Returns `true` if the term is the boolean constant `false`.
    pub fn is_bool_false(&self) -> bool {
        if let Term::Var(name, sort) = self {
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
    pub fn as_op_err(&self) -> Result<(Operator, &[Rc<Term>]), CheckerError> {
        self.as_op()
            .ok_or_else(|| CheckerError::ExpectedOperationTerm(self.clone()))
    }

    /// Tries to unwrap a quantifier term, returning the `Quantifier`, the bindings and the inner
    /// term. Returns a `CheckerError` if the term is not a quantifier term.
    pub fn as_quant_err(&self) -> Result<(Quantifier, &BindingList, &Rc<Term>), CheckerError> {
        self.as_quant()
            .ok_or_else(|| CheckerError::ExpectedQuantifierTerm(self.clone()))
    }

    /// Tries to unwrap a `let` term, returning the bindings and the inner
    /// term. Returns a `CheckerError` if the term is not a `let` term.
    pub fn as_let_err(&self) -> Result<(&BindingList, &Rc<Term>), CheckerError> {
        self.as_let()
            .ok_or_else(|| CheckerError::ExpectedLetTerm(self.clone()))
    }
}

/// A constant term.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Constant {
    /// An integer constant term.
    Integer(Integer),

    /// A real constant term.
    Real(Rational),

    /// A string literal term.
    String(String),

    BitVec(Integer, Integer),
}
