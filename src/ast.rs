//! The abstract syntax tree (AST) for the veriT Proof Format.

use num_rational::Ratio;
use std::{fmt::Debug, hash::Hash, ops::Deref, rc, str::FromStr};

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

/// A proof in the veriT Proof Format.
#[derive(Debug)]
pub struct Proof(pub Vec<ProofCommand>);

/// A proof command.
#[derive(Debug, PartialEq)]
pub enum ProofCommand {
    /// An "assume" command, of the form "(assume <symbol> <term>)".
    Assume(ByRefRc<Term>),

    /// A "step" command, of the form "(step <symbol> <clause> :rule <symbol> [:premises
    /// (<symbol>+)]? [:args <proof_args>]?)".
    Step {
        clause: Vec<ByRefRc<Term>>,
        rule: String,
        premises: Vec<usize>,
        args: Vec<ProofArg>,
    },
}

/// An argument for a "step" or "anchor" command.
#[derive(Debug, PartialEq)]
pub enum ProofArg {
    /// An argument that is just a term.
    Term(ByRefRc<Term>),

    /// An argument of the form "(:= <symbol> <term>)".
    Assign(String, ByRefRc<Term>),
}

/// A function definition. Functions are defined using the "function-def" command, of the form
/// "(define-fun <symbol> (<sorted_var>*) <sort> <term>)". These definitions are substituted in
/// during parsing, so these commands don't appear in the final AST.
pub struct FunctionDef {
    pub params: Vec<(String, ByRefRc<Term>)>,
    pub body: Term,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Operator {
    // Arithmetic
    Add,
    Sub,
    Mult,
    Div,

    // Logic
    Eq,
    Or,
    And,
    Not,
    Distinct,

    Ite,
}

/// Implements `FromStr` and `Debug` for `Operator`.
macro_rules! impl_operator_str_traits {
    ($($op:ident: $s:literal),* $(,)?) => {
        impl FromStr for Operator {
            type Err = ();

            fn from_str(s: &str) -> Result<Self, Self::Err> {
                match s {
                    $($s => Ok(Operator::$op),)*
                    _ => Err(()),
                }
            }
        }

        impl Debug for Operator {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                let s = match self {
                    $(Operator::$op => $s,)*
                };
                write!(f, "{}", s)
            }
        }
    }
}

impl_operator_str_traits! {
    Add: "+",
    Sub: "-",
    Mult: "*",
    Div: "/",
    Eq: "=",
    Or: "or",
    And: "and",
    Not: "not",
    Distinct: "distinct",
    Ite: "ite",
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SortKind {
    Function,
    Atom,
    Bool,
    Int,
    Real,
    String,
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
    // TODO: binders
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
                Operator::Add | Operator::Sub | Operator::Mult | Operator::Div => args[0].sort(),
                Operator::Eq
                | Operator::Or
                | Operator::And
                | Operator::Not
                | Operator::Distinct => Term::BOOL_SORT,
                Operator::Ite => args[1].sort(),
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
        }
    }

    /// Returns an iterator over this term and all its subterms. For example, calling this method
    /// on the term (+ (f a b) 2) would return an iterator over the terms (+ (f a b) 2), (f a b),
    /// f, a, b and 2.
    pub fn subterms(&self) -> Box<dyn Iterator<Item = &Self> + '_> {
        use std::iter;
        let iter = iter::once(self);
        match self {
            Self::Terminal(_) => Box::new(iter),
            Self::App(f, args) => Box::new(
                iter.chain(iter::once(f.as_ref()))
                    .chain(args.iter().flat_map(|t| t.as_ref().subterms())),
            ),
            Self::Op(_, args) | Self::Sort(_, args) => {
                Box::new(iter.chain(args.iter().flat_map(|t| t.as_ref().subterms())))
            }
        }
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
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Terminal {
    Integer(u64),
    Real(Ratio<u64>),
    String(String),
    Var(Identifier, ByRefRc<Term>),
}

impl Debug for Terminal {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Terminal::Integer(i) => write!(f, "{}", i),
            Terminal::Real(r) => write!(f, "{}", (*r.numer() as f64 / *r.denom() as f64)),
            Terminal::String(s) => write!(f, "\"{}\"", s),
            Terminal::Var(Identifier::Simple(s), _) => write!(f, "{}", s),
            _ => todo!(),
        }
    }
}

/// Helper macro to construct `Terminal` terms.
macro_rules! terminal {
    (int $e:expr) => {
        Term::Terminal(Terminal::Integer($e))
    };
    (real $num:literal / $denom:literal) => {
        Term::Terminal(Terminal::Real(num_rational::Ratio::new($num, $denom)))
    };
    (real $e:expr) => {
        Term::Terminal(Terminal::Real($e))
    };
    (string $e:expr) => {
        Term::Terminal(Terminal::String($e.into()))
    };
    (var $e:expr ; $sort:expr) => {
        Term::Terminal(Terminal::Var(Identifier::Simple($e.into()), $sort))
    };
    (bool true) => {
        terminal!(var "true"; ByRefRc::new(Term::BOOL_SORT.clone()))
    };
    (bool false) => {
        terminal!(var "false"; ByRefRc::new(Term::BOOL_SORT.clone()))
    };
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
