//! The abstract syntax tree (AST) for the veriT Proof Format.

use num_rational::Ratio;
use std::{collections::HashSet, fmt::Debug, hash::Hash, ops::Deref, rc, str::FromStr};

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
    Implies,

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
    Implies: "=>",
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
                | Operator::Distinct
                | Operator::Implies => Term::BOOL_SORT,
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

    /// Returns a `Vec` with this term and all its subterms, in topological ordering. For example,
    /// calling this method on the term (+ (f a b) 2) would return a `Vec` with the terms (+ (f a
    /// b) 2), (f a b), f, a, b and 2. This method traverses the term as DAG, and the resulting
    /// `Vec` will not contain any duplicate terms. This method ignores sort terms.
    pub fn subterms(&self) -> Vec<&Term> {
        let mut result = Vec::new();
        let mut visited = HashSet::new();

        fn visit<'a>(term: &'a Term, r: &mut Vec<&'a Term>, visited: &mut HashSet<&'a Term>) {
            let is_new = visited.insert(term);
            if !is_new {
                return;
            }
            r.push(term);

            match term {
                Term::App(f, args) => {
                    visit(f, r, visited);
                    for a in args.iter() {
                        visit(a, r, visited);
                    }
                }
                Term::Op(_, args) => {
                    for a in args.iter() {
                        visit(a, r, visited);
                    }
                }
                _ => (),
            }
        }

        visit(self, &mut result, &mut visited);
        result
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

/// A macro to help deconstruct operation terms. Since a term holds references to other terms in
/// `Vec`s and `Rc`s, pattern matching a complex term can be difficult and verbose. This macro
/// helps with that.
macro_rules! match_term {
    ($bind:ident = $var:expr) => {
        Some($var)
    };
    (($op:tt $($args:tt)+) = $var:expr) => {{
        let _: &Term = $var;
        if let Term::Op(match_term!(@GET_VARIANT $op), args) = $var {
            match_term!(@ARGS ($($args)+) = args.as_slice())
        } else {
            None
        }
    }};
    (@ARGS ($arg:tt) = $var:expr) => {
        match_term!(@ARGS_IDENT (arg1: $arg) = $var)
    };
    (@ARGS ($arg1:tt $arg2:tt) = $var:expr) => {
        match_term!(@ARGS_IDENT (arg1: $arg1, arg2: $arg2) = $var)
    };
    (@ARGS ($arg1:tt $arg2:tt $arg3:tt) = $var:expr) => {
        match_term!(@ARGS_IDENT (arg1: $arg1, arg2: $arg2, arg3: $arg3) = $var)
    };
    (@ARGS_IDENT ( $($name:ident : $arg:tt),* ) = $var:expr) => {
        if let [$($name),*] = $var {
            #[allow(unused_parens)]
            match ($(match_term!($arg = $name.as_ref())),*) {
                ($(Some($name)),*) => Some(($($name),*)),
                _ => None,
            }
        } else {
            None
        }

    };
    (@GET_VARIANT not) => { Operator::Not };
    (@GET_VARIANT =) => { Operator::Eq };
    (@GET_VARIANT ite) => { Operator::Ite };
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::tests::{parse_term, parse_term_with_definitions, EqByValue};

    #[test]
    fn test_match_term() {
        let term = parse_term("(= (= (not false) (= true false)) (not true))");
        let ((a, (b, c)), d) = match_term!((= (= (not a) (= b c)) (not d)) = &term).unwrap();
        EqByValue::eq(a, &terminal!(bool false));
        EqByValue::eq(b, &terminal!(bool true));
        EqByValue::eq(c, &terminal!(bool false));
        EqByValue::eq(d, &terminal!(bool true));

        let term = parse_term("(ite (not true) (- 2 2) (* 1 5))");
        let (a, b, c) = match_term!((ite (not a) b c) = &term).unwrap();
        EqByValue::eq(a, &terminal!(bool true));
        EqByValue::eq(
            b,
            &Term::Op(
                Operator::Sub,
                vec![
                    ByRefRc::new(terminal!(int 2)),
                    ByRefRc::new(terminal!(int 2)),
                ],
            ),
        );
        EqByValue::eq(
            c,
            &Term::Op(
                Operator::Mult,
                vec![
                    ByRefRc::new(terminal!(int 1)),
                    ByRefRc::new(terminal!(int 5)),
                ],
            ),
        );
    }

    #[test]
    fn test_subterms_no_duplicates() {
        fn run_tests(cases: &[&str]) {
            fn no_duplicates(slice: &[&Term]) -> bool {
                let mut seen = HashSet::new();
                slice.iter().all(|&t| seen.insert(t))
            }
            for s in cases {
                let term = parse_term(s);
                assert!(no_duplicates(&term.subterms()))
            }
        }
        run_tests(&[
            "(= 1 1)",
            "(ite false false false)",
            "(- (ite (not true) 2 3) (ite (not true) 2 3))",
            "(= (= 1 2) (not (= 1 2)))",
            "(+ (* 1 2) (- 2 (* 1 2)))",
        ]);
    }

    #[test]
    fn test_subterms() {
        fn run_tests(definitions: &str, cases: &[&[&str]]) {
            for c in cases {
                let expected = c.iter().cloned();

                let root = parse_term_with_definitions(definitions, c[0]);
                let subterms = root.subterms();
                let as_strings: Vec<_> = subterms.iter().map(|&t| format!("{:?}", t)).collect();
                let got = as_strings.iter().map(String::as_str);

                assert!(expected.eq(got))
            }
        }
        run_tests(
            "(declare-fun f (Int Int) Int)
            (declare-fun a () Int)
            (declare-fun b () Int)
            (declare-fun c () Int)",
            &[
                &["(= 0 1)", "0", "1"],
                &["(f a b)", "f", "a", "b"],
                &[
                    "(f (f a b) (f b c))",
                    "f",
                    "(f a b)",
                    "a",
                    "b",
                    "(f b c)",
                    "c",
                ],
                &[
                    "(= (= 1 2) (not (= 1 2)))",
                    "(= 1 2)",
                    "1",
                    "2",
                    "(not (= 1 2))",
                ],
                &[
                    "(ite (not false) (+ 2 (f 0 1)) (- (f a b) (f 0 1)))",
                    "(not false)",
                    "false",
                    "(+ 2 (f 0 1))",
                    "2",
                    "(f 0 1)",
                    "f",
                    "0",
                    "1",
                    "(- (f a b) (f 0 1))",
                    "(f a b)",
                    "a",
                    "b",
                ],
            ],
        )
    }
}
