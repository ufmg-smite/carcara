//! The abstract syntax tree (AST) for the veriT Proof Format.

use num_rational::Ratio;
use std::rc::Rc;
use std::str::FromStr;

/// A proof in the veriT Proof Format.
#[derive(Debug)]
pub struct Proof(pub Vec<ProofCommand>);

/// A proof command.
#[derive(Debug)]
pub enum ProofCommand {
    /// An "assume" command, of the form "(assume <symbol> <term>)".
    Assume(String, Rc<Term>),

    /// A "step" command, of the form "(step <symbol> <clause> :rule <symbol> [:premises
    /// (<symbol>+)]? [:args <proof_args>]?)".
    Step {
        step_name: String,
        clause: Vec<Rc<Term>>,
        rule: String,
        premises: Vec<String>,
        args: Vec<Rc<Term>>,
    },

    /// An "anchor" command, of the form "(anchor :step <symbol> [:args <proof_args>]?)".
    Anchor { step: String, args: Vec<Rc<Term>> },
}

/// A function definition. Functions are defined using the "function-def" command, of the form
/// "(define-fun <symbol> (<sorted_var>*) <sort> <term>)". These definitions are substituted in
/// during parsing, so these commands don't appear in the final AST.
pub struct FunctionDef {
    pub args: Vec<(String, Rc<Term>)>,
    pub return_sort: Term,
    pub body: Term,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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
}

impl FromStr for Operator {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "+" => Ok(Operator::Add),
            "-" => Ok(Operator::Sub),
            "*" => Ok(Operator::Mult),
            "/" => Ok(Operator::Div),
            "=" => Ok(Operator::Eq),
            "or" => Ok(Operator::Or),
            "and" => Ok(Operator::And),
            "not" => Ok(Operator::Not),
            _ => Err(()),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SortKind {
    Function,
    UserDefined,
    Atom,
    Bool,
    Int,
    Real,
    String,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Term {
    /// A terminal. This can be a constant or a variable.
    Terminal(Terminal),

    /// An application of a function to one or more terms.
    App(Identifier, Vec<Rc<Term>>),

    /// An application of a bulit-in operator to one or more terms.
    Op(Operator, Vec<Rc<Term>>),

    /// A sort.
    Sort(SortKind, Vec<Rc<Term>>),
    // TODO: binders
}

impl Term {
    /// The "Bool" built-in sort.
    pub fn bool() -> Self {
        Term::Sort(SortKind::Bool, Vec::new())
    }

    /// The "Int" built-in sort.
    pub fn int() -> Self {
        Term::Sort(SortKind::Int, Vec::new())
    }

    /// The "Real" built-in sort.
    pub fn real() -> Self {
        Term::Sort(SortKind::Real, Vec::new())
    }

    /// The "String" built-in sort.
    pub fn string() -> Self {
        Term::Sort(SortKind::String, Vec::new())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Terminal {
    Integer(u64),
    Real(Ratio<u64>),
    String(String),
    Var(Identifier),
}

/// Helper macro to construct `Terminal` terms.
#[macro_export]
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
    (var $e:expr) => {
        Term::Terminal(Terminal::Var(Identifier::Simple($e.into())))
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
