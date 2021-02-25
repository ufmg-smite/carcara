use num_rational::Ratio;
use std::rc::Rc;
use std::str::FromStr;

#[derive(Debug)]
pub struct Proof(pub Vec<ProofCommand>);

#[derive(Debug)]
pub enum ProofCommand {
    Assume(String, Rc<Term>),
    Step {
        step_name: String,
        clause: Clause,
        rule: String,
        premises: Vec<String>,
        args: Vec<Rc<Term>>,
    },
    Anchor {
        step: String,
        args: Vec<Rc<Term>>,
    },
    DefineFun {
        name: String,
        args: Vec<(String, Sort)>,
        return_sort: Sort,
    },
}

#[derive(Debug)]
pub struct Clause(pub Vec<Rc<Term>>);

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
pub enum Term {
    Terminal(Terminal),
    App(Rc<Term>, Vec<Rc<Term>>),
    Op(Operator, Vec<Rc<Term>>),
    // TODO: binders
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Sort(Term);

macro_rules! sort_from_iden {
    ($iden:expr) => {
        Sort(Term::Terminal(Terminal::Var(Identifier::Simple(
            $iden.into(),
        ))))
    };
}

impl Sort {
    pub fn bool() -> Self {
        sort_from_iden!("Bool")
    }

    pub fn int() -> Self {
        sort_from_iden!("Int")
    }

    pub fn real() -> Self {
        sort_from_iden!("Real")
    }

    pub fn string() -> Self {
        sort_from_iden!("String")
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Terminal {
    Integer(u64),
    Real(Ratio<u64>),
    String(String),
    Var(Identifier),
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
