use crate::ast::Constant;

use super::{Operator, Rc, Term};
use indexmap::IndexMap;
use std::cell::RefCell;
use std::fmt;

pub type Holes = IndexMap<String, Rc<RefCell<Option<Rc<Term>>>>>;

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum AttributeParameters {
    List,
    None,
}

#[derive(Debug, Clone)]
pub struct TypeParameter {
    pub term: Rc<Term>,
    pub attribute: AttributeParameters,
}

#[derive(Debug, Clone)]
pub struct RuleDefinition {
    pub name: String,
    pub parameters: IndexMap<String, TypeParameter>,
    pub arguments: Vec<String>,
    pub premises: Vec<Rc<Term>>,
    pub conclusion: Rc<Term>,
    pub is_elaborated: bool,
}

impl fmt::Display for RuleDefinition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(declare-rare-rule {} (", self.name)?;
        for (name, param) in &self.parameters {
            write!(
                f,
                "({} {} {}) ",
                name,
                param.term,
                if param.attribute == AttributeParameters::List {
                    ":list"
                } else {
                    ""
                }
            )?;
        }
        write!(f, ")\n  :args (")?;
        for arg in &self.arguments {
            write!(f, "{} ", arg)?;
        }
        write!(f, ")\n  :premises (")?;
        for premise in &self.premises {
            write!(f, "{} ", premise)?;
        }
        write!(f, ")\n  :conclusion {})\n", self.conclusion)
    }
}

#[derive(Debug, Clone)]
pub struct Program {
    pub name: String,
    pub parameters: IndexMap<String, TypeParameter>,
    pub patterns: Vec<(Rc<Term>, Rc<Term>)>,
    pub signature: Vec<Rc<Term>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DeclAttr {
    LeftAssoc,
    RightAssoc,
    RightAssocNil(Rc<Term>),
    Chainable(String),
    Binder(String),
    Pairwise(String),
}

#[derive(Debug, Clone)]
pub struct ParsedAnnotatedSort {
    pub base_sort: Rc<Term>,
    pub var_name: Option<String>,
    pub implicit: bool,
    pub requires: Vec<Vec<Rc<Term>>>,
}

#[derive(Debug, Clone)]
pub struct DeclConst {
    pub name: String,
    pub sort: Rc<Term>,
    pub attrs: Vec<DeclAttr>,
    pub parametrized_params: Vec<ParsedAnnotatedSort>,
    pub ty_params: Vec<ParsedAnnotatedSort>,
    pub is_parameterized: bool,
}

#[derive(Debug, Clone)]
pub struct RareStatements {
    pub rules: IndexMap<String, RuleDefinition>,
}

pub type Rules = RareStatements;

#[derive(Debug, Clone)]
pub enum RewriteTerm {
    ManyEq(Operator, &'static str),
    OperatorEq(Operator, Vec<RewriteTerm>),
    VarEqual(&'static str),
    Const(Constant),
}

#[macro_export]
macro_rules! pseudo_term {
    (true) => {$crate::rare::RewriteTerm::OperatorEq($crate::ast::Operator::True, vec![])};
    (false) => {$crate::rare::RewriteTerm::OperatorEq($crate::ast::Operator::False, vec![])};
    (0) => {$crate::rare::RewriteTerm::Const($crate::ast::Constant::Integer(Integer::from(0)))};
    (1) => {$crate::rare::RewriteTerm::Const($crate::ast::Constant::Integer(Integer::from(1)))};
    ("") => {$crate::rare::RewriteTerm::Const($crate::ast::Constant::String("".to_string()))};

    ($v:ident) => {$crate::rare::RewriteTerm::VarEqual(stringify!($v))};
    (($op:tt ..$args:ident..)) => {{
        $crate::rare::RewriteTerm::ManyEq($crate::ast::Operator::$op, stringify!($args))
    }};
    (($op:tt $($args:tt)+)) => {{
        let v = vec![ $(pseudo_term!($args)),+ ];
        $crate::rare::RewriteTerm::OperatorEq($crate::ast::Operator::$op, v)
    }};
    (($op:tt)) => {{
        let v = vec![];
        $crate::rare::RewriteTerm::OperatorEq($crate::ast::Operator::$op, v)
    }};
}

#[macro_export]
macro_rules! build_equation {
    ($r:tt ~> $rr:tt) => {{
        (pseudo_term!($r), pseudo_term!($rr))
    }};
}