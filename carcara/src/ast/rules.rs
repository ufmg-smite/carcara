use super::{Constant, Operator, Rc, Term};
use indexmap::IndexMap;
use std::cell::RefCell;

pub type Holes = IndexMap<String, Rc<RefCell<Option<Rc<Term>>>>>;

#[derive(Debug, Clone, PartialEq)]
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
}

pub type Rules = IndexMap<String, RuleDefinition>;
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