//! The AST types used for Rare files.

use crate::ast::Constant;

use super::{Operator, Rc, Sort, Term};
use indexmap::IndexMap;
use std::fmt;

/// The attribute of a parameter in a RARE rule.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum AttributeParameters {
    /// The `:list` attribute.
    List,

    /// No attribute.
    None,
}

/// A typed parameter in a RARE rule.
#[derive(Debug, Clone)]
pub struct TypeParameter {
    /// The sort of the parameter.
    pub sort: Rc<Sort>,

    /// The parameter attribute.
    pub attribute: AttributeParameters,
}

/// A RARE rule, from a `(declare-rare-rule ...)` command.
#[derive(Debug, Clone)]
pub struct RuleDefinition {
    /// The rule name.
    pub name: String,

    /// The rule's parameters.
    pub parameters: IndexMap<String, TypeParameter>,

    /// The rule's arguments, given via the `:args` attribute.
    pub arguments: Vec<String>,

    /// The rule's premises, given via the `:premises` attribute.
    pub premises: Vec<Rc<Term>>,

    /// The rule's conclusion, given via the `:conclusion` attribute.
    pub conclusion: Rc<Term>,

    /// Whether the rule has already been elaborated for egglog execution.
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
                param.sort,
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

/// A set of statements parsed from a Rare file.
#[derive(Debug, Clone, Default)]
pub struct RareStatements {
    /// The rare rules, indexed by their name.
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

macro_rules! build_equation {
    ($r:tt ~> $rr:tt) => {{ (pseudo_term!($r), pseudo_term!($rr)) }};
}

pub(crate) use {build_equation, pseudo_term};
