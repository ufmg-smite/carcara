use crate::ast::{
    Binder as AletheBinder, BindingList, Constant, Operator, Rc, Sort, SortedVar,
    Term as AletheTerm, TermPool,
};
use itertools::Itertools;
use std::borrow::Borrow;
use std::collections::VecDeque;
use std::ops::Deref;
use std::{fmt, vec};

const WHITE_SPACE: &'static str = " ";

use super::proof::Proof;
use super::Context;

/// The BNF grammar of Lambdapi is in [lambdapi.bnf](https://raw.githubusercontent.com/Deducteam/lambdapi/master/doc/lambdapi.bnf).
/// Data structure of this file try to represent this grammar.

#[inline]
pub fn set() -> Term {
    Term::TermId("Set".into())
}

#[inline]
pub fn omicron() -> Term {
    Term::TermId("o".into())
}

#[inline]
pub fn index() -> Term {
    Term::TermId("𝑰".into())
}

#[inline]
pub fn tau(term: Term) -> Term {
    //TODO: Print without parenthesis when there is only 1 sort
    Term::TermId(format!("τ ({})", term))
}

#[inline]
pub fn proof(term: Term) -> Term {
    Term::Alethe(LTerm::Proof(Box::new(term)))
}

#[derive(Debug, Clone, PartialEq)]
pub enum BuiltinSort {
    /// a non-dependent function A ⤳ T where A and T are Set
    Arrow(Box<Term>, Box<Term>),
    Bool,
    Int, //FIXME: We use ℤ because some feature in ℤ encoding are missing in Stdlib.Z
}

impl fmt::Display for BuiltinSort {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            BuiltinSort::Arrow(a, b) => write!(f, "{} ⤳ {}", a, b),
            BuiltinSort::Bool => write!(f, "o"),
            BuiltinSort::Int => write!(f, "int"),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Modifier {
    Constant,
    Opaque,
}

impl fmt::Display for Modifier {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Modifier::Constant => write!(f, "constant"),
            Modifier::Opaque => write!(f, "opaque"),
        }
    }
}

/// The Grammar <command> token
#[derive(Debug, Clone, PartialEq)]
pub enum Command {
    RequireOpen(String),
    /// Symbol declaration with a proof script (theorem or interactive definition)
    Symbol(Option<Modifier>, String, Vec<Param>, Term, Option<Proof>),
    /// Symbol declaration with an optional definition
    Definition(String, Vec<Param>, Option<Term>, Option<Term>),
    Rule(Term, Term),
}

impl fmt::Display for Command {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Command::RequireOpen(path) => write!(f, "open require {};", path),
            Command::Symbol(modifier, name, params, term, proof) => {
                let params = params
                    .iter()
                    .map(|x| format!("{}", x))
                    .collect::<Vec<_>>()
                    .join(WHITE_SPACE);
                write!(
                    f,
                    "{}symbol {} {}: {}",
                    modifier
                        .as_ref()
                        .map(|m| format!("{} ", m))
                        .unwrap_or(String::new()),
                    name,
                    params,
                    term
                )?;

                if let Some(proof) = proof {
                    write!(f, " ≔\n")?;
                    writeln!(f, "begin")?;
                    write!(f, "{}", proof)?;
                    write!(f, "\nend")?;
                }
                write!(f, ";\n")
            }
            Command::Definition(name, params, r#type, definition) => {
                let params = params
                    .iter()
                    .map(|x| format!("{}", x))
                    .collect::<Vec<_>>()
                    .join(WHITE_SPACE);
                write!(f, "symbol {} {}", name, params)?;
                if let Some(r#ty) = r#type {
                    write!(f, " : {}", r#ty)?;
                }
                if let Some(def) = definition {
                    write!(f, " ≔ {}", def)?;
                }
                //write!(f, "symbol {} {} : {} ≔ {};", name, params, r#type, definition)
                write!(f, ";\n")
            }
            Command::Rule(l, r) => writeln!(f, "rule {} ↪ {};", l, r),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Term {
    Alethe(LTerm),
    Sort(BuiltinSort),
    TermId(String),
    Terms(Vec<Term>),
    Function(Vec<Term>),
    /// Lambdapi can only represent Nat in its AST
    Nat(u32),
    Underscore,
}

macro_rules! terms {
    ($($t:expr),+ $(,)?) => {
        Term::Terms(vec![ $( $t),+ ])
    };
}

pub(crate) use terms;

pub trait VisitorArgs {
    fn visit(&mut self, mapping: &Vec<(&(String, Rc<AletheTerm>), &Rc<AletheTerm>)>);
}

impl VisitorArgs for LTerm {
    fn visit(&mut self, mapping: &Vec<(&(String, Rc<AletheTerm>), &Rc<AletheTerm>)>) {
        match self {
            LTerm::Clauses(ts) | LTerm::NOr(ts) | LTerm::NAnd(ts) => {
                ts.iter_mut().for_each(|t| t.visit(mapping));
            }
            LTerm::Choice(bs, t) => t.visit(
                &mapping
                    .into_iter()
                    .cloned()
                    .filter(|((id, _ ), _)| bs.0.iter().any(|SortedTerm(bind_name, _)| matches!(bind_name.borrow(), Term::TermId(x) if x != id )))
                    .collect_vec()
            ),
            LTerm::Exist(Bindings(bs), t) | LTerm::Forall(Bindings(bs), t) => t.visit(
                &mapping
                    .into_iter()
                    .cloned()
                    .filter(|((id, _), _)| bs.iter().any(|SortedTerm(bind_name, _)| matches!(bind_name.borrow(), Term::TermId(x) if x != id )))
                    .collect_vec()
            ),
            LTerm::Implies(t1, t2) | LTerm::Iff(t1, t2) | LTerm::Eq(t1, t2) => {
                t1.visit(mapping);
                t2.visit(mapping);
            }
            LTerm::Proof(t) => t.visit(mapping),
            LTerm::Neg(t) => {
                if let Some(t) = t {
                    t.visit(mapping)
                }
            }
            _ => {}
        }
    }
}

impl VisitorArgs for Term {
    fn visit(&mut self, mapping: &Vec<(&(String, Rc<AletheTerm>), &Rc<AletheTerm>)>) {
        match self {
            Term::TermId(id) => {
                if let Some((_, t)) = mapping.iter().find(|((name, _), _)| id == name) {
                    *self = (*t).into();
                }
            }
            Term::Function(ts) | Term::Terms(ts) => {
                ts.iter_mut().for_each(|t| t.visit(mapping));
            }
            Term::Alethe(t) => t.visit(mapping),
            t => todo!("{}", t),
        }
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Term::Alethe(t) => write!(f, "{}", t),
            Term::Sort(bs) => write!(f, "{}", bs),
            Term::TermId(id) => write!(f, "{}", id),
            Term::Function(terms) => write!(
                f,
                "{}",
                terms
                    .iter()
                    .map(|x| format!("{}", x))
                    .collect::<Vec<_>>()
                    .join(" → ")
            ),
            Term::Terms(terms) => {
                write!(
                    f,
                    "( {} )",
                    terms
                        .iter()
                        .map(|x| format!("{}", x))
                        .collect::<Vec<_>>()
                        .join(WHITE_SPACE)
                )
            }
            Term::Nat(n) => write!(f, "{}", n),
            Term::Underscore => write!(f, "_"),
        }
    }
}

/// Use to translate the `cong` rule
impl From<Operator> for Term {
    fn from(op: Operator) -> Self {
        match op {
            Operator::Equals => "(=)".into(),
            Operator::Or => "(∨ᶜ)".into(),
            Operator::And => "(∧ᶜ)".into(),
            Operator::LessEq => "(≤)".into(),
            Operator::LessThan => "(<)".into(),
            Operator::Implies => "(⇒ᶜ)".into(),
            Operator::Distinct => "distinct".into(),
            Operator::Add => "(+)".into(),
            Operator::Mult => "(×)".into(),
            Operator::Sub => "(-)".into(),
            Operator::GreaterEq => "(≥)".into(),
            Operator::GreaterThan => "(>)".into(),
            Operator::Not => "(¬)".into(),
            o => todo!("Operator {:?}", o),
        }
    }
}

impl<S: Into<String>> From<S> for Term {
    fn from(id: S) -> Self {
        Term::TermId(id.into())
    }
}

pub fn conv(term: &Rc<AletheTerm>, ctx: &crate::lambdapi::Context) -> Term {
    ctx.term_sharing.get(term).map_or_else(
        || match term.deref() {
            AletheTerm::Sort(_) => Term::from(term),
            AletheTerm::App(f, args) => {
                let mut func = vec![conv(f, ctx)];
                let mut args: Vec<Term> = args.into_iter().map(|a| conv(a, ctx)).collect();
                func.append(&mut args);
                Term::Terms(func)
            }
            AletheTerm::Op(operator, args) => {
                let args = args
                    .into_iter()
                    .map(|a| conv(a, ctx))
                    .collect::<VecDeque<_>>();
                return match operator {
                    Operator::Not => Term::Alethe(LTerm::Neg(Some(Box::new(
                        args.front().map(|a| a.clone()).unwrap(),
                    )))),
                    Operator::Or => Term::Alethe(LTerm::NOr(args.into())),
                    Operator::Equals => Term::Alethe(LTerm::Eq(
                        Box::new(args[0].clone()),
                        Box::new(args[1].clone()),
                    )),
                    Operator::And => Term::Alethe(LTerm::NAnd(args.into())),
                    Operator::Implies => Term::Alethe(LTerm::Implies(
                        Box::new(args[0].clone()),
                        Box::new(args[1].clone()),
                    )),
                    Operator::Distinct => Term::Alethe(LTerm::Distinct(ListLP(
                        args.into_iter().map(Into::into).collect_vec(),
                    ))),
                    Operator::Sub if args.len() == 2 => {
                        Term::Terms(vec![args[0].clone(), "-".into(), args[1].clone()])
                    }
                    Operator::Sub if args.len() == 1 => {
                        Term::Terms(vec!["~".into(), args[0].clone()])
                    }
                    Operator::Add => {
                        Term::Terms(vec![args[0].clone(), "+".into(), args[1].clone()])
                    }
                    Operator::GreaterEq => {
                        Term::Terms(vec![args[0].clone(), "≥".into(), args[1].clone()])
                    }
                    Operator::GreaterThan => {
                        Term::Terms(vec![args[0].clone(), ">".into(), args[1].clone()])
                    }
                    Operator::LessEq => {
                        Term::Terms(vec![args[0].clone(), "≤".into(), args[1].clone()])
                    }
                    Operator::LessThan => {
                        Term::Terms(vec![args[0].clone(), "<".into(), args[1].clone()])
                    }
                    Operator::Mult => {
                        Term::Terms(vec![args[0].clone(), "×".into(), args[1].clone()])
                    }
                    Operator::RareList => {
                        Term::Terms(args.into_iter().map(From::from).collect_vec())
                    }
                    Operator::True => Term::Alethe(LTerm::True),
                    Operator::False => Term::Alethe(LTerm::False),
                    o => todo!("Operator {:?}", o),
                };
            }
            AletheTerm::Let(..) => todo!("let term"),
            AletheTerm::Binder(AletheBinder::Forall, bs, t) => {
                Term::Alethe(LTerm::Forall(Bindings::from(bs), Box::new(conv(t, ctx))))
            }
            AletheTerm::Binder(AletheBinder::Exists, bs, t) => {
                Term::Alethe(LTerm::Exist(Bindings::from(bs), Box::new(conv(t, ctx))))
            }
            AletheTerm::Binder(AletheBinder::Choice, bs, t) => {
                Term::Alethe(LTerm::Choice(Bindings::from(bs), Box::new(conv(t, ctx))))
            }
            AletheTerm::Var(id, _term) => Term::TermId(id.to_string()),
            AletheTerm::Const(c) => match c {
                Constant::Integer(i) => Term::Nat(i.to_u32().unwrap()), //FIXME: better support of number
                Constant::String(s) => Term::from(s),
                c => unimplemented!("{}", c),
            },
            e => todo!("{:#?}", e),
        },
        |(name, _def)| Term::from(name),
    )
}

impl From<&Rc<AletheTerm>> for Term {
    fn from(term: &Rc<AletheTerm>) -> Self {
        match term.deref() {
            AletheTerm::Sort(sort) => match sort {
                Sort::Function(params) => Term::Function(params.iter().map(Term::from).collect()),
                Sort::Atom(id, _terms) => Term::TermId(id.clone()),
                Sort::Bool => Term::Sort(BuiltinSort::Bool),
                Sort::Int => Term::Sort(BuiltinSort::Int),
                s => todo!("{:#?}", s),
            },
            AletheTerm::App(f, args) => {
                let mut func = vec![Term::from(f)];
                let mut args: Vec<Term> = args.into_iter().map(Term::from).collect();
                func.append(&mut args);
                Term::Terms(func)
            }
            AletheTerm::Op(operator, args) => {
                let args = args.into_iter().map(Term::from).collect::<VecDeque<_>>();
                return match operator {
                    Operator::Not => Term::Alethe(LTerm::Neg(Some(Box::new(
                        args.front().map(|a| Term::from(a.clone())).unwrap(),
                    )))),
                    Operator::Or => {
                        //args.push_back(Term::Alethe(LTerm::False));
                        Term::Alethe(LTerm::NOr(args.into()))
                    }
                    Operator::Equals => Term::Alethe(LTerm::Eq(
                        Box::new(args[0].clone()),
                        Box::new(args[1].clone()),
                    )),
                    Operator::And => {
                        //args.push_back(Term::Alethe(LTerm::True));
                        Term::Alethe(LTerm::NAnd(args.into()))
                    }
                    Operator::Implies => Term::Alethe(LTerm::Implies(
                        Box::new(args[0].clone()),
                        Box::new(args[1].clone()),
                    )),
                    Operator::Distinct => Term::Alethe(LTerm::Distinct(ListLP(
                        args.into_iter().map(Into::into).collect_vec(),
                    ))),
                    Operator::Sub if args.len() == 2 => {
                        Term::Terms(vec![args[0].clone(), "-".into(), args[1].clone()])
                    }
                    Operator::Sub if args.len() == 1 => {
                        Term::Terms(vec!["~".into(), args[0].clone()])
                    }
                    Operator::Add => {
                        Term::Terms(vec![args[0].clone(), "+".into(), args[1].clone()])
                    }
                    Operator::GreaterEq => {
                        Term::Terms(vec![args[0].clone(), "≥".into(), args[1].clone()])
                    }
                    Operator::GreaterThan => {
                        Term::Terms(vec![args[0].clone(), ">".into(), args[1].clone()])
                    }
                    Operator::LessEq => {
                        Term::Terms(vec![args[0].clone(), "≤".into(), args[1].clone()])
                    }
                    Operator::LessThan => {
                        Term::Terms(vec![args[0].clone(), "<".into(), args[1].clone()])
                    }
                    Operator::Mult => {
                        Term::Terms(vec![args[0].clone(), "×".into(), args[1].clone()])
                    }
                    Operator::RareList => {
                        Term::Terms(args.into_iter().map(From::from).collect_vec())
                    }
                    Operator::True => Term::Alethe(LTerm::True),
                    Operator::False => Term::Alethe(LTerm::False),
                    o => todo!("Operator {:?}", o),
                };
            }
            AletheTerm::Let(..) => todo!("let term"),
            AletheTerm::Binder(AletheBinder::Forall, bs, t) => {
                Term::Alethe(LTerm::Forall(Bindings::from(bs), Box::new(Term::from(t))))
            }
            AletheTerm::Binder(AletheBinder::Exists, bs, t) => {
                Term::Alethe(LTerm::Exist(Bindings::from(bs), Box::new(Term::from(t))))
            }
            AletheTerm::Binder(AletheBinder::Choice, bs, t) => {
                Term::Alethe(LTerm::Choice(Bindings::from(bs), Box::new(Term::from(t))))
            }
            AletheTerm::Var(id, _term) => Term::TermId(id.to_string()),
            AletheTerm::Const(c) => match c {
                Constant::Integer(i) => Term::Nat(i.to_u32().unwrap()), //FIXME: better support of number
                Constant::String(s) => Term::from(s),
                c => unimplemented!("{}", c),
            },
            e => todo!("{:#?}", e),
        }
    }
}

impl From<Rc<AletheTerm>> for Term {
    fn from(term: Rc<AletheTerm>) -> Self {
        Self::from(&term)
    }
}

impl From<AletheTerm> for Term {
    fn from(term: AletheTerm) -> Self {
        Self::from(&Rc::new(term))
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Param(pub String, pub Term);

impl fmt::Display for Param {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Param(id, _term) => write!(f, "{}", id),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct SortedTerm(pub Box<Term>, pub Box<Term>);

impl From<&SortedVar> for SortedTerm {
    fn from(var: &SortedVar) -> Self {
        SortedTerm(
            Box::new(Term::TermId(var.0.clone())),
            Box::new(Term::from(&var.1)),
        )
    }
}

impl fmt::Display for SortedTerm {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}: {}", self.0, self.1)
    }
}

/// Represent the Stdlib.List inductive type in a shallow Rust encoding (Vec).
/// This structure exists for making pretty printing easier by not overloading LTerm.
#[derive(Debug, Clone, PartialEq)]
pub struct Bindings(pub Vec<SortedTerm>);

impl From<&BindingList> for Bindings {
    fn from(bindings: &BindingList) -> Self {
        Bindings(
            bindings
                .into_iter()
                .map(SortedTerm::from)
                .collect::<Vec<_>>(),
        )
    }
}

impl fmt::Display for Bindings {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let s = Itertools::intersperse(
            self.0.iter().map(|t| format!("({})", t)),
            WHITE_SPACE.to_string(),
        )
        .collect::<String>();
        write!(f, "{}", s)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct ListLP(pub Vec<Term>);

impl fmt::Display for ListLP {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let s = self
            .0
            .iter()
            .rev()
            .fold("□".to_string(), |acc, e| format!("(cons {} {})", e, acc));
        write!(f, "{}", s)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum LTerm {
    True,
    False,
    NAnd(Vec<Term>),
    NOr(Vec<Term>),
    Neg(Option<Box<Term>>), //TODO: explain why cong need to add Option to Neg
    Implies(Box<Term>, Box<Term>),
    Iff(Box<Term>, Box<Term>),
    Eq(Box<Term>, Box<Term>),
    Clauses(Vec<Term>),
    Proof(Box<Term>),
    Resolution(
        bool,
        Option<Box<Term>>,
        Option<Box<Term>>,
        Option<Box<Term>>,
        Box<Term>,
        Box<Term>,
    ),
    Forall(Bindings, Box<Term>),
    Exist(Bindings, Box<Term>),
    Distinct(ListLP),
    Choice(Bindings, Box<Term>),
}

macro_rules! id {
    ($x1:expr) => {
        Term::TermId($x1.into())
    };
}

pub(crate) use id;

macro_rules! bid {
    ($x1:expr) => {
        Box::new(Term::TermId($x1.into()))
    };
}

pub(crate) use bid;

macro_rules! not {
    ($x1:expr) => {
        Term::Alethe(LTerm::Neg(Some(Box::new($x1))))
    };
}

pub(crate) use not;

macro_rules! eq {
    ($x1:expr, $x2:expr) => {
        Term::Alethe(LTerm::Eq($x1, $x2))
    };
}

pub(crate) use eq;

macro_rules! imp {
    ($x1:expr, $x2:expr) => {
        Term::Alethe(LTerm::Implies(Box::new($x1), Box::new($x2)))
    };
}

pub(crate) use imp;

macro_rules! iff {
    ($x1:expr, $x2:expr) => {
        Term::Alethe(LTerm::Iff($x1, $x2))
    };
}

pub(crate) use iff;

macro_rules! or {
    ($($x:expr),+ $(,)?) => {
        Box::new(Term::Alethe(LTerm::NOr(vec![
            $($x),+
        ])))
    };
}

pub(crate) use or;

macro_rules! and {
    ($($x:expr),+ $(,)?) => {
        Box::new(Term::Alethe(LTerm::NAnd(vec![
            $($x),+
        ])))
    };
}

pub(crate) use and;

impl fmt::Display for LTerm {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            LTerm::True => write!(f, "⊤"),
            LTerm::False => write!(f, "⊥"),
            LTerm::Neg(Some(t)) => write!(f, "(¬ᶜ {})", t),
            LTerm::Neg(None) => write!(f, "¬ᶜ"),
            LTerm::NAnd(ts) => {
                let s = Itertools::intersperse(
                    ts.into_iter().map(|t| format!("{}", t)),
                    " ∧ᶜ ".to_string(),
                )
                .collect::<String>();
                write!(f, "{}", s)
            }
            LTerm::NOr(ts) => {
                let s = Itertools::intersperse(
                    ts.into_iter().map(|t| format!("{}", t)),
                    " ∨ᶜ ".to_string(),
                )
                .collect::<String>();
                write!(f, "{}", s)
            }
            LTerm::Clauses(ts) => {
                if ts.is_empty() {
                    write!(f, "{}", LTerm::False)
                } else {
                    let s = Itertools::intersperse(
                        ts.into_iter().map(|t| format!("({})", t)),
                        " ⟇ ".to_string(),
                    )
                    .collect::<String>();
                    write!(f, "{}", s)
                }
            }
            LTerm::Implies(l, r) => {
                write!(f, "({}) ⇒ᶜ ({})", l, r)
            }
            LTerm::Iff(l, r) => {
                write!(f, "({}) ⇔ᶜ ({})", l, r)
            }
            LTerm::Eq(l, r) => {
                write!(f, "({}) = ({})", l, r)
            }
            LTerm::Proof(t) => write!(f, "π ({})", t),
            LTerm::Resolution(pivot_position, pivot, a, b, h1, h2) => {
                if *pivot_position {
                    write!(f, "resolutionₗ ")?;
                } else {
                    write!(f, "resolutionᵣ ")?;
                }

                write!(
                    f,
                    "{} {} {} {} {}",
                    pivot.to_owned().unwrap_or(Box::new(Term::Underscore)),
                    a.to_owned().unwrap_or(Box::new(Term::Underscore)),
                    b.to_owned().unwrap_or(Box::new(Term::Underscore)),
                    h1,
                    h2
                )
            }
            LTerm::Forall(bs, t) => write!(f, "`∀ᶜ {}, {}", bs, t),
            LTerm::Exist(bs, t) => write!(f, "`∃ᶜ {}, {}", bs, t),
            LTerm::Distinct(l) => write!(f, "distinct ({})", l),
            LTerm::Choice(x, p) => write!(f, "`ϵ {}, {}", x, p),
        }
    }
}

#[inline]
pub fn clauses(terms: Vec<Term>) -> Term {
    Term::Alethe(LTerm::Proof(Box::new(Term::Alethe(LTerm::Clauses(terms)))))
}

macro_rules! cl {
    ($($x:expr),+ $(,)?) => {
        Term::Alethe(LTerm::Proof(Box::new(Term::Alethe(LTerm::Clauses( vec![ $($x),+ ] )))))
    };
}

pub(crate) use cl;

pub trait Visitor {
    fn visit(&self, ctx: &mut Context);
}

impl Visitor for Rc<AletheTerm> {
    fn visit(&self, ctx: &mut Context) {
        match self.deref() {
            AletheTerm::Const(_)
            | AletheTerm::Var(..)
            | AletheTerm::Sort(_)
            | AletheTerm::ParamOp { .. }
            | AletheTerm::Let(..)
            | AletheTerm::Op(Operator::True, _)
            | AletheTerm::Op(Operator::False, _) => {}
            AletheTerm::Op(_, ops) => {
                if self.is_closed(&mut ctx.pool, &ctx.global_variables) {
                    if let Some((count, t)) = ctx.term_indices.get_mut(self) {
                        *count = *count + 1;
                        if *count >= 1 {
                            ctx.term_sharing
                                .insert(self.clone(), (t.to_string(), self.into()));
                        }
                    } else {
                        ctx.term_indices.insert(
                            self.clone(),
                            (1, format!("p_{}", ctx.term_indices.len() + 1)),
                        );
                    }
                }
                ops.into_iter().for_each(|op| op.visit(ctx));
            }
            AletheTerm::App(o, ops) => {
                if self.is_closed(&mut ctx.pool, &ctx.global_variables) {
                    if let Some((count, t)) = ctx.term_indices.get_mut(self) {
                        *count = *count + 1;
                        if *count >= 1 {
                            ctx.term_sharing
                                .insert(self.clone(), (t.to_string(), self.into()));
                        }
                    } else {
                        ctx.term_indices.insert(
                            self.clone(),
                            (1, format!("p_{}", ctx.term_indices.len() + 1)),
                        );
                    }
                }
                o.visit(ctx);
                ops.into_iter().for_each(|op| op.visit(ctx));
            }
            AletheTerm::Binder(_, bs, t) => {
                let bounded_variables = bs.into_iter().map(|(name, _)| name).collect_vec();
                let free_vars_remaining = ctx
                    .pool
                    .free_vars(self)
                    .into_iter()
                    .filter(|var| !ctx.global_variables.contains(var))
                    .filter(|var| match var.deref() {
                        AletheTerm::Var(var, _) => bounded_variables.contains(&var) == false,
                        _ => false,
                    })
                    .collect_vec();

                if free_vars_remaining.is_empty() {
                    if let Some((count, t)) = ctx.term_indices.get_mut(self) {
                        *count = *count + 1;
                        if *count >= 1 {
                            ctx.term_sharing
                                .insert(self.clone(), (t.to_string(), self.into()));
                        }
                    } else {
                        ctx.term_indices.insert(
                            self.clone(),
                            (1, format!("p_{}", ctx.term_indices.len() + 1)),
                        );
                    }
                }
                t.visit(ctx);
            }
        }
    }
}

#[cfg(test)]
mod tests_term {
    use super::*;
    use crate::parser::{parse_instance, Config};
    use std::collections::HashSet;

    #[test]
    fn test_free_var_collection() {
        let problem: &[u8] = b"
            (declare-sort Idv 0)
            (declare-fun clt () Idv)
            (declare-fun cap (Idv Idv) Idv)
            (declare-fun FunApp (Idv Idv) Idv)
            (declare-fun FunExcept (Idv Idv Idv) Idv)
            (declare-fun Mem (Idv Idv) Bool)
            (declare-fun SetEnum () Idv)
            (declare-fun TrigEq (Idv Idv) Bool)
            (declare-fun TrigEqDollar (Idv
            Idv) Bool)
            (declare-fun Client () Idv)
            (declare-fun Res () Idv)
            (declare-fun VarUnsat () Idv)
            (declare-fun UnsatPrim () Idv)
            (declare-fun Alloc () Idv)
            (declare-fun AllocPrim () Idv)
            (declare-fun S () Idv)
        ";
        let proof = b"
            (assume Goal (! (not (=> (! (and (forall ((c1 Idv) (c2 Idv)) (=> (and (Mem c1 Client) (Mem c2 Client)) (forall ((r Idv)) (=> (Mem r Res) (=> (Mem r (cap (FunApp Alloc c1) (FunApp Alloc c2))) (TrigEq c1 c2)))))) (and (and (! (TrigEqDollar (FunApp VarUnsat clt) SetEnum) :named @p_5) (! (TrigEqDollar (FunApp Alloc clt) SetEnum) :named @p_4)) (and (! (not (TrigEqDollar S SetEnum)) :named @p_3) (! (TrigEq UnsatPrim (FunExcept VarUnsat clt S)) :named @p_2)) (! (TrigEq AllocPrim Alloc) :named @p_1))) :named @p_6) (forall ((c1 Idv) (c2 Idv)) (=> (and (Mem c1 Client) (Mem c2 Client)) (forall ((r Idv)) (=> (Mem r Res) (=> (Mem r (cap (FunApp AllocPrim c1) (FunApp AllocPrim c2))) (TrigEq c1 c2)))))))) :named @p_7))
            (step t1 (cl (and (Mem S S) (not (=> (! (and (forall ((c1 Idv) (c2 Idv)) (=> (and (Mem c1 Client) (Mem c2 Client)) (forall ((r Idv)) (=> (Mem r Res) (=> (Mem r (cap (FunApp Alloc c1) (FunApp Alloc c2))) (TrigEq c1 c2)))))) (and (and (! (TrigEqDollar (FunApp VarUnsat clt) SetEnum) :named @p_5) (! (TrigEqDollar (FunApp Alloc clt) SetEnum) :named @p_4)) (and (! (not (TrigEqDollar S SetEnum)) :named @p_3) (! (TrigEq UnsatPrim (FunExcept VarUnsat clt S)) :named @p_2)) (! (TrigEq AllocPrim Alloc) :named @p_1))) :named @p_6) (forall ((c1 Idv) (c2 Idv)) (=> (and (Mem c1 Client) (Mem c2 Client)) (forall ((r Idv)) (=> (Mem r Res) (=> (Mem r (cap (FunApp AllocPrim c1) (FunApp AllocPrim c2))) (TrigEq c1 c2))))))))))  :rule hole)
        ";
        let (problem, proof, mut pool) = parse_instance(problem, proof, Config::new()).unwrap();

        let mut ctx = Context::default();

        let global_variables: HashSet<_> = problem
            .prelude
            .function_declarations
            .iter()
            .map(|var| pool.add(var.clone().into()))
            .collect();

        ctx.global_variables = global_variables;

        let res = crate::lambdapi::translate_commands(
            &mut ctx,
            &mut proof.iter(),
            0,
            |id, t, ps| Command::Symbol(None, crate::lambdapi::normalize_name(id), vec![], t, Some(Proof(ps))),
        )
        .expect("translate cong");

        assert_eq!(2, res.len());

        let t1 = res.last().unwrap().clone();
    }

    #[test]
    fn test_free_var_quantifier() {
        let problem: &[u8] = b"
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun r () Bool)
            (declare-fun s () Bool)
        ";
        let proof = b"
            (step t1 (cl (or
                    (not (forall ((p Bool) (q Bool))
                        (not (and (=> p q) (or q (not (not p))) (or r false (not q))))
                    ))
                    (forall ((p Bool) (q Bool)) (or p (not q) (not s)))
                )) :rule qnt_cnf)
        ";
        let (problem, proof, mut pool) = parse_instance(problem, proof, Config::new()).unwrap();

        let global_variables: HashSet<_> = problem
            .prelude
            .function_declarations
            .iter()
            .map(|var| pool.add(var.clone().into()))
            .collect();

        assert_eq!(1, proof.commands.len());

        let node = crate::ast::ProofNode::from_commands(proof.commands.clone());

        let clause = node.clause().first().unwrap();

        let mut ctx = Context::default();

        ctx.global_variables = global_variables;

        clause.visit(&mut ctx);

        println!("global var {:#?}", ctx.global_variables);
        println!("indices {:#?}", ctx.term_indices);
        println!("sharing {:#?}", ctx.term_sharing);
    }
}


// (step t1 (cl 
//     (and (Mem S S)
//     (not (=> (! (and (forall ((c1 Idv) (c2 Idv)) (=> (and (Mem c1 Client) (Mem c2 Client)) (forall ((r Idv)) (=> (Mem r Res) (=> (Mem r (cap (FunApp Alloc c1) (FunApp Alloc c2))) (TrigEq c1 c2)))))) (and (and (! (TrigEqDollar (FunApp VarUnsat clt) SetEnum) :named @p_5) (! (TrigEqDollar (FunApp Alloc clt) SetEnum) :named @p_4)) (and (! (not (TrigEqDollar S SetEnum)) :named @p_3) (! (TrigEq UnsatPrim (FunExcept VarUnsat clt S)) :named @p_2)) (! (TrigEq AllocPrim Alloc) :named @p_1))) :named @p_6) (forall ((c1 Idv) (c2 Idv)) (=> (and (Mem c1 Client) (Mem c2 Client)) (forall ((r Idv)) (=> (Mem r Res) (=> (Mem r (cap (FunApp AllocPrim c1) (FunApp AllocPrim c2))) (TrigEq c1 c2))))))))
//     )
//     )  :rule hole)