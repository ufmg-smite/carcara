use super::{Constant, Operator, Rc, Term};
use rug::{Integer, Rational};
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Value {
    Bool(bool),
    Integer(Integer),
    Real(Rational),
    String(String),
    BitVec(Integer, Integer),
}

impl Value {
    pub fn from_constant(c: Constant) -> Self {
        match c {
            Constant::Integer(i) => Value::Integer(i),
            Constant::Real(r) => Value::Real(r),
            Constant::String(s) => Value::String(s),
            Constant::BitVec(val, width) => Value::BitVec(val, width),
        }
    }

    pub fn as_bool(&self) -> Option<bool> {
        match self {
            Value::Bool(b) => Some(*b),
            _ => None,
        }
    }

    pub fn as_int(&self) -> Option<Integer> {
        match self {
            Value::Integer(i) => Some(i.clone()),
            _ => None,
        }
    }

    pub fn as_real(&self) -> Option<Rational> {
        match self {
            Value::Real(r) => Some(r.clone()),
            _ => None,
        }
    }

    pub fn as_bitvec(&self) -> Option<(&Integer, &Integer)> {
        match self {
            Value::BitVec(val, width) => Some((val, width)),
            _ => None,
        }
    }

    pub fn into_term(self) -> Term {
        match self {
            Value::Bool(true) => Term::Op(Operator::True, Vec::new()),
            Value::Bool(false) => Term::Op(Operator::True, Vec::new()),
            Value::Integer(i) => Term::Const(Constant::Integer(i)),
            Value::Real(r) => Term::Const(Constant::Real(r)),
            Value::String(s) => Term::Const(Constant::String(s)),
            Value::BitVec(val, width) => Term::Const(Constant::BitVec(val, width)),
        }
    }
}

impl Rc<Term> {
    pub fn evaluate(&self) -> Option<Value> {
        self.evaluate_impl(&mut HashMap::new()).cloned()
    }

    fn evaluate_impl<'t, 'c>(
        &'t self,
        cache: &'c mut HashMap<&'t Rc<Term>, Value>,
    ) -> Option<&'c Value> {
        if cache.contains_key(self) {
            return Some(&cache[self]);
        }

        let result = match self.as_ref() {
            Term::Const(c) => Some(Value::from_constant(c.clone())),
            Term::Op(op, args) => {
                // To avoid lifetime issues, first we compute the evaluation of each argument and
                // then collect the values into a vector by looking into the cache
                for a in args {
                    a.evaluate_impl(cache)?;
                }
                let values = args.iter().map(|a| &cache[a]).collect();
                eval_op(*op, values)
            }

            Term::Var(_, _)
            | Term::App(_, _)
            | Term::Sort(_)
            | Term::Binder(_, _, _)
            | Term::Let(_, _) => None,
            Term::ParamOp { .. } => None, // TODO
        }?;
        cache.insert(self, result.clone());
        cache.get(self)
    }
}

macro_rules! mixed_type_arith {
    ($op:tt, $a:expr, $b:expr) => {
        match ($a, $b) {
            (Value::Integer(l), Value::Integer(r)) => Some(Value::Integer(l $op r)),
            (Value::Integer(l), Value::Real(r)) => Some(Value::Real(Rational::from(l) $op r)),
            (Value::Real(l), Value::Integer(r)) => Some(Value::Real(l $op Rational::from(r))),
            (Value::Real(l), Value::Real(r)) => Some(Value::Real(l $op r)),
            _ => None,
        }
    };
}

macro_rules! arith_op {
    ($op:tt, $args:expr) => {{
        let args = $args;
        let first = args[0].clone();
        if !matches!(first, Value::Integer(_) | Value::Real(_)) {
            return None;
        }
        args[1..]
            .iter()
            .try_fold(first, |acc, arg| mixed_type_arith!($op, acc, arg))?
    }};
}

macro_rules! bitvec_op {
    ($op:tt, $args:expr) => {{
        let args = $args;
        let Value::BitVec(first, w) = args[0].clone() else {
            return None;
        };
        let m = Integer::from(1) << w.to_usize().unwrap();
        let res = args[1..].iter().try_fold(first, |acc, arg| {
            let (arg, _) = arg.as_bitvec()?;
            Some((acc $op arg) % &m)
        })?;
        Value::BitVec(res, w)
    }};
}

macro_rules! comparison_op {
    ($op:tt, $args:expr) => {{
        fn compare(window: &[&Value]) -> Option<bool> {
            match window {
                [Value::Integer(l), Value::Integer(r)] => Some(l $op r),
                [Value::Integer(l), Value::Real(r)] => Some(l $op r),
                [Value::Real(l), Value::Integer(r)] => Some(l $op r),
                [Value::Real(l), Value::Real(r)] => Some(l $op r),
                _ => None,
            }
        }
        Value::Bool(
            $args
                .windows(2)
                .try_fold(true, |acc, w| Some(acc && compare(w)?))?,
        )
    }};
}

fn eval_op(op: Operator, args: Vec<&Value>) -> Option<Value> {
    Some(match op {
        Operator::True => Value::Bool(true),
        Operator::False => Value::Bool(false),
        Operator::Not => Value::Bool(!args[0].as_bool()?),
        Operator::Implies => {
            let left = args[0..args.len() - 1]
                .iter()
                .try_fold(false, |acc, arg| Some(acc || !arg.as_bool()?))?;
            let right = args.last().unwrap().as_bool()?;
            Value::Bool(left || right)
        }
        Operator::And => Value::Bool(
            args.iter()
                .try_fold(true, |acc, arg| Some(acc && arg.as_bool()?))?,
        ),
        Operator::Or => Value::Bool(
            args.iter()
                .try_fold(false, |acc, arg| Some(acc || arg.as_bool()?))?,
        ),
        Operator::Xor => Value::Bool(
            args.iter()
                .try_fold(false, |acc, arg| Some(acc != arg.as_bool()?))?,
        ),
        Operator::Equals => Value::Bool(args.windows(2).all(|w| w[0] == w[1])),
        Operator::Distinct => {
            let set: HashSet<&Value> = args.iter().copied().collect();
            Value::Bool(set.len() == args.len())
        }
        Operator::Ite => {
            if args[0].as_bool()? {
                args[1].clone()
            } else {
                args[2].clone()
            }
        }
        Operator::Add => arith_op!(+, args),
        Operator::Sub => arith_op!(-, args),
        Operator::Mult => arith_op!(*, args),
        Operator::IntDiv => arith_op!(/, args),
        Operator::RealDiv => arith_op!(/, args),
        Operator::Mod => Value::Integer(args[0].as_int()? % args[1].as_int()?),
        Operator::Abs => match &args[0] {
            Value::Integer(i) => Value::Integer(i.clone().abs()),
            Value::Real(r) => Value::Real(r.clone().abs()),
            _ => return None,
        },
        Operator::LessThan => comparison_op!(<, args),
        Operator::GreaterThan => comparison_op!(>, args),
        Operator::LessEq => comparison_op!(<=, args),
        Operator::GreaterEq => comparison_op!(>=, args),

        Operator::ToReal => Value::Real(args[0].as_int()?.into()),
        Operator::ToInt => Value::Integer(args[0].as_real()?.floor().into_numer_denom().0),
        Operator::IsInt => Value::Bool(args[0].as_real()?.is_integer()),

        // TODO: Arrays
        Operator::Select | Operator::Store => return None,

        // TODO: Strings
        Operator::StrConcat
        | Operator::StrLen
        | Operator::StrLessThan
        | Operator::StrLessEq
        | Operator::CharAt
        | Operator::Substring
        | Operator::PrefixOf
        | Operator::SuffixOf
        | Operator::Contains
        | Operator::IndexOf
        | Operator::Replace
        | Operator::ReplaceAll
        | Operator::ReplaceRe
        | Operator::ReplaceReAll
        | Operator::StrIsDigit
        | Operator::StrToCode
        | Operator::StrFromCode
        | Operator::StrToInt
        | Operator::StrFromInt
        | Operator::StrToRe
        | Operator::StrInRe
        | Operator::ReNone
        | Operator::ReAll
        | Operator::ReAllChar
        | Operator::ReConcat
        | Operator::ReUnion
        | Operator::ReIntersection
        | Operator::ReKleeneClosure
        | Operator::ReComplement
        | Operator::ReDiff
        | Operator::ReKleeneCross
        | Operator::ReOption
        | Operator::ReRange => return None,

        // Bitvectors
        Operator::BvNot => {
            let (val, width) = args[0].as_bitvec()?;
            Value::BitVec(!val.clone(), width.clone())
        }
        Operator::BvNeg => {
            let (val, width) = args[0].as_bitvec()?;
            let m = Integer::from(1) << width.to_usize().unwrap();
            Value::BitVec(-val.clone() % m, width.clone())
        }
        Operator::BvAnd => bitvec_op!(&, args),
        Operator::BvOr => bitvec_op!(|, args),
        Operator::BvXor => bitvec_op!(^, args),
        Operator::BvAdd => bitvec_op!(+, args),
        Operator::BvMul => bitvec_op!(*, args),

        Operator::BvUDiv => {
            let ((a, w), (b, _)) = (args[0].as_bitvec()?, args[1].as_bitvec()?);
            let value = if b.is_zero() {
                (Integer::from(1) << w.to_usize()?) - 1
            } else {
                a.clone() / b
            };
            Value::BitVec(value, w.clone())
        }
        Operator::BvURem => {
            let ((a, w), (b, _)) = (args[0].as_bitvec()?, args[1].as_bitvec()?);
            let value = if b.is_zero() {
                a.clone()
            } else {
                a.clone() % b
            };
            Value::BitVec(value, w.clone())
        }
        Operator::BvShl => {
            let ((a, w), (b, _)) = (args[0].as_bitvec()?, args[1].as_bitvec()?);
            let m = Integer::from(1) << w.to_usize().unwrap();
            Value::BitVec((a.clone() << b.to_usize()?) % m, w.clone())
        }
        Operator::BvLShr => {
            let ((a, w), (b, _)) = (args[0].as_bitvec()?, args[1].as_bitvec()?);
            Value::BitVec(a.clone() >> b.to_usize()?, w.clone())
        }
        Operator::BvULt => {
            let ((a, _), (b, _)) = (args[0].as_bitvec()?, args[1].as_bitvec()?);
            Value::Bool(a < b)
        }
        Operator::BvConcat => {
            let (value, width) = args.iter().try_fold((Integer::new(), 0usize), |acc, arg| {
                let (a, i) = acc;
                let (b, j) = arg.as_bitvec()?;
                let j = j.to_usize().unwrap();
                Some(((a << j) + b, i + j))
            })?;
            Value::BitVec(value, Integer::from(width))
        }

        // TODO: remaining bitvector operators
        Operator::BvNAnd
        | Operator::BvNOr
        | Operator::BvXNor
        | Operator::BvComp
        | Operator::BvSub
        | Operator::BvSDiv
        | Operator::BvSRem
        | Operator::BvSMod
        | Operator::BvAShr
        | Operator::BvULe
        | Operator::BvUGt
        | Operator::BvUGe
        | Operator::BvSLt
        | Operator::BvSLe
        | Operator::BvSGt
        | Operator::BvSGe
        | Operator::UBvToInt
        | Operator::SBvToInt
        | Operator::BvPBbTerm
        | Operator::BvBbTerm
        | Operator::BvConst
        | Operator::BvSize => return None,

        // TODO: Rare
        Operator::RareList | Operator::Cl | Operator::Delete => return None,
    })
}
