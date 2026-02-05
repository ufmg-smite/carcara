use super::{Constant, Operator, ParamOperator, Rc, Term};
use rug::{Integer, Rational};
use std::collections::{HashMap, HashSet};

/// A representation of the value of an SMT-LIB/Alethe term. This is constructed by evaluating a
/// term (see [`Rc::<Term>::evaluate`]).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Value {
    Bool(bool),
    Integer(Integer),
    Real(Rational),
    String(String),
    BitVec(Integer, usize),
}

impl Value {
    /// Constructs a value from a [`Constant`].
    pub fn from_constant(c: Constant) -> Self {
        match c {
            Constant::Integer(i) => Value::Integer(i),
            Constant::Real(r) => Value::Real(r),
            Constant::String(s) => Value::String(s),
            Constant::BitVec(val, width) => Value::BitVec(val, width),
        }
    }

    /// Constructs a new bitvector value, truncating the integer `value` to `width` bits, and
    /// ensuring it is non-negative.
    pub fn new_bitvec(value: Integer, width: usize) -> Self {
        Self::BitVec(value.keep_bits(width as u32), width)
    }

    /// Tries to extract a `bool` from the value.
    pub fn as_bool(&self) -> Option<bool> {
        match self {
            Value::Bool(b) => Some(*b),
            _ => None,
        }
    }

    /// Tries to extract an [`Integer`] from the value.
    pub fn as_int(&self) -> Option<Integer> {
        match self {
            Value::Integer(i) => Some(i.clone()),
            _ => None,
        }
    }

    /// Tries to extract a [`Rational`] from the value.
    pub fn as_real(&self) -> Option<Rational> {
        match self {
            Value::Real(r) => Some(r.clone()),
            _ => None,
        }
    }

    /// Tries to extract a bitvector from the value, interpreting the bits as an unsigned integer.
    pub fn as_bitvec(&self) -> Option<(&Integer, usize)> {
        match self {
            Value::BitVec(val, width) => Some((val, *width)),
            _ => None,
        }
    }

    /// Tries to extract a bitvector from the value, interpreting the bits as a signed integer.
    pub fn as_signed_bitvec(&self) -> Option<(Integer, usize)> {
        let (val, w) = self.as_bitvec()?;
        let val = if val.get_bit((w - 1) as u32) {
            let m = Integer::from(1) << w;
            m.clone() - val
        } else {
            val.clone()
        };
        Some((val, w))
    }

    /// Constructs a constant term that corresponds to this value.
    pub fn into_term(self) -> Term {
        match self {
            Value::Bool(true) => Term::Op(Operator::True, Vec::new()),
            Value::Bool(false) => Term::Op(Operator::False, Vec::new()),
            Value::Integer(i) => Term::Const(Constant::Integer(i)),
            Value::Real(r) => Term::Const(Constant::Real(r)),
            Value::String(s) => Term::Const(Constant::String(s)),
            Value::BitVec(val, width) => Term::Const(Constant::BitVec(val, width)),
        }
    }
}

impl Rc<Term> {
    /// Tries to obtain a [`Value`] from a term by evaluating it. This will return `Some` if the
    /// term is "evaluatable".
    ///
    /// We say that a term is evaluatable if it is either:
    /// - a constant term
    /// - an application of an operator over evaluatable terms
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
            Term::ParamOp { op, op_args, args } => {
                for a in op_args.iter().chain(args) {
                    a.evaluate_impl(cache)?;
                }
                let op_args = op_args.iter().map(|a| &cache[a]).collect();
                let args = args.iter().map(|a| &cache[a]).collect();
                eval_param_op(*op, op_args, args)
            }

            Term::Var(_, _)
            | Term::App(_, _)
            | Term::Sort(_)
            | Term::Binder(_, _, _)
            | Term::Let(_, _) => None,
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
        let res = args[1..].iter().try_fold(first, |acc, arg| {
            let (arg, _) = arg.as_bitvec()?;
            Some((acc $op arg).keep_bits(w as u32))
        })?;
        Value::new_bitvec(res, w)
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

macro_rules! bitvec_comparison_op {
    ($op:tt, $args:expr, "signed") => {{
        let args = $args;
        let ((a, _), (b, _)) = (args[0].as_signed_bitvec()?, args[1].as_signed_bitvec()?);
        Value::Bool(a $op b)
    }};
    ($op:tt, $args:expr) => {{
        let args = $args;
        let ((a, _), (b, _)) = (args[0].as_bitvec()?, args[1].as_bitvec()?);
        Value::Bool(a $op b)
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
        Operator::Sub if args.len() == 1 => match args[0] {
            Value::Integer(i) => Value::Integer(-i.clone()),
            Value::Real(r) => Value::Real(-r.clone()),
            _ => return None,
        },
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
            Value::new_bitvec(!val.clone(), width)
        }
        Operator::BvNeg => {
            let (val, width) = args[0].as_bitvec()?;
            Value::new_bitvec(-val.clone(), width)
        }
        Operator::BvAnd => bitvec_op!(&, args),
        Operator::BvOr => bitvec_op!(|, args),
        Operator::BvXor => bitvec_op!(^, args),
        Operator::BvAdd => bitvec_op!(+, args),
        Operator::BvMul => bitvec_op!(*, args),
        Operator::BvSub => {
            let ((a, w), (b, _)) = (args[0].as_signed_bitvec()?, args[1].as_signed_bitvec()?);
            Value::new_bitvec(a - b, w)
        }
        Operator::BvUDiv => {
            let ((a, w), (b, _)) = (args[0].as_bitvec()?, args[1].as_bitvec()?);
            let value = if b.is_zero() {
                (Integer::from(1) << w) - 1
            } else {
                a.clone() / b
            };
            Value::new_bitvec(value, w)
        }
        Operator::BvURem => {
            let ((a, w), (b, _)) = (args[0].as_bitvec()?, args[1].as_bitvec()?);
            let value = if b.is_zero() {
                a.clone()
            } else {
                a.clone() % b
            };
            Value::new_bitvec(value, w)
        }
        Operator::BvSDiv => {
            let ((a, w), (b, _)) = (args[0].as_signed_bitvec()?, args[1].as_signed_bitvec()?);
            if b.is_zero() {
                return None;
            }
            Value::new_bitvec(a / b, w)
        }
        Operator::BvSRem | Operator::BvSMod => {
            let ((a, w), (b, _)) = (args[0].as_signed_bitvec()?, args[1].as_signed_bitvec()?);
            if b.is_zero() {
                return None;
            }
            let signum: Integer = if op == Operator::BvSRem { &a } else { &b }
                .signum_ref()
                .into();
            let value = a.abs() % b.abs();
            Value::new_bitvec(value * signum, w)
        }
        Operator::BvShl => {
            let ((a, w), (b, _)) = (args[0].as_bitvec()?, args[1].as_bitvec()?);
            Value::new_bitvec(a.clone() << b.to_usize()?, w)
        }
        Operator::BvLShr => {
            let ((a, w), (b, _)) = (args[0].as_bitvec()?, args[1].as_bitvec()?);
            Value::new_bitvec(a.clone() >> b.to_usize()?, w)
        }
        Operator::BvAShr => {
            let ((a, w), (b, _)) = (args[0].as_bitvec()?, args[1].as_bitvec()?);
            let b = b.to_usize().unwrap();
            let mut result = a.clone() >> b;
            if a.get_bit((w - 1) as u32) {
                // If the leading bit is 1, we have to fill the new bits with 1s. The mask is b 1s
                // followed by w 0s:
                // --b--|---w---
                // 11111|0000000
                let mask = ((Integer::from(1) << b) - 1) << (w - b);
                result |= mask;
            }
            Value::new_bitvec(result, w)
        }
        Operator::BvULt => bitvec_comparison_op!(<, args),
        Operator::BvULe => bitvec_comparison_op!(<=, args),
        Operator::BvUGt => bitvec_comparison_op!(>, args),
        Operator::BvUGe => bitvec_comparison_op!(>=, args),
        Operator::BvSLt => bitvec_comparison_op!(<, args, "signed"),
        Operator::BvSLe => bitvec_comparison_op!(<=, args, "signed"),
        Operator::BvSGt => bitvec_comparison_op!(>, args, "signed"),
        Operator::BvSGe => bitvec_comparison_op!(>=, args, "signed"),
        Operator::BvConcat => {
            let (value, width) = args.iter().try_fold((Integer::new(), 0), |acc, arg| {
                let (a, i) = acc;
                let (b, j) = arg.as_bitvec()?;
                Some(((a << j) + b, i + j))
            })?;
            Value::new_bitvec(value, width)
        }
        Operator::BvNAnd => {
            let ((a, w), (b, _)) = (args[0].as_bitvec()?, args[1].as_bitvec()?);
            Value::new_bitvec(!(a.clone() & b), w)
        }
        Operator::BvNOr => {
            let ((a, w), (b, _)) = (args[0].as_bitvec()?, args[1].as_bitvec()?);
            Value::new_bitvec(!(a.clone() | b), w)
        }
        Operator::BvXNor => {
            let ((a, w), (b, _)) = (args[0].as_bitvec()?, args[1].as_bitvec()?);
            Value::new_bitvec(!(a.clone() ^ b), w)
        }
        Operator::BvComp => {
            let ((a, _), (b, _)) = (args[0].as_bitvec()?, args[1].as_bitvec()?);
            Value::new_bitvec(Integer::from(if a == b { 1 } else { 0 }), 1)
        }
        Operator::UBvToInt => Value::Integer(args[0].as_bitvec()?.0.clone()),
        Operator::SBvToInt => Value::Integer(args[0].as_signed_bitvec()?.0),
        Operator::BvSize => Value::Integer(args[0].as_bitvec()?.1.into()),
        Operator::BvConst => {
            let value = args[0].as_int()?;
            let width = args[1].as_int()?.to_usize().unwrap();
            Value::new_bitvec(value, width)
        }
        Operator::BvBbTerm => {
            let width = args.len();
            let mut result = Integer::with_capacity(width);
            for (i, b) in args.into_iter().enumerate() {
                result.set_bit(i as u32, b.as_bool()?);
            }
            Value::BitVec(result, width)
        }
        Operator::BvPBbTerm => {
            let width = args.len();
            let mut result = Integer::with_capacity(width);
            for (i, b) in args.into_iter().enumerate() {
                result.set_bit(i as u32, b.as_int()? == 1);
            }
            Value::BitVec(result, width)
        }

        // TODO: Rare
        Operator::RareList | Operator::Cl | Operator::Delete => return None,
    })
}

fn eval_param_op(op: ParamOperator, op_args: Vec<&Value>, args: Vec<&Value>) -> Option<Value> {
    Some(match op {
        ParamOperator::BvExtract => {
            let i = op_args[0].as_int()?.to_usize().unwrap();
            let j = op_args[1].as_int()?.to_usize().unwrap();
            let (bits, _) = args[0].as_bitvec()?;
            let bits = bits.clone().keep_bits(i as u32) >> j;
            Value::new_bitvec(bits, i - j + 1)
        }
        ParamOperator::ZeroExtend => {
            let i = op_args[0].as_int()?.to_usize().unwrap();
            let (value, w) = args[0].as_bitvec()?;
            Value::new_bitvec(value.clone(), w + i)
        }
        ParamOperator::SignExtend => {
            let i = op_args[0].as_int()?.to_usize().unwrap();
            let (value, w) = args[0].as_signed_bitvec()?;
            Value::new_bitvec(value, w + i)
        }
        ParamOperator::RotateLeft => {
            let i = op_args[0].as_int()?.to_usize().unwrap();
            let (value, w) = args[0].as_bitvec()?;
            // A left rotation by i bits is just a right rotation by w - i bits
            Value::new_bitvec(rotate_right(value, w, w - i), w)
        }
        ParamOperator::RotateRight => {
            let i = op_args[0].as_int()?.to_usize().unwrap();
            let (value, w) = args[0].as_bitvec()?;
            Value::new_bitvec(rotate_right(value, w, i), w)
        }
        ParamOperator::Repeat => {
            let i = op_args[0].as_int()?.to_usize().unwrap();
            let (value, w) = args[0].as_bitvec()?;
            let mut result = Integer::ZERO;
            for _ in 0..i {
                result <<= w;
                result += value;
            }
            Value::new_bitvec(result, w * i)
        }
        ParamOperator::IntToBv => {
            let w = op_args[0].as_int()?.to_usize().unwrap();
            let value = args[0].as_int()?;
            Value::new_bitvec(value, w)
        }
        ParamOperator::BvConst => {
            let value = op_args[0].as_int()?;
            let w = op_args[1].as_int()?.to_usize().unwrap();
            Value::new_bitvec(value, w)
        }
        ParamOperator::BvBitOf => {
            let i = op_args[0].as_int()?.to_usize().unwrap();
            let (value, _) = args[0].as_bitvec()?;
            Value::Bool(value.get_bit(i as u32))
        }
        ParamOperator::BvIntOf => {
            let i = op_args[0].as_int()?.to_usize().unwrap();
            let (value, _) = args[0].as_bitvec()?;
            let bit = Integer::from(value.get_bit(i as u32) as usize);
            Value::Integer(bit)
        }

        // TODO: Strings, Arrays
        ParamOperator::RePower | ParamOperator::ReLoop | ParamOperator::ArrayConst => return None,
    })
}

/// Rotates a `w`-sized bitvector `r` bits to the right
fn rotate_right(value: &Integer, w: usize, r: usize) -> Integer {
    let r = r % w;
    // The least significant bits, that got rotated around
    let rotated = value.clone().keep_bits(r as u32) << (w - r);
    // The most significant bits, that only got shifted right
    let shifted = value.clone() >> r;
    rotated + shifted
}
