use super::{Constant, Operator, ParamOperator, Rc, Sort, Term, pool::Pool};
use rug::{
    Integer, Rational,
    ops::{DivRounding, RemRounding},
};
use std::collections::{HashMap, HashSet};

/// A representation of the value of an SMT-LIB/Alethe term.
///
/// This is constructed by evaluating a term (see [`Rc::<Term>::evaluate`]).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Value {
    /// A boolean value.
    Bool(bool),

    /// An integer value.
    Integer(Integer),

    /// A real value.
    Real(Rational),

    /// A string value.
    String(String),

    /// A bitvector value, represented by its integer value and width.
    BitVec(Integer, usize),
}

impl Value {
    /// Constructs a value from a [`Constant`].
    pub fn from_constant(c: Constant) -> Option<Self> {
        match c {
            Constant::Integer(i) => Some(Value::Integer(i)),
            Constant::Real(r) => Some(Value::Real(r)),
            Constant::String(s) => Some(Value::String(s)),
            Constant::RegLan(_, _) => None,
            Constant::BitVec(val, width) => Some(Value::BitVec(val, width)),
        }
    }

    /// Tries to construct a value from a term, return `None` if it is not possible.
    pub fn from_term(t: &Rc<Term>) -> Option<Self> {
        match t.as_ref() {
            Term::Const(c) => Value::from_constant(c.clone()),
            Term::Op(Operator::True, _) => Some(Value::Bool(true)),
            Term::Op(Operator::False, _) => Some(Value::Bool(false)),
            _ => None,
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

    /// Tries to extract a [`&str`] from the value.
    pub fn as_str(&self) -> Option<&str> {
        match self {
            Value::String(s) => Some(s),
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

    /// Tries to extract a bitvector from the value, interpreting the bits as a signed integer in
    /// two's complement.
    pub fn as_signed_bitvec(&self) -> Option<(Integer, usize)> {
        let (val, w) = self.as_bitvec()?;
        if w == 0 {
            return None;
        }
        let val = if val.get_bit((w - 1) as u32) {
            val.clone() - (Integer::from(1) << w)
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
    /// Tries to obtain a value from a term by evaluating it.
    ///
    /// If this term is *evaluatable*, this will return a constant term corresponding to this value.
    /// Otherwise, this returns a partially evaluated term.
    ///
    /// We say that a term is evaluatable if it is either:
    /// - a constant term
    /// - an application of an operator over evaluatable terms
    pub fn evaluate(&self, pool: &mut Pool) -> Rc<Term> {
        self.evaluate_impl(&mut HashMap::new(), pool).clone()
    }

    fn evaluate_impl<'t, 'c>(
        &'t self,
        cache: &'c mut HashMap<&'t Rc<Term>, Rc<Term>>,
        pool: &mut Pool,
    ) -> &'c Rc<Term> {
        if cache.contains_key(self) {
            return &cache[self];
        }

        let result = match self.as_ref() {
            Term::Const(c) => Value::from_constant(c.clone())
                .map_or_else(|| Term::Const(c.clone()), Value::into_term),
            Term::Op(op, args) => {
                let args: Vec<_> = args
                    .iter()
                    .map(|a| a.evaluate_impl(cache, pool).clone())
                    .collect();
                eval_op(pool, *op, &args).map_or_else(|| Term::Op(*op, args), Value::into_term)
            }
            Term::ParamOp { op, op_args, args } => {
                let op_args: Vec<_> = op_args
                    .iter()
                    .map(|a| a.evaluate_impl(cache, pool).clone())
                    .collect();
                let args: Vec<_> = args
                    .iter()
                    .map(|a| a.evaluate_impl(cache, pool).clone())
                    .collect();

                eval_param_op(*op, &op_args, &args).map_or_else(
                    || Term::ParamOp { op: *op, op_args, args },
                    Value::into_term,
                )
            }
            // TODO: qualified operators, `match`, `let`
            Term::Var(_, _)
            | Term::App(_, _)
            | Term::Binder(_, _, _)
            | Term::Let(_, _)
            | Term::AsOp(_, _, _)
            | Term::Match(_, _) => {
                cache.insert(self, self.clone());
                return cache.get(self).unwrap();
            }
        };
        cache.insert(self, pool.add(result));
        cache.get(self).unwrap()
    }
}

macro_rules! mixed_type_arith {
    ($op:tt, $a:expr, $b:expr, $is_real:expr) => {
        match ($a, $b) {
            (Value::Integer(l), Value::Integer(r)) if $is_real => {
                let (l, r) = (Rational::from(l), Rational::from(r));
                Some(Value::Real(l $op r))
            }
            (Value::Integer(l), Value::Integer(r)) => Some(Value::Integer(l $op r)),
            (Value::Integer(l), Value::Real(r)) => Some(Value::Real(Rational::from(l) $op r)),
            (Value::Real(l), Value::Integer(r)) => Some(Value::Real(l $op Rational::from(r))),
            (Value::Real(l), Value::Real(r)) => Some(Value::Real(l $op r)),
            _ => None,
        }
    };
}

macro_rules! arith_op {
    ($op:tt, $args:expr $(, $flag:literal)?) => {{
        let args = $args;
        let first = args[0].as_ref()?.clone();
        if !matches!(first, Value::Integer(_) | Value::Real(_)) {
            return None;
        }
        // Hacky way to set `real` to `true` if the "real" flag is passed
        let real = $($flag == "real" ||)? false;
        args[1..]
            .iter()
            .try_fold(first, |acc, arg| mixed_type_arith!($op, acc, arg.as_ref()?, real))?
    }};
}

macro_rules! bitvec_op {
    ($op:tt, $args:expr) => {{
        let args = $args;
        let Value::BitVec(first, w) = args[0].as_ref()?.clone() else {
            return None;
        };
        let res = args[1..].iter().try_fold(first, |acc, arg| {
            let (arg, _) = arg.as_ref()?.as_bitvec()?;
            Some((acc $op arg).keep_bits(w as u32))
        })?;
        Value::new_bitvec(res, w)
    }};
}

macro_rules! comparison_op {
    ($op:tt, $args:expr) => {{
        fn compare(window: &[Option<Value>]) -> Option<bool> {
            match window {
                [Some(Value::Integer(l)), Some(Value::Integer(r))] => Some(l $op r),
                [Some(Value::Integer(l)), Some(Value::Real(r))] => Some(l $op r),
                [Some(Value::Real(l)), Some(Value::Integer(r))] => Some(l $op r),
                [Some(Value::Real(l)), Some(Value::Real(r))] => Some(l $op r),
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
        let ((a, _), (b, _)) = (
            args[0].as_ref()?.as_signed_bitvec()?,
            args[1].as_ref()?.as_signed_bitvec()?,
        );
        Value::Bool(a $op b)
    }};
    ($op:tt, $args:expr) => {{
        let args = $args;
        let ((a, _), (b, _)) = (
            args[0].as_ref()?.as_bitvec()?,
            args[1].as_ref()?.as_bitvec()?,
        );
        Value::Bool(a $op b)
    }};
}

fn eval_op(pool: &mut Pool, op: Operator, arg_terms: &[Rc<Term>]) -> Option<Value> {
    let args: Vec<_> = arg_terms.iter().map(Value::from_term).collect();
    Some(match op {
        Operator::True => Value::Bool(true),
        Operator::False => Value::Bool(false),
        Operator::Not => Value::Bool(!args[0].as_ref()?.as_bool()?),
        Operator::Implies => {
            let left = args[0..args.len() - 1]
                .iter()
                .try_fold(false, |acc, arg| Some(acc || !arg.as_ref()?.as_bool()?))?;
            let right = args.last().unwrap().as_ref()?.as_bool()?;
            Value::Bool(left || right)
        }
        Operator::And => Value::Bool(
            args.iter()
                .try_fold(true, |acc, arg| Some(acc && arg.as_ref()?.as_bool()?))?,
        ),
        Operator::Or => Value::Bool(
            args.iter()
                .try_fold(false, |acc, arg| Some(acc || arg.as_ref()?.as_bool()?))?,
        ),
        Operator::Xor => Value::Bool(
            args.iter()
                .try_fold(false, |acc, arg| Some(acc != arg.as_ref()?.as_bool()?))?,
        ),
        Operator::Equals => {
            let result = 'block: {
                for w in args.windows(2) {
                    if w[0].as_ref()? != w[1].as_ref()? {
                        break 'block false;
                    }
                }
                true
            };
            Value::Bool(result)
        }
        Operator::Distinct => {
            let n = args.len();
            let set: HashSet<Value> = args.into_iter().collect::<Option<_>>()?;
            Value::Bool(set.len() == n)
        }
        Operator::Ite => {
            if args[0].as_ref()?.as_bool()? {
                args[1].as_ref()?.clone()
            } else {
                args[2].as_ref()?.clone()
            }
        }
        Operator::Add => arith_op!(+, args),
        Operator::Sub if args.len() == 1 => match args[0].as_ref()? {
            Value::Integer(i) => Value::Integer(-i.clone()),
            Value::Real(r) => Value::Real(-r.clone()),
            _ => return None,
        },
        Operator::Sub => arith_op!(-, args),
        Operator::Mult => arith_op!(*, args),
        // SMT-LIB defines `div` and `mod` using Euclidean division. Division by zero is left
        // unspecified, so we don't evaluate it
        Operator::IntDiv => {
            let first = args[0].as_ref()?.as_int()?;
            Value::Integer(args[1..].iter().try_fold(first, |acc, arg| {
                let d = arg.as_ref()?.as_int()?;
                (!d.is_zero()).then(|| acc.div_euc(d))
            })?)
        }
        Operator::RealDiv => {
            let divisor_is_zero = |arg: &Option<Value>| match arg {
                Some(Value::Integer(i)) => i.is_zero(),
                Some(Value::Real(r)) => r.is_zero(),
                _ => false,
            };
            if args[1..].iter().any(divisor_is_zero) {
                return None;
            }
            arith_op!(/, args, "real")
        }
        Operator::Mod => {
            let (a, b) = (args[0].as_ref()?.as_int()?, args[1].as_ref()?.as_int()?);
            if b.is_zero() {
                return None;
            }
            Value::Integer(a.rem_euc(b))
        }
        Operator::Abs => match &args[0].as_ref()? {
            Value::Integer(i) => Value::Integer(i.clone().abs()),
            Value::Real(r) => Value::Real(r.clone().abs()),
            _ => return None,
        },
        Operator::Pow2 => {
            let v = args[0].as_ref()?.as_int()?;
            if v < 0 {
                return Some(Value::Integer(Integer::from(0)));
            }
            let v = v.to_usize()?;
            Value::Integer(Integer::from(1) << v)
        }
        Operator::Log2 => {
            let v = args[0].as_ref()?.as_int()?;
            if v <= 0 {
                Value::Integer(Integer::from(0))
            } else {
                Value::Integer(Integer::from(v.significant_bits() - 1))
            }
        }
        Operator::IsPow2 => {
            let v = args[0].as_ref()?.as_int()?;
            Value::Bool(v.is_power_of_two())
        }

        // TODO: Transcendentals
        Operator::RealPi
        | Operator::Sqrt
        | Operator::Exp
        | Operator::Sin
        | Operator::Cos
        | Operator::Tan
        | Operator::Csc
        | Operator::Sec
        | Operator::Cot
        | Operator::Arcsin
        | Operator::Arccos
        | Operator::Arctan
        | Operator::Arccsc
        | Operator::Arcsec
        | Operator::Arccot => return None,

        Operator::LessThan => comparison_op!(<, args),
        Operator::GreaterThan => comparison_op!(>, args),
        Operator::LessEq => comparison_op!(<=, args),
        Operator::GreaterEq => comparison_op!(>=, args),

        Operator::ToReal => Value::Real(args[0].as_ref()?.as_int()?.into()),
        Operator::ToInt => {
            Value::Integer(args[0].as_ref()?.as_real()?.floor().into_numer_denom().0)
        }
        Operator::IsInt => Value::Bool(args[0].as_ref()?.as_real()?.is_integer()),

        // TODO: Arrays
        Operator::Select | Operator::Store => return None,

        Operator::StrConcat => {
            let mut result = String::new();
            for a in args {
                result += a.as_ref()?.as_str()?;
            }
            Value::String(result)
        }
        Operator::StrLen => Value::Integer(args[0].as_ref()?.as_str()?.chars().count().into()),
        Operator::StrLessThan => {
            let a = args[0].as_ref()?.as_str()?;
            let b = args[1].as_ref()?.as_str()?;
            Value::Bool(a < b)
        }
        Operator::StrLessEq => {
            let a = args[0].as_ref()?.as_str()?;
            let b = args[1].as_ref()?.as_str()?;
            Value::Bool(a <= b)
        }
        Operator::CharAt => {
            let s = args[0].as_ref()?.as_str()?;
            let Some(i) = args[1].as_ref()?.as_int()?.to_usize() else {
                return Some(Value::String(String::new()));
            };
            s.chars().nth(i).map_or(Value::String(String::new()), |ch| {
                Value::String(ch.to_string())
            })
        }
        Operator::Substring => {
            let a = args[0].as_ref()?.as_str()?;
            let Some(i) = args[1].as_ref()?.as_int()?.to_usize() else {
                // If `i` is too large, we return the empty string
                return Some(Value::String(String::new()));
            };
            let n = args[2].as_ref()?.as_int()?;
            if n.is_negative() {
                return Some(Value::String(String::new()));
            }
            // If `n` is too large however, we truncate
            let n = n.to_usize().unwrap_or(usize::MAX);
            Value::String(a.chars().skip(i).take(n).collect())
        }
        Operator::PrefixOf => {
            let a = args[0].as_ref()?.as_str()?;
            let b = args[1].as_ref()?.as_str()?;
            Value::Bool(b.strip_prefix(a).is_some())
        }
        Operator::SuffixOf => {
            let a = args[0].as_ref()?.as_str()?;
            let b = args[1].as_ref()?.as_str()?;
            Value::Bool(b.strip_suffix(a).is_some())
        }
        Operator::Contains => {
            let a = args[0].as_ref()?.as_str()?;
            let b = args[1].as_ref()?.as_str()?;
            Value::Bool(a.contains(b))
        }
        Operator::IndexOf => {
            let a = args[0].as_ref()?.as_str()?;
            let b = args[1].as_ref()?.as_str()?;
            let Some(i) = args[2].as_ref()?.as_int()?.to_usize() else {
                // If `i` is too large, we return -1
                return Some(Value::Integer(Integer::from(-1)));
            };
            if i > a.chars().count() {
                return Some(Value::Integer(Integer::from(-1)));
            }
            let trimmed: String = a.chars().skip(i).collect();
            let Some(index_found) = trimmed.find(b) else {
                // If we don't find it, return -1
                return Some(Value::Integer(Integer::from(-1)));
            };
            // `find` returns a byte offset, but string indices in SMT-LIB count characters
            let index_found = trimmed[..index_found].chars().count();
            Value::Integer(Integer::from(i + index_found))
        }
        Operator::IndexOfRe
        | Operator::Replace
        | Operator::ReplaceAll
        | Operator::ReplaceRe
        | Operator::ReplaceReAll
        | Operator::StrIsDigit => return None, // TODO
        Operator::StrToCode => {
            // If the string doesn't have exactly one character, the result is -1
            let mut chars = args[0].as_ref()?.as_str()?.chars();
            match (chars.next(), chars.next()) {
                (Some(c), None) => Value::Integer(Integer::from(c as u32)),
                _ => Value::Integer(Integer::from(-1)),
            }
        }
        Operator::StrFromCode => {
            let code = args[0].as_ref()?.as_int()?;

            // SMT-LIB only recognizes the planes 0 to 2 of Unicode, meaning values up to 0x2FFFF.
            // Invalid values become the empty string.
            let string = if code.is_negative() || code > 0x2FFFF {
                String::new()
            } else {
                // Surrogate code points can't be represented as a Rust `char`, so we don't
                // evaluate them
                char::from_u32(code.to_u32()?)?.to_string()
            };
            Value::String(string)
        }
        Operator::StrToInt => return None, // TODO
        Operator::StrFromInt => {
            // Negative integers are converted to the empty string
            let i = args[0].as_ref()?.as_int()?;
            Value::String(if i.is_negative() {
                String::new()
            } else {
                i.to_string()
            })
        }

        // TODO: Regular expressions
        Operator::StrToRe
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
        | Operator::ReRange
        | Operator::ReFromAutomaton => return None,

        // Bitvectors
        Operator::BvNot => {
            let (val, width) = args[0].as_ref()?.as_bitvec()?;
            Value::new_bitvec(!val.clone(), width)
        }
        Operator::BvNeg => {
            let (val, width) = args[0].as_ref()?.as_bitvec()?;
            Value::new_bitvec(-val.clone(), width)
        }
        Operator::BvAnd => bitvec_op!(&, args),
        Operator::BvOr => bitvec_op!(|, args),
        Operator::BvXor => bitvec_op!(^, args),
        Operator::BvAdd => bitvec_op!(+, args),
        Operator::BvMul => bitvec_op!(*, args),
        Operator::BvSub => bitvec_op!(-, args),
        Operator::BvUDiv => {
            let ((a, w), (b, _)) = (
                args[0].as_ref()?.as_bitvec()?,
                args[1].as_ref()?.as_bitvec()?,
            );
            let value = if b.is_zero() {
                (Integer::from(1) << w) - 1
            } else {
                a.clone() / b
            };
            Value::new_bitvec(value, w)
        }
        Operator::BvURem => {
            let ((a, w), (b, _)) = (
                args[0].as_ref()?.as_bitvec()?,
                args[1].as_ref()?.as_bitvec()?,
            );
            let value = if b.is_zero() {
                a.clone()
            } else {
                a.clone() % b
            };
            Value::new_bitvec(value, w)
        }
        // The signed division operators are defined in SMT-LIB in terms of `bvudiv` and `bvurem`.
        // In particular, this determines the result when the divisor is zero
        Operator::BvSDiv => {
            let ((a, w), (b, _)) = (
                args[0].as_ref()?.as_signed_bitvec()?,
                args[1].as_ref()?.as_signed_bitvec()?,
            );
            let value = if b.is_zero() {
                // `bvudiv` by zero is all ones, so this is either -1 or its negation
                Integer::from(if a.is_negative() { 1 } else { -1 })
            } else {
                // Truncating division
                a / b
            };
            Value::new_bitvec(value, w)
        }
        Operator::BvSRem | Operator::BvSMod => {
            let ((a, w), (b, _)) = (
                args[0].as_ref()?.as_signed_bitvec()?,
                args[1].as_ref()?.as_signed_bitvec()?,
            );
            let value = if b.is_zero() {
                a
            } else if op == Operator::BvSRem {
                a % b
            } else {
                a.rem_floor(b)
            };
            Value::new_bitvec(value, w)
        }
        Operator::BvShl => {
            let ((a, w), (b, _)) = (
                args[0].as_ref()?.as_bitvec()?,
                args[1].as_ref()?.as_bitvec()?,
            );
            match b.to_usize() {
                Some(b) if b < w => Value::new_bitvec(a.clone() << b, w),
                _ => Value::new_bitvec(Integer::ZERO, w),
            }
        }
        Operator::BvLShr => {
            let ((a, w), (b, _)) = (
                args[0].as_ref()?.as_bitvec()?,
                args[1].as_ref()?.as_bitvec()?,
            );
            match b.to_usize() {
                Some(b) if b < w => Value::new_bitvec(a.clone() >> b, w),
                _ => Value::new_bitvec(Integer::ZERO, w),
            }
        }
        Operator::BvAShr => {
            let ((a, w), (b, _)) = (
                args[0].as_ref()?.as_bitvec()?,
                args[1].as_ref()?.as_bitvec()?,
            );
            if w == 0 {
                return None;
            }
            // Shifting by `w` or more bits is the same as shifting by `w` bits
            let b = b.to_usize().map_or(w, |b| b.min(w));
            let mut result = a.clone() >> b;
            if a.get_bit((w - 1) as u32) {
                // If the leading bit is 1, we have to fill the new bits with 1s. The mask is b 1s
                // followed by w - b 0s:
                // |----w----|
                // |-b-|
                // 11111000000
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
                let (b, j) = arg.as_ref()?.as_bitvec()?;
                Some(((a << j) + b, i + j))
            })?;
            Value::new_bitvec(value, width)
        }
        Operator::BvNAnd => {
            let ((a, w), (b, _)) = (
                args[0].as_ref()?.as_bitvec()?,
                args[1].as_ref()?.as_bitvec()?,
            );
            Value::new_bitvec(!(a.clone() & b), w)
        }
        Operator::BvNOr => {
            let ((a, w), (b, _)) = (
                args[0].as_ref()?.as_bitvec()?,
                args[1].as_ref()?.as_bitvec()?,
            );
            Value::new_bitvec(!(a.clone() | b), w)
        }
        Operator::BvXNor => {
            let ((a, w), (b, _)) = (
                args[0].as_ref()?.as_bitvec()?,
                args[1].as_ref()?.as_bitvec()?,
            );
            Value::new_bitvec(!(a.clone() ^ b), w)
        }
        Operator::BvComp => {
            let ((a, _), (b, _)) = (
                args[0].as_ref()?.as_bitvec()?,
                args[1].as_ref()?.as_bitvec()?,
            );
            Value::new_bitvec(Integer::from(if a == b { 1 } else { 0 }), 1)
        }
        Operator::UBvToInt => Value::Integer(args[0].as_ref()?.as_bitvec()?.0.clone()),
        Operator::SBvToInt => Value::Integer(args[0].as_ref()?.as_signed_bitvec()?.0),
        Operator::BvSize => match pool.sort(&arg_terms[0]).as_ref() {
            Sort::BitVec(width) => Value::Integer(Integer::from(*width)),
            _ => return None,
        },
        Operator::BvConst => {
            let value = args[0].as_ref()?.as_int()?;
            let width = args[1].as_ref()?.as_int()?.to_usize()?;
            Value::new_bitvec(value, width)
        }
        Operator::BvBbTerm => {
            let width = args.len();
            let mut result = Integer::with_capacity(width);
            for (i, b) in args.into_iter().enumerate() {
                result.set_bit(i as u32, b?.as_bool()?);
            }
            Value::BitVec(result, width)
        }
        Operator::BvPBbTerm => {
            let width = args.len();
            let mut result = Integer::with_capacity(width);
            for (i, b) in args.into_iter().enumerate() {
                result.set_bit(i as u32, b?.as_int()? == 1);
            }
            Value::BitVec(result, width)
        }
        Operator::BvIte => {
            let (cond, _) = args[0].as_ref()?.as_bitvec()?;
            if *cond == 1 {
                args[1].as_ref()?.clone()
            } else {
                args[2].as_ref()?.clone()
            }
        }

        // TODO: Rare
        Operator::RareList | Operator::Cl | Operator::Delete => return None,

        // TODO: Sets and relations
        Operator::SetUnion
        | Operator::SetInter
        | Operator::SetMinus
        | Operator::SetMember
        | Operator::SetSubset
        | Operator::SetSingleton
        | Operator::SetIsEmpty
        | Operator::SetIsSingleton
        | Operator::SetCard
        | Operator::SetInsert
        | Operator::SetComplement
        | Operator::Tuple
        | Operator::TupleUnit
        | Operator::RelTranspose
        | Operator::RelTclosure
        | Operator::RelJoin
        | Operator::RelProduct => return None,
    })
}

fn eval_param_op(op: ParamOperator, op_args: &[Rc<Term>], args: &[Rc<Term>]) -> Option<Value> {
    let op_args: Vec<_> = op_args
        .iter()
        .map(Value::from_term)
        .collect::<Option<_>>()?;

    let args: Vec<_> = args.iter().map(Value::from_term).collect::<Option<_>>()?;

    Some(match op {
        ParamOperator::BvExtract => {
            let i = op_args[0].as_int()?.to_usize()?;
            let j = op_args[1].as_int()?.to_usize()?;
            if j > i {
                return None;
            }
            let (bits, _) = args[0].as_bitvec()?;
            let bits = bits.clone().keep_bits(i as u32 + 1) >> j;
            Value::new_bitvec(bits, i - j + 1)
        }
        ParamOperator::ZeroExtend => {
            let i = op_args[0].as_int()?.to_usize()?;
            let (value, w) = args[0].as_bitvec()?;
            Value::new_bitvec(value.clone(), w + i)
        }
        ParamOperator::SignExtend => {
            let i = op_args[0].as_int()?.to_usize()?;
            let (value, w) = args[0].as_signed_bitvec()?;
            Value::new_bitvec(value, w + i)
        }
        ParamOperator::RotateLeft => {
            let i = op_args[0].as_int()?.to_usize()?;
            let (value, w) = args[0].as_bitvec()?;
            if w == 0 {
                return None;
            }
            // A left rotation by i bits is just a right rotation by w - i bits
            Value::new_bitvec(rotate_right(value, w, w - i % w), w)
        }
        ParamOperator::RotateRight => {
            let i = op_args[0].as_int()?.to_usize()?;
            let (value, w) = args[0].as_bitvec()?;
            if w == 0 {
                return None;
            }
            Value::new_bitvec(rotate_right(value, w, i), w)
        }
        ParamOperator::Repeat => {
            let i = op_args[0].as_int()?.to_usize()?;
            let (value, w) = args[0].as_bitvec()?;
            let mut result = Integer::ZERO;
            for _ in 0..i {
                result <<= w;
                result += value;
            }
            Value::new_bitvec(result, w * i)
        }
        ParamOperator::IntToBv => {
            let w = op_args[0].as_int()?.to_usize()?;
            let value = args[0].as_int()?;
            Value::new_bitvec(value, w)
        }
        ParamOperator::BvConst => {
            let value = op_args[0].as_int()?;
            let w = op_args[1].as_int()?.to_usize()?;
            Value::new_bitvec(value, w)
        }
        ParamOperator::BvBitOf => {
            let i = op_args[0].as_int()?.to_usize()?;
            let (value, _) = args[0].as_bitvec()?;
            Value::Bool(value.get_bit(i as u32))
        }
        ParamOperator::BvIntOf => {
            let i = op_args[0].as_int()?.to_usize()?;
            let (value, _) = args[0].as_bitvec()?;
            let bit = Integer::from(value.get_bit(i as u32) as usize);
            Value::Integer(bit)
        }

        // TODO: Strings, datatypes, sets and relations
        ParamOperator::RePower
        | ParamOperator::ReLoop
        | ParamOperator::Tester
        | ParamOperator::TupleSelect => return None,
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

#[cfg(test)]
mod tests {
    use crate::ast::pool::Pool;
    use crate::parser::tests::parse_terms;

    /// Checks that each term evaluates to the expected result.
    fn run_tests(cases: &[(&str, &str)]) {
        let definitions = "
            (declare-const x Int)
            (declare-const s String)
            (declare-const b (_ BitVec 4))
        ";
        for &(term, expected) in cases {
            let mut pool = Pool::new();
            let [term, expected] = parse_terms(&mut pool, definitions, [term, expected]);
            assert_eq!(expected.evaluate(&mut pool), term.evaluate(&mut pool));
        }
    }

    #[test]
    fn booleans() {
        run_tests(&[
            ("(not true)", "false"),
            ("(and true true false)", "false"),
            ("(or false false true)", "true"),
            ("(xor true true true)", "true"),
            ("(=> true false)", "false"),
            ("(=> false false false)", "true"),
            ("(= 1 1 1)", "true"),
            ("(= 1 1 2)", "false"),
            ("(distinct 1 2 3)", "true"),
            ("(distinct 1 2 1)", "false"),
            ("(ite false 1 2)", "2"),
        ]);
    }

    #[test]
    fn arithmetic() {
        run_tests(&[
            ("(+ 1 2 3)", "6"),
            ("(- 5)", "(- 5)"),
            ("(- 5 2 1)", "2"),
            ("(* 2 3 4)", "24"),
            ("(+ 1.5 1.0)", "2.5"),
            ("(/ 1.0 4.0)", "0.25"),
            ("(/ 1.0 2.0 2.0)", "0.25"),
            ("(abs (- 3))", "3"),
            ("(< 1 2 3)", "true"),
            ("(< 1 3 2)", "false"),
            ("(>= 2.0 2.0)", "true"),
            ("(to_real 3)", "3.0"),
            ("(to_int 2.5)", "2"),
            ("(to_int (- 2.5))", "(- 3)"),
            ("(is_int 2.0)", "true"),
            ("(is_int 2.5)", "false"),
        ]);
    }

    #[test]
    fn div_and_mod() {
        // `div` and `mod` use Euclidean division, so the remainder is never negative
        run_tests(&[
            ("(div 7 2)", "3"),
            ("(mod 7 2)", "1"),
            ("(div (- 7) 2)", "(- 4)"),
            ("(mod (- 7) 2)", "1"),
            ("(div 7 (- 2))", "(- 3)"),
            ("(mod 7 (- 2))", "1"),
            ("(div (- 7) (- 2))", "4"),
            ("(mod (- 7) (- 2))", "1"),
            ("(mod (- 6) 3)", "0"),
            ("(div 100 3 4)", "8"),
        ]);

        // Division by zero is unspecified, so it should not be evaluated
        run_tests(&[
            ("(div 1 0)", "(div 1 0)"),
            ("(mod 1 0)", "(mod 1 0)"),
            ("(/ 1.0 0.0)", "(/ 1.0 0.0)"),
        ]);
    }

    #[test]
    fn strings() {
        run_tests(&[
            (r#"(str.++ "a" "b" "c")"#, r#""abc""#),
            (r#"(str.len "abc")"#, "3"),
            (r#"(str.< "a" "b")"#, "true"),
            (r#"(str.< "b" "a")"#, "false"),
            (r#"(str.< "a" "a")"#, "false"),
            (r#"(str.< "a" "ab")"#, "true"),
            (r#"(str.<= "a" "a")"#, "true"),
            (r#"(str.<= "b" "a")"#, "false"),
            (r#"(str.at "abc" 1)"#, r#""b""#),
            (r#"(str.at "abc" 3)"#, r#""""#),
            (r#"(str.at "abc" (- 1))"#, r#""""#),
            (r#"(str.substr "abcde" 1 3)"#, r#""bcd""#),
            (r#"(str.substr "abcde" 1 10)"#, r#""bcde""#),
            (r#"(str.substr "abcde" 1 (- 1))"#, r#""""#),
            (r#"(str.substr "abcde" (- 1) 2)"#, r#""""#),
            (r#"(str.prefixof "ab" "abc")"#, "true"),
            (r#"(str.prefixof "bc" "abc")"#, "false"),
            (r#"(str.suffixof "bc" "abc")"#, "true"),
            (r#"(str.contains "abc" "b")"#, "true"),
            (r#"(str.contains "abc" "d")"#, "false"),
            (r#"(str.indexof "abcabc" "c" 0)"#, "2"),
            (r#"(str.indexof "abcabc" "c" 3)"#, "5"),
            (r#"(str.indexof "abc" "d" 0)"#, "(- 1)"),
            (r#"(str.indexof "abc" "a" 4)"#, "(- 1)"),
            (r#"(str.indexof "abc" "" 3)"#, "3"),
            (r#"(str.to_code "a")"#, "97"),
            (r#"(str.to_code "")"#, "(- 1)"),
            (r#"(str.to_code "ab")"#, "(- 1)"),
            ("(str.from_code 97)", r#""a""#),
            ("(str.from_code (- 1))", r#""""#),
            ("(str.from_code 196608)", r#""""#),
            ("(str.from_int 42)", r#""42""#),
            ("(str.from_int (- 42))", r#""""#),
        ]);

        // Strings with non-ASCII characters
        run_tests(&[
            (r#"(str.len "\u{e9}t\u{e9}")"#, "3"),
            (r#"(str.at "\u{e9}t\u{e9}" 1)"#, r#""t""#),
            (r#"(str.indexof "\u{e9}t\u{e9}" "t" 0)"#, "1"),
            (r#"(str.indexof "\u{e9}t\u{e9}t" "t" 2)"#, "3"),
            (r#"(str.to_code "\u{e9}")"#, "233"),
            // Surrogate code points can't be represented, so they are not evaluated
            ("(str.from_code 55296)", "(str.from_code 55296)"),
        ]);
    }

    #[test]
    fn bitvectors() {
        run_tests(&[
            ("(bvnot #b0101)", "#b1010"),
            ("(bvneg #b0001)", "#b1111"),
            ("(bvand #b1100 #b1010)", "#b1000"),
            ("(bvor #b1100 #b1010)", "#b1110"),
            ("(bvxor #b1100 #b1010)", "#b0110"),
            ("(bvnand #b1100 #b1010)", "#b0111"),
            ("(bvnor #b1100 #b1010)", "#b0001"),
            ("(bvxnor #b1100 #b1010)", "#b1001"),
            ("(bvadd #b1111 #b0010)", "#b0001"),
            ("(bvmul #b0110 #b0011)", "#b0010"),
            ("(bvsub #b0001 #b0010)", "#b1111"),
            ("(bvsub #b1000 #b0001)", "#b0111"),
            ("(bvcomp #b1010 #b1010)", "#b1"),
            ("(bvcomp #b1010 #b1011)", "#b0"),
            ("(concat #b10 #b01 #b1)", "#b10011"),
            ("(ubv_to_int #b1111)", "15"),
            ("(sbv_to_int #b1111)", "(- 1)"),
            ("(sbv_to_int #b1000)", "(- 8)"),
            ("(sbv_to_int #b0111)", "7"),
            ("(@bvsize b)", "4"),
        ]);
    }

    #[test]
    fn bitvector_comparisons() {
        run_tests(&[
            ("(bvult #b0001 #b1111)", "true"),
            ("(bvule #b1111 #b1111)", "true"),
            ("(bvugt #b0001 #b1111)", "false"),
            ("(bvuge #b0001 #b1111)", "false"),
            // #b1111 is -1 and #b0001 is 1
            ("(bvslt #b1111 #b0001)", "true"),
            ("(bvslt #b0001 #b1111)", "false"),
            ("(bvsle #b1111 #b1111)", "true"),
            ("(bvsgt #b0001 #b1111)", "true"),
            ("(bvsge #b1000 #b0111)", "false"),
            // #b1000 (-8) is the smallest signed 4-bit value
            ("(bvslt #b1000 #b1111)", "true"),
        ]);
    }

    #[test]
    fn bitvector_division() {
        run_tests(&[
            ("(bvudiv #b0111 #b0010)", "#b0011"),
            ("(bvudiv #b0111 #b0000)", "#b1111"),
            ("(bvurem #b0111 #b0010)", "#b0001"),
            ("(bvurem #b0111 #b0000)", "#b0111"),
            // 7 / 2, -7 / 2, 7 / -2, -7 / -2
            ("(bvsdiv #b0111 #b0010)", "#b0011"),
            ("(bvsdiv #b1001 #b0010)", "#b1101"),
            ("(bvsdiv #b0111 #b1110)", "#b1101"),
            ("(bvsdiv #b1001 #b1110)", "#b0011"),
            // Overflow: -8 / -1 = 8, which wraps around to -8
            ("(bvsdiv #b1000 #b1111)", "#b1000"),
            // Division by zero is -1 if the dividend is non-negative, and 1 otherwise
            ("(bvsdiv #b0111 #b0000)", "#b1111"),
            ("(bvsdiv #b1001 #b0000)", "#b0001"),
            // The sign of `bvsrem` follows the dividend
            ("(bvsrem #b0111 #b0010)", "#b0001"),
            ("(bvsrem #b1001 #b0010)", "#b1111"),
            ("(bvsrem #b0111 #b1110)", "#b0001"),
            ("(bvsrem #b1001 #b1110)", "#b1111"),
            ("(bvsrem #b1001 #b0000)", "#b1001"),
            // The sign of `bvsmod` follows the divisor
            ("(bvsmod #b0111 #b0010)", "#b0001"),
            ("(bvsmod #b1001 #b0010)", "#b0001"),
            ("(bvsmod #b0111 #b1110)", "#b1111"),
            ("(bvsmod #b1001 #b1110)", "#b1111"),
            ("(bvsmod #b1011 #b0100)", "#b0011"),
            ("(bvsmod #b1100 #b0100)", "#b0000"),
            ("(bvsmod #b1001 #b0000)", "#b1001"),
        ]);
    }

    #[test]
    fn bitvector_shifts() {
        run_tests(&[
            ("(bvshl #b0011 #b0001)", "#b0110"),
            ("(bvshl #b0011 #b0011)", "#b1000"),
            ("(bvshl #b0011 #b0100)", "#b0000"),
            ("(bvshl #b0011 #b1111)", "#b0000"),
            ("(bvlshr #b1100 #b0001)", "#b0110"),
            ("(bvlshr #b1100 #b0100)", "#b0000"),
            ("(bvlshr #b1100 #b1111)", "#b0000"),
            ("(bvashr #b1100 #b0001)", "#b1110"),
            ("(bvashr #b0100 #b0001)", "#b0010"),
            ("(bvashr #b1000 #b0100)", "#b1111"),
            ("(bvashr #b1000 #b1111)", "#b1111"),
            ("(bvashr #b0111 #b1111)", "#b0000"),
            // Large shifts (bigger than usize)
            ("(bvshl (@bv 1 65) (bvnot (@bv 0 65)))", "(@bv 0 65)"),
            ("(bvlshr (@bv 1 65) (bvnot (@bv 0 65)))", "(@bv 0 65)"),
        ]);
    }

    #[test]
    fn indexed_bitvector_operators() {
        run_tests(&[
            ("((_ extract 2 1) #b0110)", "#b11"),
            ("((_ extract 0 0) #b0001)", "#b1"),
            ("((_ extract 3 0) #b1010)", "#b1010"),
            ("((_ zero_extend 2) #b11)", "#b0011"),
            ("((_ sign_extend 2) #b10)", "#b1110"),
            ("((_ sign_extend 2) #b01)", "#b0001"),
            ("((_ sign_extend 0) #b10)", "#b10"),
            ("((_ rotate_left 1) #b1001)", "#b0011"),
            ("((_ rotate_left 4) #b1001)", "#b1001"),
            ("((_ rotate_left 5) #b1001)", "#b0011"),
            ("((_ rotate_right 1) #b1001)", "#b1100"),
            ("((_ rotate_right 5) #b1001)", "#b1100"),
            ("((_ repeat 3) #b10)", "#b101010"),
            ("((_ int_to_bv 4) 18)", "#b0010"),
            ("((_ int_to_bv 4) (- 1))", "#b1111"),
            ("(_ bv5 4)", "#b0101"),
        ]);
    }

    #[test]
    fn partial_evaluation() {
        run_tests(&[
            ("(+ x (+ 1 1))", "(+ x 2)"),
            ("(and (= x 0) (not false))", "(and (= x 0) true)"),
            (r#"(str.++ s (str.++ "a" "b"))"#, r#"(str.++ s "ab")"#),
            ("(bvadd b (bvadd #b0001 #b0001))", "(bvadd b #b0010)"),
            (
                "(forall ((y Int)) (= y (+ 1 1)))",
                "(forall ((y Int)) (= y (+ 1 1)))",
            ),
        ]);
    }
}
