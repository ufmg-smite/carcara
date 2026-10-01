//! This module implements less strict definitions of equality for terms. In particular, it
//! contains two definitions of equality that differ from `PartialEq`:
//!
//! - `polyeq` considers `=` terms that are reflections of each other as equal, meaning the terms
//!   `(= a b)` and `(= b a)` are considered equal by this method.
//!
//! - `alpha_equiv` compares terms by alpha-equivalence, meaning it implements equality of terms
//!   modulo renaming of bound variables.

use rug::Rational;

use super::{
    AnchorArg, BindingList, Constant, NaryCase, Operator, ProofCommand, ProofStep, Rc, Sort,
    Subproof, Term,
};
use crate::utils::HashMapStack;
use std::time::{Duration, Instant};

/// A trait that represents objects that can be compared for equality modulo reordering of
/// equalities or alpha equivalence.
pub trait PolyeqComparable {
    /// Compares two objects with a given [`Polyeq`]. Returns `true` if they are equivalent.
    fn eq(comp: &mut Polyeq, a: &Self, b: &Self) -> bool;
}

/// Computes whether the two given terms are equal, modulo reordering of equalities.
///
/// That is, for this function, `=` terms that are reflections of each other are considered as
/// equal, meaning terms like `(and p (= a b))` and `(and p (= b a))` are considered equal.
///
/// This function records how long it takes to run, and adds that duration to the `time` argument.
pub fn polyeq(a: &Rc<Term>, b: &Rc<Term>, time: &mut Duration) -> bool {
    Polyeq::new().mod_reordering(true).eq_with_time(a, b, time)
}

/// Similar to `polyeq`, but instead compares terms for alpha equivalence.
///
/// This means that two terms which are the same, except for the renaming of a bound variable, are
/// considered equivalent. This functions still considers equality modulo reordering of equalities.
/// For example, this function will consider the terms `(forall ((x Int)) (= x 0))` and `(forall ((y
/// Int)) (= 0 y))` as equivalent.
///
/// This function records how long it takes to run, and adds that duration to the `time` argument.
pub fn alpha_equiv(a: &Rc<Term>, b: &Rc<Term>, time: &mut Duration) -> bool {
    Polyeq::new()
        .mod_reordering(true)
        .alpha_equiv(true)
        .eq_with_time(a, b, time)
}

/// Configuration for a `Polyeq`.
///
/// This controls how the comparison is performed and which families of terms are considered
/// equivalent.
#[derive(Default)]
pub struct PolyeqConfig {
    /// If set to true, term comparison will be done modulo reordering of equalities. That is, the
    /// terms `(= a b)` and `(= b a)` will be considered equivalent.
    pub is_mod_reordering: bool,

    /// If set to true, terms will be compared for alpha equivalence. That is, terms that can be
    /// made equal by renaming bound variables will be considered equivalent.
    pub is_alpha_equivalence: bool,

    /// If set to true, term comparison will be done modulo the expansion of n-ary operators. That
    /// is, the syntax sugar around n-ary operators will be expanded before comparison, such that
    /// the terms `(and a b c)` and `(and (and a b) c)` will be considered equivalent.
    pub is_mod_nary: bool,
}

impl PolyeqConfig {
    /// Constructs a new `PolyeqConfig`, with all options set to `false`.
    pub fn new() -> Self {
        Self::default()
    }
}

/// A configurable comparator for polyequality and alpha equivalence.
pub struct Polyeq {
    // In order to check alpha-equivalence, we can't use a simple global cache. For instance, let's
    // say we are comparing the following terms for alpha equivalence:
    // ```
    //     a := (and
    //         (forall ((x Int) (y Int)) (< x y))
    //         (forall ((x Int) (y Int)) (< x y))
    //     )
    //     b := (and
    //         (forall ((x Int) (y Int)) (< x y))
    //         (forall ((y Int) (x Int)) (< x y))
    //     )
    // ```
    // When comparing the first argument of each term, `(forall ((x Int) (y Int)) (< x y))`,
    // `(< x y)` will become `(< $0 $1)` for both `a` and `b`, using De Bruijn indices. We will see
    // that they are equal, and add the entry `((< x y), (< x y))` to the cache. However, when we
    // are comparing the second argument of each term, `(< x y)` will again be `(< $0 $1)` in `a`,
    // but it will be `(< $1 $0)` in `b`. If we just rely on the cache, we will incorrectly
    // determine that `a` and `b` are alpha-equivalent.  To account for that, we use a more
    // complicated caching system, based on a `HashMapStack`. We push a new scope every time we
    // enter a binder term, and pop it as we exit. This unfortunately means that equalities derived
    // inside a binder term can't be reused outside of it, degrading performance. If we are not
    // checking for alpha-equivalence, we never push an additional scope to this `HashMapStack`,
    // meaning it functions as a simple hash map.
    cache: HashMapStack<(Rc<Term>, Rc<Term>), ()>,
    is_mod_reordering: bool,
    de_bruijn_map: Option<DeBruijnMap>,
    is_mod_nary: bool,

    current_depth: usize,
    max_depth: usize,
}

impl Default for Polyeq {
    fn default() -> Self {
        Self::new()
    }
}

impl Polyeq {
    /// Constructs a new `Polyeq` with the default configuration.
    pub fn new() -> Self {
        Self::with_config(PolyeqConfig::new())
    }

    /// Constructs a new `Polyeq` with the provided configuration.
    pub fn with_config(config: PolyeqConfig) -> Self {
        Self {
            cache: HashMapStack::new(),
            is_mod_reordering: config.is_mod_reordering,
            de_bruijn_map: config.is_alpha_equivalence.then(DeBruijnMap::new),
            is_mod_nary: config.is_mod_nary,
            current_depth: 0,
            max_depth: 0,
        }
    }

    /// Controls whether to compare terms modulo the reordering of equalities.
    pub fn mod_reordering(mut self, value: bool) -> Self {
        self.is_mod_reordering = value;
        self
    }

    /// Controls whether to compare terms for alpha equivalence.
    pub fn alpha_equiv(mut self, value: bool) -> Self {
        self.de_bruijn_map = value.then(DeBruijnMap::new);
        self
    }

    /// Controls whether to compare terms modulo the expansion of n-ary operators.
    pub fn mod_nary(mut self, value: bool) -> Self {
        self.is_mod_nary = value;
        self
    }

    /// Compares two `[PolyeqComparable]` objects, and returns `true` if they are equivalent.
    pub fn eq<T>(&mut self, a: &T, b: &T) -> bool
    where
        T: PolyeqComparable + ?Sized,
    {
        PolyeqComparable::eq(self, a, b)
    }

    /// Compares two `[PolyeqComparable]` objects, and returns `true` if they are equivalent.
    /// Additionally, records how long the comparison took, and adds that time to the given `time`
    /// argument.
    pub fn eq_with_time<T>(&mut self, a: &T, b: &T, time: &mut Duration) -> bool
    where
        T: PolyeqComparable + ?Sized,
    {
        let start = Instant::now();
        let result = self.eq(a, b);
        *time += start.elapsed();
        result
    }

    /// The maximum term depth this `Polyeq` reached when performing a comparison.
    pub fn max_depth(&self) -> usize {
        self.max_depth
    }

    fn compare_binder<V: PolyeqComparable>(
        &mut self,
        a_binds: &BindingList<V>,
        b_binds: &BindingList<V>,
        a_inner: &Rc<Term>,
        b_inner: &Rc<Term>,
    ) -> bool {
        if let Some(de_bruijn_map) = self.de_bruijn_map.as_mut() {
            // First, we push new scopes into the De Bruijn map and the cache stack
            de_bruijn_map.push();
            self.cache.push_scope();

            // Then, we check that the binding lists and the inner terms are equivalent
            for (a_var, b_var) in a_binds.iter().zip(b_binds.iter()) {
                if !self.eq(&a_var.1, &b_var.1) {
                    // We must remember to pop the frames from the De Bruijn map and cache stack
                    // here, so as not to leave them in a corrupted state
                    self.de_bruijn_map.as_mut().unwrap().pop();
                    self.cache.pop_scope();
                    return false;
                }
                // We also insert each variable in the binding lists into the De Bruijn map
                self.de_bruijn_map
                    .as_mut()
                    .unwrap()
                    .insert(a_var.0.clone(), b_var.0.clone());
            }
            let result = self.eq(a_inner, b_inner);

            // Finally, we pop the scopes we pushed
            self.de_bruijn_map.as_mut().unwrap().pop();
            self.cache.pop_scope();

            result
        } else {
            self.eq(a_binds, b_binds) && self.eq(a_inner, b_inner)
        }
    }

    fn compare_op(
        &mut self,
        op_a: Operator,
        args_a: &[Rc<Term>],
        op_b: Operator,
        args_b: &[Rc<Term>],
    ) -> bool {
        // Modulo reordering of equalities
        if self.is_mod_reordering
            && let (Operator::Equals, [a_1, a_2], Operator::Equals, [b_1, b_2]) =
                (op_a, args_a, op_b, args_b)
        {
            // If the term is an equality of two terms, we also check if they would be
            // equal if one of them was flipped
            return self.eq(&(a_1, a_2), &(b_1, b_2)) || self.eq(&(a_1, a_2), &(b_2, b_1));
        }

        // Modulo n-ary expansion
        if self.is_mod_nary {
            if op_a != op_b {
                // TODO: check pairwise case
                return if op_a.nary_case() == Some(NaryCase::Chainable) {
                    op_b == Operator::And && self.compare_chainable(op_a, args_a, args_b)
                } else if op_b.nary_case() == Some(NaryCase::Chainable) {
                    op_a == Operator::And && self.compare_chainable(op_b, args_b, args_a)
                } else {
                    false
                };
            } else if args_a.len() != args_b.len() {
                let case = op_a.nary_case();
                return matches!(case, Some(NaryCase::RightAssoc | NaryCase::LeftAssoc))
                    && self.compare_assoc(op_a, args_a, args_b);
            };
        }

        // General case
        op_a == op_b && self.eq(args_a, args_b)
    }

    fn compare_chainable(&mut self, op: Operator, args: &[Rc<Term>], chain: &[Rc<Term>]) -> bool {
        if args.len() != chain.len() + 1 {
            return false;
        }
        args.windows(2)
            .zip(chain.iter())
            .all(|(window, chain_term)| {
                let (a, b) = (&window[0], &window[1]);
                match chain_term.as_ref() {
                    Term::Op(chain_op, args) if *chain_op == op && args.len() == 2 => {
                        self.eq(a, &args[0]) && self.eq(b, &args[1])
                    }
                    _ => false,
                }
            })
    }

    fn compare_assoc(&mut self, op: Operator, left: &[Rc<Term>], right: &[Rc<Term>]) -> bool {
        fn split(args: &[Rc<Term>], is_right: bool) -> (&Rc<Term>, &[Rc<Term>]) {
            match args {
                [] | [_] => unreachable!(),
                [first, rest @ ..] if is_right => (first, rest),
                [rest @ .., last] => (last, rest),
            }
        }

        fn flatten_if_singleton(tail: &[Rc<Term>], op: Operator) -> Option<&[Rc<Term>]> {
            let [term] = tail else {
                return None;
            };
            let (term_op, args) = term.as_op()?;
            if term_op == op { Some(args) } else { None }
        }

        match (left.len(), right.len()) {
            (1, 1) => return self.eq(&left[0], &right[0]),
            (1, _) | (_, 1) => return false,
            _ => (),
        }

        let is_right = op.nary_case() == Some(NaryCase::RightAssoc);

        let (left_head, mut left_tail) = split(left, is_right);
        let (right_head, mut right_tail) = split(right, is_right);

        if !self.eq(left_head, right_head) {
            return false;
        }

        left_tail = flatten_if_singleton(left_tail, op).unwrap_or(left_tail);
        right_tail = flatten_if_singleton(right_tail, op).unwrap_or(right_tail);

        self.compare_assoc(op, left_tail, right_tail)
    }
}

impl PolyeqComparable for Rc<Term> {
    fn eq(comp: &mut Polyeq, a: &Self, b: &Self) -> bool {
        // In general, if the two `Rc`s are directly equal, we can return `true`.
        //
        // However, if we are checking for alpha-equivalence, identical terms may be considered
        // different if the bound variables in them have different meanings. For example, in the
        // terms `(forall ((x Int) (y Int)) (< x y))` and `(forall ((y Int) (x Int)) (< x y))`,
        // even though both instances of `(< x y)` are identical, they are not alpha-equivalent.
        //
        // To account for that, if we are checking for alpha-equivalence and have encountered at
        // least one binder, we don't apply this optimization
        let possibly_renamed = comp.de_bruijn_map.as_ref().is_some_and(|m| !m.is_empty());
        if !possibly_renamed && a == b {
            return true;
        }

        // We first check the cache to see if these terms were already determined to be equal
        if comp.cache.get(&(a.clone(), b.clone())).is_some() {
            return true;
        }

        comp.current_depth += 1;
        comp.max_depth = std::cmp::max(comp.max_depth, comp.current_depth);
        let result = comp.eq(a.as_ref(), b.as_ref());
        if result {
            comp.cache.insert((a.clone(), b.clone()), ());
        }
        comp.current_depth -= 1;
        result
    }
}

impl PolyeqComparable for Term {
    fn eq(comp: &mut Polyeq, a: &Self, b: &Self) -> bool {
        match (a, b) {
            (Term::Const(a1), Term::Const(b1)) => match (a1, b1) {
                (Constant::Real(r1), Constant::Integer(i2)) if r1.is_integer() => {
                    r1.numer().clone() == i2.clone()
                }
                (Constant::Integer(i1), Constant::Real(r2)) if r2.is_integer() => {
                    i1.clone() == r2.numer().clone()
                }
                _ => a == b,
            },
            (Term::Var(a, a_sort), Term::Var(b, b_sort)) if comp.de_bruijn_map.is_some() => {
                // If we are checking for alpha-equivalence, and we encounter two variables, we
                // check that they are equivalent using the De Bruijn map
                if let Some(db) = comp.de_bruijn_map.as_mut() {
                    db.compare(a, b) && comp.eq(a_sort, b_sort)
                } else {
                    a == b && comp.eq(a_sort, b_sort)
                }
            }
            (Term::App(f_a, args_a), Term::App(f_b, args_b)) => {
                comp.eq(f_a, f_b) && comp.eq(args_a, args_b)
            }
            (
                Term::ParamOp {
                    op: op_a,
                    op_args: op_args_a,
                    args: args_a,
                },
                Term::ParamOp {
                    op: op_b,
                    op_args: op_args_b,
                    args: args_b,
                },
            ) => op_a == op_b && op_args_a == op_args_b && comp.eq(args_a, args_b),
            (Term::AsOp(op_a, sort_a, args_a), Term::AsOp(op_b, sort_b, args_b)) => {
                op_a == op_b && sort_a == sort_b && comp.eq(args_a, args_b)
            }

            // Check the singleton case (op a) = a, where op is left-associative
            (Term::Op(op, args), other) | (other, Term::Op(op, args))
                if comp.is_mod_nary
                    && args.len() == 1
                    && op.nary_case() == Some(NaryCase::LeftAssoc)
                    // We have to check with `==` first because we are calling into `comp.eq` with
                    // `&Term`s directly (instead of `Rc<Term>`s), so the `==` check is skipped
                    && (args[0].as_ref() == other || comp.eq(args[0].as_ref(), other)) =>
            {
                true
            }
            (Term::Op(op_a, args_a), Term::Op(op_b, args_b)) => {
                comp.compare_op(*op_a, args_a, *op_b, args_b)
            }
            (Term::Binder(q_a, binds_a, a), Term::Binder(q_b, binds_b, b)) => {
                q_a == q_b && comp.compare_binder(binds_a, binds_b, a, b)
            }
            (Term::Let(binds_a, a), Term::Let(binds_b, b)) => {
                comp.compare_binder(binds_a, binds_b, a, b)
            }
            (Term::Const(Constant::Real(r)), Term::Op(Operator::RealDiv, args)) => {
                // if a is a rational and b a division literal, check
                // if they are the same
                match (args[0].as_ref(), args[1].as_ref()) {
                    (Term::Const(Constant::Real(r1)), Term::Const(Constant::Real(r2)))
                        if r1.is_integer() && r2.is_integer() =>
                    {
                        Rational::from((r1.numer(), r2.numer())) == r.clone()
                    }
                    _ => false,
                }
            }
            (Term::Op(Operator::RealDiv, args), Term::Const(Constant::Real(r))) => {
                // if a is a rational and b a division literal, check
                // if they are the same
                match (args[0].as_ref(), args[1].as_ref()) {
                    (Term::Const(Constant::Real(r1)), Term::Const(Constant::Real(r2)))
                        if r.is_positive() && r1.is_integer() && r2.is_integer() =>
                    {
                        Rational::from((r1.numer(), r2.numer())) == r.clone()
                    }
                    (Term::Op(Operator::Sub, args), Term::Const(Constant::Integer(r2)))
                    | (Term::Const(Constant::Integer(r2)), Term::Op(Operator::Sub, args))
                        if r.is_negative() && args.len() == 1 =>
                    {
                        if let Term::Const(Constant::Integer(r1)) = args[0].as_ref() {
                            Rational::from((r1, r2)) == r.clone().abs()
                        } else {
                            false
                        }
                    }
                    _ => false,
                }
            }
            (Term::Const(Constant::Integer(i1)), Term::Op(Operator::Sub, args))
            | (Term::Op(Operator::Sub, args), Term::Const(Constant::Integer(i1)))
                if i1.is_negative() && args.len() == 1 =>
            {
                if let Term::Const(Constant::Integer(i2)) = args[0].as_ref() {
                    i1.clone().abs() == i2.clone()
                } else if let Term::Const(Constant::Real(r2)) = args[0].as_ref() {
                    i1.clone().abs() == r2.numer().clone()
                } else {
                    false
                }
            }
            (Term::Op(Operator::Sub, args), Term::Const(Constant::Real(r)))
            | (Term::Const(Constant::Real(r)), Term::Op(Operator::Sub, args))
                if r.is_negative() && args.len() == 1 =>
            {
                match args[0].as_ref() {
                    Term::Op(Operator::RealDiv, sub_args) => {
                        match (sub_args[0].as_ref(), sub_args[1].as_ref()) {
                            (Term::Const(Constant::Real(r1)), Term::Const(Constant::Real(r2)))
                                if r1.is_integer() && r2.is_integer() =>
                            {
                                Rational::from((r1.numer(), r2.numer())) == r.clone().abs()
                            }
                            _ => false,
                        }
                    }
                    Term::Const(Constant::Real(r1)) => r1.clone() == r.clone().abs(),
                    _ => false,
                }
            }
            _ => false,
        }
    }
}

impl<T: PolyeqComparable> PolyeqComparable for BindingList<T> {
    fn eq(comp: &mut Polyeq, a: &Self, b: &Self) -> bool {
        comp.eq(&a.0, &b.0)
    }
}

impl PolyeqComparable for Rc<Sort> {
    fn eq(comp: &mut Polyeq, a: &Self, b: &Self) -> bool {
        a == b || comp.eq(a.as_ref(), b.as_ref())
    }
}

impl PolyeqComparable for Sort {
    fn eq(comp: &mut Polyeq, a: &Self, b: &Self) -> bool {
        match (a, b) {
            (Sort::Function(sorts_a), Sort::Function(sorts_b)) => comp.eq(sorts_a, sorts_b),
            (Sort::Atom(a, sorts_a), Sort::Atom(b, sorts_b)) => {
                a == b && comp.eq(sorts_a.as_ref(), sorts_b.as_ref())
            }
            (Sort::Bool, Sort::Bool)
            | (Sort::Int, Sort::Int)
            | (Sort::Real, Sort::Real)
            | (Sort::String, Sort::String)
            | (Sort::RegLan, Sort::RegLan)
            | (Sort::Type, Sort::Type) => true,
            (Sort::Array(x_a, y_a), Sort::Array(x_b, y_b)) => {
                comp.eq(x_a, x_b) && comp.eq(y_a, y_b)
            }
            (Sort::BitVec(a), Sort::BitVec(b)) => a == b,
            (Sort::ParamBitVec, Sort::ParamBitVec) => true,
            _ => false,
        }
    }
}

impl<T: PolyeqComparable> PolyeqComparable for &T {
    fn eq(comp: &mut Polyeq, a: &Self, b: &Self) -> bool {
        comp.eq(*a, *b)
    }
}

impl<T: PolyeqComparable> PolyeqComparable for [T] {
    fn eq(comp: &mut Polyeq, a: &Self, b: &Self) -> bool {
        a.len() == b.len() && a.iter().zip(b.iter()).all(|(a, b)| comp.eq(a, b))
    }
}

impl<T: PolyeqComparable> PolyeqComparable for Vec<T> {
    fn eq(comp: &mut Polyeq, a: &Self, b: &Self) -> bool {
        comp.eq(a.as_slice(), b.as_slice())
    }
}

impl<T: PolyeqComparable, U: PolyeqComparable> PolyeqComparable for (T, U) {
    fn eq(comp: &mut Polyeq, a: &Self, b: &Self) -> bool {
        comp.eq(&a.0, &b.0) && comp.eq(&a.1, &b.1)
    }
}

impl PolyeqComparable for String {
    fn eq(_: &mut Polyeq, a: &Self, b: &Self) -> bool {
        a == b
    }
}

impl PolyeqComparable for AnchorArg {
    fn eq(comp: &mut Polyeq, a: &Self, b: &Self) -> bool {
        match (a, b) {
            (AnchorArg::Variable(a), AnchorArg::Variable(b)) => comp.eq(a, b),
            (AnchorArg::Assign(a_name, a_value), AnchorArg::Assign(b_name, b_value)) => {
                a_name == b_name && comp.eq(a_value, b_value)
            }
            _ => false,
        }
    }
}

impl PolyeqComparable for ProofCommand {
    fn eq(comp: &mut Polyeq, a: &Self, b: &Self) -> bool {
        match (a, b) {
            (
                ProofCommand::Assume { id: a_id, term: a_term },
                ProofCommand::Assume { id: b_id, term: b_term },
            ) => a_id == b_id && comp.eq(a_term, b_term),
            (ProofCommand::Step(a), ProofCommand::Step(b)) => comp.eq(a, b),
            (ProofCommand::Subproof(a), ProofCommand::Subproof(b)) => comp.eq(a, b),
            _ => false,
        }
    }
}

impl PolyeqComparable for ProofStep {
    fn eq(comp: &mut Polyeq, a: &Self, b: &Self) -> bool {
        a.id == b.id
            && comp.eq(&a.clause, &b.clause)
            && a.rule == b.rule
            && a.premises == b.premises
            && comp.eq(&a.args, &b.args)
            && a.discharge == b.discharge
    }
}

impl PolyeqComparable for Subproof {
    fn eq(comp: &mut Polyeq, a: &Self, b: &Self) -> bool {
        comp.eq(&a.commands, &b.commands) && comp.eq(&a.args, &b.args)
    }
}

struct DeBruijnMap {
    // To check for alpha-equivalence, we make use of De Bruijn indices. The idea is to map each
    // bound variable to an integer depending on the order in which they were bound. As we compare
    // the two terms, if we encounter two bound variables, we need only to check if the associated
    // integers are equal, and the actual names of the variables are irrelevant.
    //
    // Normally, the index selected for a given appearance of a variable is the number of bound
    // variables introduced between that variable and its appearance. That is, the term
    //     `(forall ((x Int)) (and (exists ((y Int)) (> x y)) (> x 5)))`
    // would be represented using De Bruijn indices like this:
    //     `(forall ((x Int)) (and (exists ((y Int)) (> $1 $0)) (> $0 5)))`
    // This has a few annoying properties, like the fact that the same bound variable can receive
    // different indices in different appearances (in the example, `x` appears as both `$0` and
    // `$1`). To simplify the implementation, we revert the order of the indices, such that each
    // variable appearance is assigned the index of the binding of that variable. That is, all
    // appearances of the first bound variable are assigned `$0`, all appearances of the variable
    // that is bound second are assigned `$1`, etc. The given term would then be represented like
    // this:
    //     `(forall ((x Int)) (and (exists ((y Int)) (> $0 $1)) (> $0 5)))`
    indices: (HashMapStack<String, usize>, HashMapStack<String, usize>),

    // Holds the count of how many variables were bound before each depth
    counter: Vec<usize>,
}

impl DeBruijnMap {
    fn new() -> Self {
        Self {
            indices: (HashMapStack::new(), HashMapStack::new()),
            counter: vec![0],
        }
    }

    fn is_empty(&self) -> bool {
        self.indices.0.is_empty() && self.indices.1.is_empty()
    }

    fn push(&mut self) {
        self.indices.0.push_scope();
        self.indices.1.push_scope();
        let current = *self.counter.last().unwrap();
        self.counter.push(current);
    }

    fn pop(&mut self) {
        self.indices.0.pop_scope();
        self.indices.1.pop_scope();

        // If we successfully popped the scopes from the indices stacks, that means that there was
        // at least one scope, so we can safely pop from the counter stack as well
        self.counter.pop();
    }

    fn insert(&mut self, a: String, b: String) {
        let current = self.counter.last_mut().unwrap();
        self.indices.0.insert(a, *current);
        self.indices.1.insert(b, *current);
        *current += 1;
    }

    fn compare(&self, a: &str, b: &str) -> bool {
        match (self.indices.0.get(a), self.indices.1.get(b)) {
            // If both a and b are free variables, they need to have the same name
            (None, None) => a == b,

            // If they are both bound variables, they need to have the same De Bruijn indices
            (Some(a), Some(b)) => a == b,

            // If one of them is bound and the other is free, they are not equal
            _ => false,
        }
    }
}
