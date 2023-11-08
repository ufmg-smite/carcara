//! This module implements less strict definitions of equality for terms. In particular, it
//! contains two definitions of equality that differ from `PartialEq`:
//!
//! - `polyeq` considers `=` terms that are reflections of each other as equal, meaning the terms
//! `(= a b)` and `(= b a)` are considered equal by this method.
//!
//! - `alpha_equiv` compares terms by alpha-equivalence, meaning it implements equality of terms
//! modulo renaming of bound variables.

use super::{BindingList, Operator, ProofArg, ProofCommand, ProofStep, Rc, Sort, Subproof, Term};
use crate::utils::HashMapStack;
use std::time::{Duration, Instant};

/// A trait that represents objects that can be compared for equality modulo reordering of
/// equalities or alpha equivalence.
pub trait Polyeq {
    fn eq(comp: &mut PolyeqComparator, a: &Self, b: &Self) -> bool;
}

/// Computes whether the two given terms are equal, modulo reordering of equalities.
///
/// That is, for this function, `=` terms that are reflections of each other are considered as
/// equal, meaning terms like `(and p (= a b))` and `(and p (= b a))` are considered equal.
///
/// This function records how long it takes to run, and adds that duration to the `time` argument.
pub fn polyeq(a: &Rc<Term>, b: &Rc<Term>, time: &mut Duration) -> bool {
    let start = Instant::now();
    let result = Polyeq::eq(&mut PolyeqComparator::new(true, false), a, b);
    *time += start.elapsed();
    result
}

/// Similar to `polyeq`, but also records the maximum depth the polyequal comparator reached when
/// comparing the terms.
///
/// This function records how long it takes to run, and adds that duration to the `time` argument.
pub fn tracing_polyeq(a: &Rc<Term>, b: &Rc<Term>, time: &mut Duration) -> (bool, usize) {
    let start = Instant::now();

    let mut comp = PolyeqComparator::new(true, false);
    let result = Polyeq::eq(&mut comp, a, b);

    *time += start.elapsed();
    (result, comp.max_depth)
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
    let start = Instant::now();

    // When we are checking for alpha-equivalence, we can't always assume that if `a` and `b` are
    // identical, they are alpha-equivalent, so that optimization is not used in `Polyeq::eq`.
    // However, here at the "root" level this assumption is valid, so we check if the terms are
    // directly equal before doing anything else
    let result = a == b || Polyeq::eq(&mut PolyeqComparator::new(true, true), a, b);

    *time += start.elapsed();
    result
}

/// A configurable comparator for polyequality and alpha equivalence.
pub struct PolyeqComparator {
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

    current_depth: usize,
    max_depth: usize,
}

impl PolyeqComparator {
    /// Constructs a new `PolyeqComparator`.
    ///
    /// If `is_mod_reordering` is `true`, the comparator will compare terms modulo reordering of
    /// equalities. If `is_alpha_equivalence` is `true`, the comparator will compare terms for alpha
    /// equivalence.
    pub fn new(is_mod_reordering: bool, is_alpha_equivalence: bool) -> Self {
        Self {
            is_mod_reordering,
            cache: HashMapStack::new(),
            de_bruijn_map: if is_alpha_equivalence {
                Some(DeBruijnMap::new())
            } else {
                None
            },
            current_depth: 0,
            max_depth: 0,
        }
    }

    fn compare_binder(
        &mut self,
        a_binds: &BindingList,
        b_binds: &BindingList,
        a_inner: &Rc<Term>,
        b_inner: &Rc<Term>,
    ) -> bool {
        if let Some(de_bruijn_map) = self.de_bruijn_map.as_mut() {
            // First, we push new scopes into the De Bruijn map and the cache stack
            de_bruijn_map.push();
            self.cache.push_scope();

            // Then, we check that the binding lists and the inner terms are equivalent
            for (a_var, b_var) in a_binds.iter().zip(b_binds.iter()) {
                if !Polyeq::eq(self, &a_var.1, &b_var.1) {
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
            let result = Polyeq::eq(self, a_inner, b_inner);

            // Finally, we pop the scopes we pushed
            self.de_bruijn_map.as_mut().unwrap().pop();
            self.cache.pop_scope();

            result
        } else {
            Polyeq::eq(self, a_binds, b_binds) && Polyeq::eq(self, a_inner, b_inner)
        }
    }
}

impl Polyeq for Rc<Term> {
    fn eq(comp: &mut PolyeqComparator, a: &Self, b: &Self) -> bool {
        // If the two `Rc`s are directly equal, and we are not checking for alpha-equivalence, we
        // can return `true`.
        // Note that if we are checking for alpha-equivalence, identical terms may be considered
        // different, if the bound variables in them have different meanings. For example, in the
        // terms `(forall ((x Int) (y Int)) (< x y))` and `(forall ((y Int) (x Int)) (< x y))`,
        // even though both instances of `(< x y)` are identical, they are not alpha-equivalent.
        if comp.de_bruijn_map.is_none() && a == b {
            return true;
        }

        // We first check the cache to see if these terms were already determined to be equal
        if comp.cache.get(&(a.clone(), b.clone())).is_some() {
            return true;
        }

        comp.current_depth += 1;
        comp.max_depth = std::cmp::max(comp.max_depth, comp.current_depth);
        let result = Polyeq::eq(comp, a.as_ref(), b.as_ref());
        if result {
            comp.cache.insert((a.clone(), b.clone()), ());
        }
        comp.current_depth -= 1;
        result
    }
}

impl Polyeq for Term {
    fn eq(comp: &mut PolyeqComparator, a: &Self, b: &Self) -> bool {
        match (a, b) {
            (Term::Const(a), Term::Const(b)) => a == b,
            (Term::Var(a, a_sort), Term::Var(b, b_sort)) if comp.de_bruijn_map.is_some() => {
                // If we are checking for alpha-equivalence, and we encounter two variables, we
                // check that they are equivalent using the De Bruijn map
                if let Some(db) = comp.de_bruijn_map.as_mut() {
                    db.compare(a, b) && Polyeq::eq(comp, a_sort, b_sort)
                } else {
                    a == b && Polyeq::eq(comp, a_sort, b_sort)
                }
            }
            (Term::App(f_a, args_a), Term::App(f_b, args_b)) => {
                Polyeq::eq(comp, f_a, f_b) && Polyeq::eq(comp, args_a, args_b)
            }
            (Term::Op(op_a, args_a), Term::Op(op_b, args_b)) => {
                if comp.is_mod_reordering {
                    if let (Operator::Equals, [a_1, a_2], Operator::Equals, [b_1, b_2]) =
                        (op_a, args_a.as_slice(), op_b, args_b.as_slice())
                    {
                        // If the term is an equality of two terms, we also check if they would be
                        // equal if one of them was flipped
                        return Polyeq::eq(comp, &(a_1, a_2), &(b_1, b_2))
                            || Polyeq::eq(comp, &(a_1, a_2), &(b_2, b_1));
                    }
                }
                // General case
                op_a == op_b && Polyeq::eq(comp, args_a, args_b)
            }
            (Term::Sort(a), Term::Sort(b)) => Polyeq::eq(comp, a, b),
            (Term::Quant(q_a, _, _), Term::Quant(q_b, _, _)) if q_a != q_b => false,
            (Term::Quant(_, a_binds, a), Term::Quant(_, b_binds, b))
            | (Term::Let(a_binds, a), Term::Let(b_binds, b))
            | (Term::Lambda(a_binds, a), Term::Lambda(b_binds, b)) => {
                comp.compare_binder(a_binds, b_binds, a, b)
            }
            (Term::Choice(a_var, a), Term::Choice(b_var, b)) => {
                let a_binds = BindingList(vec![a_var.clone()]);
                let b_binds = BindingList(vec![b_var.clone()]);
                comp.compare_binder(&a_binds, &b_binds, a, b)
            }
            _ => false,
        }
    }
}

impl Polyeq for BindingList {
    fn eq(comp: &mut PolyeqComparator, a: &Self, b: &Self) -> bool {
        Polyeq::eq(comp, &a.0, &b.0)
    }
}

impl Polyeq for Sort {
    fn eq(comp: &mut PolyeqComparator, a: &Self, b: &Self) -> bool {
        match (a, b) {
            (Sort::Function(sorts_a), Sort::Function(sorts_b)) => {
                Polyeq::eq(comp, sorts_a, sorts_b)
            }
            (Sort::Atom(a, sorts_a), Sort::Atom(b, sorts_b)) => {
                a == b && Polyeq::eq(comp, sorts_a, sorts_b)
            }
            (Sort::Bool, Sort::Bool)
            | (Sort::Int, Sort::Int)
            | (Sort::Real, Sort::Real)
            | (Sort::String, Sort::String) => true,
            (Sort::Array(x_a, y_a), Sort::Array(x_b, y_b)) => {
                Polyeq::eq(comp, x_a, x_b) && Polyeq::eq(comp, y_a, y_b)
            }
            _ => false,
        }
    }
}

impl<T: Polyeq> Polyeq for &T {
    fn eq(comp: &mut PolyeqComparator, a: &Self, b: &Self) -> bool {
        Polyeq::eq(comp, *a, *b)
    }
}

impl<T: Polyeq> Polyeq for [T] {
    fn eq(comp: &mut PolyeqComparator, a: &Self, b: &Self) -> bool {
        a.len() == b.len() && a.iter().zip(b.iter()).all(|(a, b)| Polyeq::eq(comp, a, b))
    }
}

impl<T: Polyeq> Polyeq for Vec<T> {
    fn eq(comp: &mut PolyeqComparator, a: &Self, b: &Self) -> bool {
        Polyeq::eq(comp, a.as_slice(), b.as_slice())
    }
}

impl<T: Polyeq, U: Polyeq> Polyeq for (T, U) {
    fn eq(comp: &mut PolyeqComparator, a: &Self, b: &Self) -> bool {
        Polyeq::eq(comp, &a.0, &b.0) && Polyeq::eq(comp, &a.1, &b.1)
    }
}

impl Polyeq for String {
    fn eq(_: &mut PolyeqComparator, a: &Self, b: &Self) -> bool {
        a == b
    }
}

impl Polyeq for ProofArg {
    fn eq(comp: &mut PolyeqComparator, a: &Self, b: &Self) -> bool {
        match (a, b) {
            (ProofArg::Term(a), ProofArg::Term(b)) => Polyeq::eq(comp, a, b),
            (ProofArg::Assign(sa, ta), ProofArg::Assign(sb, tb)) => {
                sa == sb && Polyeq::eq(comp, ta, tb)
            }
            _ => false,
        }
    }
}

impl Polyeq for ProofCommand {
    fn eq(comp: &mut PolyeqComparator, a: &Self, b: &Self) -> bool {
        match (a, b) {
            (
                ProofCommand::Assume { id: a_id, term: a_term },
                ProofCommand::Assume { id: b_id, term: b_term },
            ) => a_id == b_id && Polyeq::eq(comp, a_term, b_term),
            (ProofCommand::Step(a), ProofCommand::Step(b)) => Polyeq::eq(comp, a, b),
            (ProofCommand::Subproof(a), ProofCommand::Subproof(b)) => Polyeq::eq(comp, a, b),
            _ => false,
        }
    }
}

impl Polyeq for ProofStep {
    fn eq(comp: &mut PolyeqComparator, a: &Self, b: &Self) -> bool {
        a.id == b.id
            && Polyeq::eq(comp, &a.clause, &b.clause)
            && a.rule == b.rule
            && a.premises == b.premises
            && Polyeq::eq(comp, &a.args, &b.args)
            && a.discharge == b.discharge
    }
}

impl Polyeq for Subproof {
    fn eq(comp: &mut PolyeqComparator, a: &Self, b: &Self) -> bool {
        Polyeq::eq(comp, &a.commands, &b.commands)
            && Polyeq::eq(comp, &a.assignment_args, &b.assignment_args)
            && Polyeq::eq(comp, &a.variable_args, &b.variable_args)
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
