//! This module implements less strict definitions of equality for terms. In particular, it
//! contains three definitions of equality that differ from `PartialEq`:
//!
//! - `eq` implements a "deep" equality, meaning that it compares `ast::Rc`s by value,
//! instead of by reference.
//!
//! - `eq_modulo_reordering` is also a "deep" equality, but it considers `=` terms that are
//! reflections of each other as equal, meaning the terms `(= a b)` and `(= b a)` are considered
//! equal by this method.
//!
//! - `are_alpha_equivalent` compares terms by alpha-equivalence, meaning it implements equality of
//! terms modulo renaming of bound variables.

use super::{
    BindingList, Identifier, Operator, ProofArg, ProofCommand, ProofStep, Rc, Sort, Subproof, Term,
    Terminal,
};
use crate::utils::SymbolTable;
use std::time::{Duration, Instant};

pub trait DeepEq {
    fn eq(checker: &mut DeepEqualityChecker, a: &Self, b: &Self) -> bool;
}

pub fn timed_deep_eq<T: DeepEq>(a: &T, b: &T, time: &mut Duration) -> bool {
    let start = Instant::now();
    let result = deep_eq(a, b);
    *time += start.elapsed();
    result
}

pub fn timed_deep_eq_modulo_reordering<T: DeepEq>(a: &T, b: &T, time: &mut Duration) -> bool {
    let start = Instant::now();
    let result = deep_eq_modulo_reordering(a, b);
    *time += start.elapsed();
    result
}

pub fn deep_eq<T: DeepEq>(a: &T, b: &T) -> bool {
    DeepEq::eq(&mut DeepEqualityChecker::new(false, false), a, b)
}

pub fn deep_eq_modulo_reordering<T: DeepEq>(a: &T, b: &T) -> bool {
    DeepEq::eq(&mut DeepEqualityChecker::new(true, false), a, b)
}

pub fn tracing_deep_eq(a: &Rc<Term>, b: &Rc<Term>, time: &mut Duration) -> (bool, usize) {
    let start = Instant::now();

    let mut checker = DeepEqualityChecker::new(true, false);
    let result = DeepEq::eq(&mut checker, a, b);

    *time += start.elapsed();
    (result, checker.max_depth)
}

pub fn are_alpha_equivalent(a: &Rc<Term>, b: &Rc<Term>, time: &mut Duration) -> bool {
    let start = Instant::now();

    // When we are checking for alpha-equivalence, we can't always assume that if `a` and `b` are
    // identical, they are alpha-equivalent, so that optimization is not used in `DeepEq::eq`.
    // However, here at the "root" level this assumption is valid, so we check if the terms are
    // directly equal before doing anything else
    let result = a == b || DeepEq::eq(&mut DeepEqualityChecker::new(true, true), a, b);

    *time += start.elapsed();
    result
}

pub struct DeepEqualityChecker {
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
    // complicated caching system, based on a `SymbolTable`. We push a new scope every time we enter
    // a binder term, and pop it as we exit. This unfortunately means that equalities derived
    // inside a binder term can't be reused outside of it, degrading performance. If we are not
    // checking for alpha-equivalence, we never push an additional scope to this `SymbolTable`,
    // meaning it functions as a simple hash set.
    cache: SymbolTable<(Rc<Term>, Rc<Term>), ()>,
    is_mod_reordering: bool,
    alpha_equiv_checker: Option<AlphaEquivalenceChecker>,

    current_depth: usize,
    max_depth: usize,
}

impl DeepEqualityChecker {
    pub fn new(is_mod_reordering: bool, is_alpha_equivalence: bool) -> Self {
        Self {
            is_mod_reordering,
            cache: SymbolTable::new(),
            alpha_equiv_checker: if is_alpha_equivalence {
                Some(AlphaEquivalenceChecker::new())
            } else {
                None
            },
            current_depth: 0,
            max_depth: 0,
        }
    }

    fn check_binder(
        &mut self,
        a_binds: &BindingList,
        b_binds: &BindingList,
        a_inner: &Rc<Term>,
        b_inner: &Rc<Term>,
    ) -> bool {
        if let Some(alpha_checker) = self.alpha_equiv_checker.as_mut() {
            // First, we push new scopes into the alpha-equivalence checker and the cache stack
            alpha_checker.push();
            self.cache.push_scope();

            // Then, we check that the binding lists and the inner terms are equivalent
            for (a_var, b_var) in a_binds.iter().zip(b_binds.iter()) {
                if !DeepEq::eq(self, &a_var.1, &b_var.1) {
                    // We must remember to pop the frames from the alpha equivalence checker and
                    // cache stack here, so as not to leave them in a corrupted state
                    self.alpha_equiv_checker.as_mut().unwrap().pop();
                    self.cache.pop_scope();
                    return false;
                }
                // We also insert each variable in the binding lists into the alpha-equivalence
                // checker
                self.alpha_equiv_checker
                    .as_mut()
                    .unwrap()
                    .insert(a_var.0.clone(), b_var.0.clone());
            }
            let result = DeepEq::eq(self, a_inner, b_inner);

            // Finally, we pop the scopes we pushed
            self.alpha_equiv_checker.as_mut().unwrap().pop();
            self.cache.pop_scope();

            result
        } else {
            DeepEq::eq(self, a_binds, b_binds) && DeepEq::eq(self, a_inner, b_inner)
        }
    }
}

impl DeepEq for Rc<Term> {
    fn eq(checker: &mut DeepEqualityChecker, a: &Self, b: &Self) -> bool {
        // If the two `Rc`s are directly equal, and we are not checking for alpha-equivalence, we
        // can return `true`.
        // Note that if we are checking for alpha-equivalence, identical terms may be considered
        // different, if the bound variables in them have different meanings. For example, in the
        // terms `(forall ((x Int) (y Int)) (< x y))` and `(forall ((y Int) (x Int)) (< x y))`,
        // even though both instances of `(< x y)` are identical, they are not alpha-equivalent.
        if checker.alpha_equiv_checker.is_none() && a == b {
            return true;
        }

        // We first check the cache to see if these terms were already determined to be equal
        if checker.cache.get(&(a.clone(), b.clone())).is_some() {
            return true;
        }

        checker.current_depth += 1;
        checker.max_depth = std::cmp::max(checker.max_depth, checker.current_depth);
        let result = DeepEq::eq(checker, a.as_ref(), b.as_ref());
        if result {
            checker.cache.insert((a.clone(), b.clone()), ());
        }
        checker.current_depth -= 1;
        result
    }
}

impl DeepEq for Term {
    fn eq(checker: &mut DeepEqualityChecker, a: &Self, b: &Self) -> bool {
        match (a, b) {
            (Term::App(f_a, args_a), Term::App(f_b, args_b)) => {
                DeepEq::eq(checker, f_a, f_b) && DeepEq::eq(checker, args_a, args_b)
            }
            (Term::Op(op_a, args_a), Term::Op(op_b, args_b)) => {
                if checker.is_mod_reordering {
                    if let (Operator::Equals, [a_1, a_2], Operator::Equals, [b_1, b_2]) =
                        (op_a, args_a.as_slice(), op_b, args_b.as_slice())
                    {
                        // If the term is an equality of two terms, we also check if they would be
                        // equal if one of them was flipped
                        return DeepEq::eq(checker, &(a_1, a_2), &(b_1, b_2))
                            || DeepEq::eq(checker, &(a_1, a_2), &(b_2, b_1));
                    }
                }
                // General case
                op_a == op_b && DeepEq::eq(checker, args_a, args_b)
            }
            (Term::Sort(a), Term::Sort(b)) => DeepEq::eq(checker, a, b),
            (Term::Terminal(a), Term::Terminal(b)) => match (a, b) {
                // If we are checking for alpha-equivalence, and we encounter two variables, we
                // check that they are equivalent using the alpha-equivalence checker
                (
                    Terminal::Var(Identifier::Simple(a_var), a_sort),
                    Terminal::Var(Identifier::Simple(b_var), b_sort),
                ) if checker.alpha_equiv_checker.is_some() => {
                    let alpha = checker.alpha_equiv_checker.as_mut().unwrap();
                    alpha.check(a_var, b_var) && DeepEq::eq(checker, a_sort, b_sort)
                }

                (Terminal::Var(iden_a, sort_a), Terminal::Var(iden_b, sort_b)) => {
                    iden_a == iden_b && DeepEq::eq(checker, sort_a, sort_b)
                }
                (a, b) => a == b,
            },
            (Term::Quant(q_a, _, _), Term::Quant(q_b, _, _)) if q_a != q_b => false,
            (Term::Quant(_, a_binds, a), Term::Quant(_, b_binds, b))
            | (Term::Let(a_binds, a), Term::Let(b_binds, b))
            | (Term::Lambda(a_binds, a), Term::Lambda(b_binds, b)) => {
                checker.check_binder(a_binds, b_binds, a, b)
            }
            (Term::Choice(a_var, a), Term::Choice(b_var, b)) => {
                let a_binds = BindingList(vec![a_var.clone()]);
                let b_binds = BindingList(vec![b_var.clone()]);
                checker.check_binder(&a_binds, &b_binds, a, b)
            }
            _ => false,
        }
    }
}

impl DeepEq for BindingList {
    fn eq(checker: &mut DeepEqualityChecker, a: &Self, b: &Self) -> bool {
        DeepEq::eq(checker, &a.0, &b.0)
    }
}

impl DeepEq for Sort {
    fn eq(checker: &mut DeepEqualityChecker, a: &Self, b: &Self) -> bool {
        match (a, b) {
            (Sort::Function(sorts_a), Sort::Function(sorts_b)) => {
                DeepEq::eq(checker, sorts_a, sorts_b)
            }
            (Sort::Atom(a, sorts_a), Sort::Atom(b, sorts_b)) => {
                a == b && DeepEq::eq(checker, sorts_a, sorts_b)
            }
            (Sort::Bool, Sort::Bool)
            | (Sort::Int, Sort::Int)
            | (Sort::Real, Sort::Real)
            | (Sort::String, Sort::String) => true,
            (Sort::Array(x_a, y_a), Sort::Array(x_b, y_b)) => {
                DeepEq::eq(checker, x_a, x_b) && DeepEq::eq(checker, y_a, y_b)
            }
            _ => false,
        }
    }
}

impl<T: DeepEq> DeepEq for &T {
    fn eq(checker: &mut DeepEqualityChecker, a: &Self, b: &Self) -> bool {
        DeepEq::eq(checker, *a, *b)
    }
}

impl<T: DeepEq> DeepEq for [T] {
    fn eq(checker: &mut DeepEqualityChecker, a: &Self, b: &Self) -> bool {
        a.len() == b.len()
            && a.iter()
                .zip(b.iter())
                .all(|(a, b)| DeepEq::eq(checker, a, b))
    }
}

impl<T: DeepEq> DeepEq for Vec<T> {
    fn eq(checker: &mut DeepEqualityChecker, a: &Self, b: &Self) -> bool {
        DeepEq::eq(checker, a.as_slice(), b.as_slice())
    }
}

impl<T: DeepEq, U: DeepEq> DeepEq for (T, U) {
    fn eq(checker: &mut DeepEqualityChecker, a: &Self, b: &Self) -> bool {
        DeepEq::eq(checker, &a.0, &b.0) && DeepEq::eq(checker, &a.1, &b.1)
    }
}

impl DeepEq for String {
    fn eq(_: &mut DeepEqualityChecker, a: &Self, b: &Self) -> bool {
        a == b
    }
}

impl DeepEq for ProofArg {
    fn eq(checker: &mut DeepEqualityChecker, a: &Self, b: &Self) -> bool {
        match (a, b) {
            (ProofArg::Term(a), ProofArg::Term(b)) => DeepEq::eq(checker, a, b),
            (ProofArg::Assign(sa, ta), ProofArg::Assign(sb, tb)) => {
                sa == sb && DeepEq::eq(checker, ta, tb)
            }
            _ => false,
        }
    }
}

impl DeepEq for ProofCommand {
    fn eq(checker: &mut DeepEqualityChecker, a: &Self, b: &Self) -> bool {
        match (a, b) {
            (
                ProofCommand::Assume { id: a_id, term: a_term },
                ProofCommand::Assume { id: b_id, term: b_term },
            ) => a_id == b_id && DeepEq::eq(checker, a_term, b_term),
            (ProofCommand::Step(a), ProofCommand::Step(b)) => DeepEq::eq(checker, a, b),
            (ProofCommand::Subproof(a), ProofCommand::Subproof(b)) => DeepEq::eq(checker, a, b),
            _ => false,
        }
    }
}

impl DeepEq for ProofStep {
    fn eq(checker: &mut DeepEqualityChecker, a: &Self, b: &Self) -> bool {
        a.id == b.id
            && DeepEq::eq(checker, &a.clause, &b.clause)
            && a.rule == b.rule
            && a.premises == b.premises
            && DeepEq::eq(checker, &a.args, &b.args)
            && a.discharge == b.discharge
    }
}

impl DeepEq for Subproof {
    fn eq(checker: &mut DeepEqualityChecker, a: &Self, b: &Self) -> bool {
        DeepEq::eq(checker, &a.commands, &b.commands)
            && DeepEq::eq(checker, &a.assignment_args, &b.assignment_args)
            && DeepEq::eq(checker, &a.variable_args, &b.variable_args)
    }
}

struct AlphaEquivalenceChecker {
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
    indices: (SymbolTable<String, usize>, SymbolTable<String, usize>),
    counter: Vec<usize>, // Holds the count of how many variables were bound before each depth
}

impl AlphaEquivalenceChecker {
    fn new() -> Self {
        Self {
            indices: (SymbolTable::new(), SymbolTable::new()),
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

        // If we successfully popped the scopes from the symbol tables, that means that there was
        // at least one scope, so we can safely pop from the counter stack as well
        self.counter.pop();
    }

    fn insert(&mut self, a: String, b: String) {
        let current = self.counter.last_mut().unwrap();
        self.indices.0.insert(a, *current);
        self.indices.1.insert(b, *current);
        *current += 1;
    }

    fn check(&self, a: &str, b: &str) -> bool {
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
