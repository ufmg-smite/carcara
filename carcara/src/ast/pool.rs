//! This module implements `TermPool`, a structure that stores terms and implements hash consing.

use super::{Rc, Term};
use ahash::AHashSet;

pub type TermPool = AdvancedPools::LocalPool;

pub trait TPool {
    /// Returns the term corresponding to the boolean constant `true`.
    fn bool_true(&self) -> Rc<Term>;
    /// Returns the term corresponding to the boolean constant `false`.
    fn bool_false(&self) -> Rc<Term>;
    /// Returns the term corresponding to the boolean constant determined by `value`.
    fn bool_constant(&self, value: bool) -> Rc<Term> {
        match value {
            true => self.bool_true(),
            false => self.bool_false(),
        }
    }
    /// Takes a term and returns a possibly newly allocated `Rc` that references it.
    ///
    /// If the term was not originally in the term pool, it is added to it. Otherwise, this method
    /// just returns an `Rc` pointing to the existing allocation. This method also computes the
    /// term's sort, and adds it to the sort cache.
    fn add(&mut self, term: Term) -> Rc<Term>;
    /// Takes a vector of terms and calls [`TermPool::add`] on each.
    fn add_all(&mut self, terms: Vec<Term>) -> Vec<Rc<Term>> {
        terms.into_iter().map(|t| self.add(t)).collect()
    }
    /// Returns the sort of the given term.
    ///
    /// This method assumes that the sorts of any subterms have already been checked, and are
    /// correct. If `term` is itself a sort, this simply returns that sort.
    fn sort(&self, term: &Rc<Term>) -> Rc<Term>;
    /// Returns an `AHashSet` containing all the free variables in the given term.
    ///
    /// This method uses a cache, so there is no additional cost to computing the free variables of
    /// a term multiple times.
    fn free_vars<'s, 't: 's>(&'s mut self, term: &'t Rc<Term>) -> AHashSet<Rc<Term>>;
}

pub mod PrimitivePool {
    use crate::ast::Constant;

    use super::{
        super::{Rc, Sort, Term},
        TPool,
    };
    use ahash::{AHashMap, AHashSet};

    /// A structure to store and manage all allocated terms.
    ///
    /// You can add a `Term` to the pool using [`TermPool::add`], which will return an `Rc<Term>`. This
    /// struct ensures that, if two equal terms are added to a pool, they will be in the same
    /// allocation. This invariant allows terms to be safely compared and hashed by reference, instead
    /// of by value (see [`Rc`]).
    ///
    /// This struct also provides other utility methods, like computing the sort of a term (see
    /// [`TermPool::sort`]) or its free variables (see [`TermPool::free_vars`]).
    pub struct TermPool {
        /// A map of the terms in the pool.
        pub(crate) terms: AHashMap<Term, Rc<Term>>,
        pub(crate) free_vars_cache: AHashMap<Rc<Term>, AHashSet<Rc<Term>>>,
        pub(crate) sorts_cache: AHashMap<Rc<Term>, Rc<Term>>,
        pub(crate) bool_true: Rc<Term>,
        pub(crate) bool_false: Rc<Term>,
    }

    impl Default for TermPool {
        fn default() -> Self {
            Self::new()
        }
    }

    impl TermPool {
        /// Constructs a new `TermPool`. This new pool will already contain the boolean constants `true`
        /// and `false`, as well as the `Bool` sort.
        pub fn new() -> Self {
            let mut terms = AHashMap::new();
            let mut sorts_cache = AHashMap::new();
            let bool_sort = Self::add_term_to_map(&mut terms, Term::Sort(Sort::Bool));

            let [bool_true, bool_false] = ["true", "false"]
                .map(|b| Self::add_term_to_map(&mut terms, Term::new_var(b, bool_sort.clone())));

            sorts_cache.insert(bool_false.clone(), bool_sort.clone());
            sorts_cache.insert(bool_true.clone(), bool_sort.clone());
            sorts_cache.insert(bool_sort.clone(), bool_sort.clone());

            Self {
                terms,
                free_vars_cache: AHashMap::new(),
                sorts_cache,
                bool_true,
                bool_false,
            }
        }

        fn add_term_to_map(terms_map: &mut AHashMap<Term, Rc<Term>>, term: Term) -> Rc<Term> {
            use std::collections::hash_map::Entry;

            match terms_map.entry(term) {
                Entry::Occupied(occupied_entry) => occupied_entry.get().clone(),
                Entry::Vacant(vacant_entry) => {
                    let term = vacant_entry.key().clone();
                    vacant_entry.insert(Rc::new(term)).clone()
                }
            }
        }

        /// Computes the sort of a term and adds it to the sort cache.
        pub(super) fn compute_sort<'a, 'b: 'a>(&'a mut self, term: &'b Rc<Term>) -> Rc<Term> {
            use super::super::Operator;

            if self.sorts_cache.contains_key(term) {
                return self.sorts_cache[term].clone();
            }

            let result: Sort = match term.as_ref() {
                Term::Const(c) => match c {
                    Constant::Integer(_) => Sort::Int,
                    Constant::Real(_) => Sort::Real,
                    Constant::String(_) => Sort::String,
                },
                Term::Var(_, sort) => sort.as_sort().unwrap().clone(),
                Term::Op(op, args) => match op {
                    Operator::Not
                    | Operator::Implies
                    | Operator::And
                    | Operator::Or
                    | Operator::Xor
                    | Operator::Equals
                    | Operator::Distinct
                    | Operator::LessThan
                    | Operator::GreaterThan
                    | Operator::LessEq
                    | Operator::GreaterEq
                    | Operator::IsInt => Sort::Bool,
                    Operator::Ite => self.compute_sort(&args[1]).as_sort().unwrap().clone(),
                    Operator::Add | Operator::Sub | Operator::Mult => {
                        if args
                            .iter()
                            .any(|a| self.compute_sort(a).as_sort().unwrap() == &Sort::Real)
                        {
                            Sort::Real
                        } else {
                            Sort::Int
                        }
                    }
                    Operator::RealDiv | Operator::ToReal => Sort::Real,
                    Operator::IntDiv | Operator::Mod | Operator::Abs | Operator::ToInt => Sort::Int,
                    Operator::Select => match self.compute_sort(&args[0]).as_sort().unwrap() {
                        Sort::Array(_, y) => y.as_sort().unwrap().clone(),
                        _ => unreachable!(),
                    },
                    Operator::Store => self.compute_sort(&args[0]).as_sort().unwrap().clone(),
                },
                Term::App(f, _) => {
                    match self.compute_sort(f).as_sort().unwrap() {
                        Sort::Function(sorts) => sorts.last().unwrap().as_sort().unwrap().clone(),
                        _ => unreachable!(), // We assume that the function is correctly sorted
                    }
                }
                Term::Sort(sort) => sort.clone(),
                Term::Quant(_, _, _) => Sort::Bool,
                Term::Choice((_, sort), _) => sort.as_sort().unwrap().clone(),
                Term::Let(_, inner) => self.compute_sort(inner).as_sort().unwrap().clone(),
                Term::Lambda(bindings, body) => {
                    let mut result: Vec<_> =
                        bindings.iter().map(|(_name, sort)| sort.clone()).collect();
                    let return_sort = self.compute_sort(body).as_ref().clone();
                    result.push(self.add(return_sort));
                    Sort::Function(result)
                }
            };
            let sorted_term = Self::add_term_to_map(&mut self.terms, Term::Sort(result));
            self.sorts_cache.insert(term.clone(), sorted_term);
            self.sorts_cache[term].clone()
        }
    }

    impl TPool for TermPool {
        fn bool_true(&self) -> Rc<Term> {
            self.bool_true.clone()
        }

        fn bool_false(&self) -> Rc<Term> {
            self.bool_false.clone()
        }

        fn add(&mut self, term: Term) -> Rc<Term> {
            let term = Self::add_term_to_map(&mut self.terms, term);
            self.compute_sort(&term);
            term
        }

        fn sort(&self, term: &Rc<Term>) -> Rc<Term> {
            self.sorts_cache[term].clone()
        }

        fn free_vars<'s, 't: 's>(&'s mut self, term: &'t Rc<Term>) -> AHashSet<Rc<Term>> {
            // Here, I would like to do
            // ```
            // if let Some(vars) = self.free_vars_cache.get(term) {
            //     return vars;
            // }
            // ```
            // However, because of a limitation in the borrow checker, the compiler thinks that
            // this immutable borrow of `cache` has to live until the end of the function, even
            // though the code immediately returns. This would stop me from mutating `cache` in the
            // rest of the function. Because of that, I have to check if the hash map contains
            // `term` as a key, and then get the value associated with it, meaning I have to access
            // the hash map twice, which is a bit slower. This is an example of problem case #3
            // from the non-lexical lifetimes RFC:
            // https://github.com/rust-lang/rfcs/blob/master/text/2094-nll.md
            if self.free_vars_cache.contains_key(term) {
                return self.free_vars_cache.get(term).unwrap().clone();
            }
            let set = match term.as_ref() {
                Term::App(f, args) => {
                    let mut set = self.free_vars(f).clone();
                    for a in args {
                        set.extend(self.free_vars(a).iter().cloned());
                    }
                    set
                }
                Term::Op(_, args) => {
                    let mut set = AHashSet::new();
                    for a in args {
                        set.extend(self.free_vars(a).iter().cloned());
                    }
                    set
                }
                Term::Quant(_, bindings, inner) | Term::Lambda(bindings, inner) => {
                    let mut vars = self.free_vars(inner).clone();
                    for bound_var in bindings {
                        let term = self.add(bound_var.clone().into());
                        vars.remove(&term);
                    }
                    vars
                }
                Term::Let(bindings, inner) => {
                    let mut vars = self.free_vars(inner).clone();
                    for (var, value) in bindings {
                        let sort = self.sort(value).as_ref().clone();
                        let sort = self.add(sort);
                        let term = self.add((var.clone(), sort).into());
                        vars.remove(&term);
                    }
                    vars
                }
                Term::Choice(bound_var, inner) => {
                    let mut vars = self.free_vars(inner).clone();
                    let term = self.add(bound_var.clone().into());
                    vars.remove(&term);
                    vars
                }
                Term::Var(..) => {
                    let mut set = AHashSet::with_capacity(1);
                    set.insert(term.clone());
                    set
                }
                Term::Const(_) | Term::Sort(_) => AHashSet::new(),
            };
            self.free_vars_cache.insert(term.clone(), set);
            self.free_vars_cache.get(term).unwrap().clone()
        }
    }
}

pub mod AdvancedPools {
    use super::super::{Rc, Term};
    use super::{PrimitivePool, TPool};
    use ahash::AHashSet;
    use std::sync::{Arc, RwLock};

    pub struct ContextPool {
        pub(crate) global_pool: Arc<PrimitivePool::TermPool>,
        pub(crate) storage: Arc<RwLock<PrimitivePool::TermPool>>,
    }

    impl Default for ContextPool {
        fn default() -> Self {
            Self::new()
        }
    }

    impl ContextPool {
        pub fn new() -> Self {
            Self {
                global_pool: Arc::new(PrimitivePool::TermPool::new()),
                storage: Arc::new(RwLock::new(PrimitivePool::TermPool::new())),
            }
        }

        pub fn from_global(global_pool: &Arc<PrimitivePool::TermPool>) -> Self {
            Self {
                global_pool: global_pool.clone(),
                storage: Arc::new(RwLock::new(PrimitivePool::TermPool::new())),
            }
        }

        pub fn from_previous(ctx_pool: &Self) -> Self {
            Self {
                global_pool: ctx_pool.global_pool.clone(),
                storage: ctx_pool.storage.clone(),
            }
        }

        /// Takes a term and returns an `Rc` referencing it. Receive the pools references directly.
        fn add_by_ref<'d, 'c: 'd>(
            ctx_pool: &mut PrimitivePool::TermPool,
            global_pool: &'d Arc<PrimitivePool::TermPool>,
            term: Term,
        ) -> Rc<Term> {
            use std::collections::hash_map::Entry;

            // If the global pool has the term
            if let Some(entry) = global_pool.terms.get(&term) {
                entry.clone()
            } else {
                match ctx_pool.terms.entry(term) {
                    Entry::Occupied(occupied_entry) => occupied_entry.get().clone(),
                    Entry::Vacant(vacant_entry) => {
                        let term = vacant_entry.key().clone();
                        let t = vacant_entry.insert(Rc::new(term)).clone();
                        ctx_pool.compute_sort(&t);
                        t
                    }
                }
            }
        }

        /// Returns the sort of this term exactly as the sort function. Receive the pools references directly.
        fn sort_by_ref<'d: 't, 'c: 'd, 't>(
            ctx_pool: &PrimitivePool::TermPool,
            global_pool: &'d Arc<PrimitivePool::TermPool>,
            term: &'t Rc<Term>,
        ) -> Rc<Term> {
            if let Some(sort) = global_pool.sorts_cache.get(term) {
                sort.clone()
            }
            // A sort inserted by context
            else {
                ctx_pool.sorts_cache[term].clone()
            }
        }
    }

    impl TPool for ContextPool {
        fn bool_true(&self) -> Rc<Term> {
            self.global_pool.bool_true.clone()
        }

        fn bool_false(&self) -> Rc<Term> {
            self.global_pool.bool_false.clone()
        }

        fn add(&mut self, term: Term) -> Rc<Term> {
            use std::collections::hash_map::Entry;

            // If the global pool has the term
            if let Some(entry) = self.global_pool.terms.get(&term) {
                entry.clone()
            } else {
                let mut ctx_guard = self.storage.write().unwrap();
                match ctx_guard.terms.entry(term) {
                    Entry::Occupied(occupied_entry) => occupied_entry.get().clone(),
                    Entry::Vacant(vacant_entry) => {
                        let term = vacant_entry.key().clone();
                        let t = vacant_entry.insert(Rc::new(term)).clone();
                        ctx_guard.compute_sort(&t);
                        t
                    }
                }
            }
        }

        fn sort(&self, term: &Rc<Term>) -> Rc<Term> {
            if let Some(sort) = self.global_pool.sorts_cache.get(term) {
                sort.clone()
            }
            // A sort inserted by context
            else {
                self.storage.read().unwrap().sorts_cache[term].clone()
            }
        }

        fn free_vars<'s, 't: 's>(&'s mut self, term: &'t Rc<Term>) -> AHashSet<Rc<Term>> {
            fn internal<'d: 't, 'c: 'd, 't>(
                ctx_pool: &'d mut PrimitivePool::TermPool,
                global_pool: &'c Arc<PrimitivePool::TermPool>,
                term: &'t Rc<Term>,
            ) -> &'t AHashSet<Rc<Term>> {
                // Here, I would like to do
                // ```
                // if let Some(vars) = self.free_vars_cache.get(term) {
                //     return vars;
                // }
                // ```
                // However, because of a limitation in the borrow checker, the compiler thinks that
                // this immutable borrow of `cache` has to live until the end of the function, even
                // though the code immediately returns. This would stop me from mutating `cache` in the
                // rest of the function. Because of that, I have to check if the hash map contains
                // `term` as a key, and then get the value associated with it, meaning I have to access
                // the hash map twice, which is a bit slower. This is an example of problem case #3
                // from the non-lexical lifetimes RFC:
                // https://github.com/rust-lang/rfcs/blob/master/text/2094-nll.md
                if let Some(set) = global_pool.free_vars_cache.get(term) {
                    return set;
                }
                if ctx_pool.free_vars_cache.contains_key(term) {
                    return ctx_pool.free_vars_cache.get(term).unwrap();
                }

                let set = match term.as_ref() {
                    Term::App(f, args) => {
                        let mut set = internal(ctx_pool, global_pool, f).clone();
                        for a in args {
                            set.extend(internal(ctx_pool, global_pool, a).iter().cloned());
                        }
                        set
                    }
                    Term::Op(_, args) => {
                        let mut set = AHashSet::new();
                        for a in args {
                            set.extend(internal(ctx_pool, global_pool, a).iter().cloned());
                        }
                        set
                    }
                    Term::Quant(_, bindings, inner) | Term::Lambda(bindings, inner) => {
                        let mut vars = internal(ctx_pool, global_pool, inner).clone();
                        for bound_var in bindings {
                            let term = ContextPool::add_by_ref(
                                ctx_pool,
                                global_pool,
                                bound_var.clone().into(),
                            );
                            vars.remove(&term);
                        }
                        vars
                    }
                    Term::Let(bindings, inner) => {
                        let mut vars = internal(ctx_pool, global_pool, inner).clone();
                        for (var, value) in bindings {
                            let sort = ContextPool::sort_by_ref(ctx_pool, global_pool, value)
                                .as_ref()
                                .clone();
                            let sort = ContextPool::add_by_ref(ctx_pool, global_pool, sort);
                            let term = ContextPool::add_by_ref(
                                ctx_pool,
                                global_pool,
                                (var.clone(), sort).into(),
                            );
                            vars.remove(&term);
                        }
                        vars
                    }
                    Term::Choice(bound_var, inner) => {
                        let mut vars = internal(ctx_pool, global_pool, inner).clone();
                        let term = ContextPool::add_by_ref(
                            ctx_pool,
                            global_pool,
                            bound_var.clone().into(),
                        );
                        vars.remove(&term);
                        vars
                    }
                    Term::Var(..) => {
                        let mut set = AHashSet::with_capacity(1);
                        set.insert(term.clone());
                        set
                    }
                    Term::Const(_) | Term::Sort(_) => AHashSet::new(),
                };
                ctx_pool.free_vars_cache.insert(term.clone(), set);
                ctx_pool.free_vars_cache.get(term).unwrap()
            }
            let mut ctx_guard = self.storage.write();
            internal(ctx_guard.as_mut().unwrap(), &self.global_pool, term).clone()
        }
    }

    // =========================================================================

    pub struct LocalPool {
        pub(crate) ctx_pool: ContextPool,
        pub(crate) storage: PrimitivePool::TermPool,
    }

    impl Default for LocalPool {
        fn default() -> Self {
            Self::new()
        }
    }

    impl LocalPool {
        pub fn new() -> Self {
            Self {
                ctx_pool: ContextPool::new(),
                storage: PrimitivePool::TermPool::new(),
            }
        }

        /// Instantiates a new `LocalPool` from a previous `ContextPool` (makes
        /// sure the context is shared between threads).
        pub fn from_previous(ctx_pool: &ContextPool) -> Self {
            Self {
                ctx_pool: ContextPool::from_previous(ctx_pool),
                storage: PrimitivePool::TermPool::new(),
            }
        }

        /// Takes a term and returns an `Rc` referencing it. Receive the pools references directly.
        fn add_by_ref<'d, 'c: 'd>(
            local_pool: &'d mut PrimitivePool::TermPool,
            ctx_pool: &PrimitivePool::TermPool,
            global_pool: &'d Arc<PrimitivePool::TermPool>,
            term: Term,
        ) -> Rc<Term> {
            use std::collections::hash_map::Entry;

            // If the global pool has the term
            if let Some(entry) = global_pool.terms.get(&term) {
                entry.clone()
            }
            // If this term was inserted by the context
            else if let Some(entry) = ctx_pool.terms.get(&term) {
                entry.clone()
            } else {
                match local_pool.terms.entry(term) {
                    Entry::Occupied(occupied_entry) => occupied_entry.get().clone(),
                    Entry::Vacant(vacant_entry) => {
                        let term = vacant_entry.key().clone();
                        let t = vacant_entry.insert(Rc::new(term)).clone();
                        local_pool.compute_sort(&t);
                        t
                    }
                }
            }
        }

        /// Returns the sort of this term exactly as the sort function. Receive the pools references directly.
        fn sort_by_ref<'d: 't, 'c: 'd, 't>(
            local_pool: &'d mut PrimitivePool::TermPool,
            ctx_pool: &PrimitivePool::TermPool,
            global_pool: &'d Arc<PrimitivePool::TermPool>,
            term: &'t Rc<Term>,
        ) -> Rc<Term> {
            if let Some(sort) = global_pool.sorts_cache.get(term) {
                sort.clone()
            }
            // A sort inserted by context
            else if let Some(entry) = ctx_pool.terms.get(&term) {
                entry.clone()
            } else {
                local_pool.sorts_cache[term].clone()
            }
        }
    }

    impl TPool for LocalPool {
        fn bool_true(&self) -> Rc<Term> {
            self.ctx_pool.global_pool.bool_true.clone()
        }

        fn bool_false(&self) -> Rc<Term> {
            self.ctx_pool.global_pool.bool_false.clone()
        }

        fn add(&mut self, term: Term) -> Rc<Term> {
            use std::collections::hash_map::Entry;

            // If there is a constant pool and has the term
            if let Some(entry) = self.ctx_pool.global_pool.terms.get(&term) {
                entry.clone()
            }
            // If this term was inserted by the context
            else if let Some(entry) = self.ctx_pool.storage.read().unwrap().terms.get(&term) {
                entry.clone()
            } else {
                match self.storage.terms.entry(term) {
                    Entry::Occupied(occupied_entry) => occupied_entry.get().clone(),
                    Entry::Vacant(vacant_entry) => {
                        let term = vacant_entry.key().clone();
                        let t = vacant_entry.insert(Rc::new(term)).clone();
                        self.storage.compute_sort(&t);
                        t
                    }
                }
            }
        }

        fn sort(&self, term: &Rc<Term>) -> Rc<Term> {
            if let Some(sort) = self.ctx_pool.global_pool.sorts_cache.get(term) {
                sort.clone()
            }
            // A sort inserted by context
            else if let Some(entry) = self.ctx_pool.storage.read().unwrap().terms.get(&term) {
                entry.clone()
            } else {
                self.storage.sorts_cache[term].clone()
            }
        }

        fn free_vars<'s, 't: 's>(&'s mut self, term: &'t Rc<Term>) -> AHashSet<Rc<Term>> {
            fn internal<'d: 't, 'c: 'd, 't>(
                local_pool: &'d mut PrimitivePool::TermPool,
                ctx_pool: &'t PrimitivePool::TermPool,
                global_pool: &'d Arc<PrimitivePool::TermPool>,
                term: &'t Rc<Term>,
            ) -> &'t AHashSet<Rc<Term>> {
                // Here, I would like to do
                // ```
                // if let Some(vars) = self.free_vars_cache.get(term) {
                //     return vars;
                // }
                // ```
                // However, because of a limitation in the borrow checker, the compiler thinks that
                // this immutable borrow of `cache` has to live until the end of the function, even
                // though the code immediately returns. This would stop me from mutating `cache` in the
                // rest of the function. Because of that, I have to check if the hash map contains
                // `term` as a key, and then get the value associated with it, meaning I have to access
                // the hash map twice, which is a bit slower. This is an example of problem case #3
                // from the non-lexical lifetimes RFC:
                // https://github.com/rust-lang/rfcs/blob/master/text/2094-nll.md
                if let Some(set) = global_pool.free_vars_cache.get(term) {
                    return set;
                }
                if let Some(set) = ctx_pool.free_vars_cache.get(term) {
                    return set;
                }
                if local_pool.free_vars_cache.contains_key(term) {
                    return local_pool.free_vars_cache.get(term).unwrap();
                }

                let set = match term.as_ref() {
                    Term::App(f, args) => {
                        let mut set = internal(local_pool, ctx_pool, global_pool, f).clone();
                        for a in args {
                            set.extend(
                                internal(local_pool, ctx_pool, global_pool, a)
                                    .iter()
                                    .cloned(),
                            );
                        }
                        set
                    }
                    Term::Op(_, args) => {
                        let mut set = AHashSet::new();
                        for a in args {
                            set.extend(
                                internal(local_pool, ctx_pool, global_pool, a)
                                    .iter()
                                    .cloned(),
                            );
                        }
                        set
                    }
                    Term::Quant(_, bindings, inner) | Term::Lambda(bindings, inner) => {
                        let mut vars = internal(local_pool, ctx_pool, global_pool, inner).clone();
                        for bound_var in bindings {
                            let term = LocalPool::add_by_ref(
                                local_pool,
                                ctx_pool,
                                global_pool,
                                bound_var.clone().into(),
                            );
                            vars.remove(&term);
                        }
                        vars
                    }
                    Term::Let(bindings, inner) => {
                        let mut vars = internal(local_pool, ctx_pool, global_pool, inner).clone();
                        for (var, value) in bindings {
                            let sort =
                                LocalPool::sort_by_ref(local_pool, ctx_pool, global_pool, value)
                                    .as_ref()
                                    .clone();
                            let sort =
                                LocalPool::add_by_ref(local_pool, ctx_pool, global_pool, sort);
                            let term = LocalPool::add_by_ref(
                                local_pool,
                                ctx_pool,
                                global_pool,
                                (var.clone(), sort).into(),
                            );
                            vars.remove(&term);
                        }
                        vars
                    }
                    Term::Choice(bound_var, inner) => {
                        let mut vars = internal(local_pool, ctx_pool, global_pool, inner).clone();
                        let term = LocalPool::add_by_ref(
                            local_pool,
                            ctx_pool,
                            global_pool,
                            bound_var.clone().into(),
                        );
                        vars.remove(&term);
                        vars
                    }
                    Term::Var(..) => {
                        let mut set = AHashSet::with_capacity(1);
                        set.insert(term.clone());
                        set
                    }
                    Term::Const(_) | Term::Sort(_) => AHashSet::new(),
                };
                local_pool.free_vars_cache.insert(term.clone(), set);
                local_pool.free_vars_cache.get(term).unwrap()
            }

            internal(
                &mut self.storage,
                &self.ctx_pool.storage.read().unwrap(),
                &self.ctx_pool.global_pool,
                term,
            )
            .clone()
        }
    }
}
