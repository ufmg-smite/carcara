use super::super::{Rc, Term};
use super::{PrimitivePool, TermPool};
use ahash::AHashSet;
use std::sync::{Arc, RwLock};

pub struct ContextPool {
    pub(crate) global_pool: Arc<PrimitivePool>,
    pub(crate) storage: Arc<RwLock<PrimitivePool>>,
}

impl Default for ContextPool {
    fn default() -> Self {
        Self::new()
    }
}

impl ContextPool {
    pub fn new() -> Self {
        Self {
            global_pool: Arc::new(PrimitivePool::new()),
            storage: Arc::new(RwLock::new(PrimitivePool::new())),
        }
    }

    pub fn from_global(global_pool: &Arc<PrimitivePool>) -> Self {
        Self {
            global_pool: global_pool.clone(),
            storage: Arc::new(RwLock::new(PrimitivePool::new())),
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
        ctx_pool: &mut PrimitivePool,
        global_pool: &'d PrimitivePool,
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
        ctx_pool: &PrimitivePool,
        global_pool: &'d PrimitivePool,
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

impl TermPool for ContextPool {
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
            ctx_pool: &'d mut PrimitivePool,
            global_pool: &'c PrimitivePool,
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
                    let term =
                        ContextPool::add_by_ref(ctx_pool, global_pool, bound_var.clone().into());
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
    pub(crate) storage: PrimitivePool,
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
            storage: PrimitivePool::new(),
        }
    }

    /// Instantiates a new `LocalPool` from a previous `ContextPool` (makes
    /// sure the context is shared between threads).
    pub fn from_previous(ctx_pool: &ContextPool) -> Self {
        Self {
            ctx_pool: ContextPool::from_previous(ctx_pool),
            storage: PrimitivePool::new(),
        }
    }

    /// Takes a term and returns an `Rc` referencing it. Receive the pools references directly.
    fn add_by_ref<'d, 'c: 'd>(
        local_pool: &'d mut PrimitivePool,
        ctx_pool: &PrimitivePool,
        global_pool: &'d PrimitivePool,
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
        local_pool: &'d mut PrimitivePool,
        ctx_pool: &PrimitivePool,
        global_pool: &'d PrimitivePool,
        term: &'t Rc<Term>,
    ) -> Rc<Term> {
        if let Some(sort) = global_pool.sorts_cache.get(term) {
            sort.clone()
        }
        // A sort inserted by context
        else if let Some(entry) = ctx_pool.terms.get(term) {
            entry.clone()
        } else {
            local_pool.sorts_cache[term].clone()
        }
    }
}

impl TermPool for LocalPool {
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
        else if let Some(entry) = self.ctx_pool.storage.read().unwrap().terms.get(term) {
            entry.clone()
        } else {
            self.storage.sorts_cache[term].clone()
        }
    }

    fn free_vars<'s, 't: 's>(&'s mut self, term: &'t Rc<Term>) -> AHashSet<Rc<Term>> {
        fn internal<'d: 't, 'c: 'd, 't>(
            local_pool: &'d mut PrimitivePool,
            ctx_pool: &'t PrimitivePool,
            global_pool: &'d PrimitivePool,
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
                        let sort = LocalPool::sort_by_ref(local_pool, ctx_pool, global_pool, value)
                            .as_ref()
                            .clone();
                        let sort = LocalPool::add_by_ref(local_pool, ctx_pool, global_pool, sort);
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
