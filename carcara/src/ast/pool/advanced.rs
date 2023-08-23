use super::super::{Rc, Term};
use super::{PrimitivePool, TermPool};
use indexmap::IndexSet;
use std::sync::{Arc, RwLock};

pub struct ContextPool {
    pub(crate) global_pool: Arc<PrimitivePool>,
    pub(crate) inner: Arc<RwLock<PrimitivePool>>,
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
            inner: Arc::new(RwLock::new(PrimitivePool::new())),
        }
    }

    pub fn from_global(global_pool: &Arc<PrimitivePool>) -> Self {
        Self {
            global_pool: global_pool.clone(),
            inner: Arc::new(RwLock::new(PrimitivePool::new())),
        }
    }

    pub fn from_previous(ctx_pool: &Self) -> Self {
        Self {
            global_pool: ctx_pool.global_pool.clone(),
            inner: ctx_pool.inner.clone(),
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
        // If the global pool has the term
        if let Some(entry) = self.global_pool.storage.get(&term) {
            return entry.clone();
        }
        let mut ctx_guard = self.inner.write().unwrap();
        let term = ctx_guard.storage.add(term);
        ctx_guard.compute_sort(&term);
        term
    }

    fn sort(&self, term: &Rc<Term>) -> Rc<Term> {
        if let Some(sort) = self.global_pool.sorts_cache.get(term) {
            sort.clone()
        }
        // A sort inserted by context
        else {
            self.inner.read().unwrap().sorts_cache[term].clone()
        }
    }

    fn free_vars(&mut self, term: &Rc<Term>) -> IndexSet<Rc<Term>> {
        self.inner
            .write()
            .unwrap()
            .free_vars_with_priorities(term, [&self.global_pool])
    }
}

// =========================================================================

pub struct LocalPool {
    pub(crate) ctx_pool: ContextPool,
    pub(crate) inner: PrimitivePool,
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
            inner: PrimitivePool::new(),
        }
    }

    /// Instantiates a new `LocalPool` from a previous `ContextPool` (makes
    /// sure the context is shared between threads).
    pub fn from_previous(ctx_pool: &ContextPool) -> Self {
        Self {
            ctx_pool: ContextPool::from_previous(ctx_pool),
            inner: PrimitivePool::new(),
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
        // If there is a constant pool and has the term
        if let Some(entry) = self.ctx_pool.global_pool.storage.get(&term) {
            entry.clone()
        }
        // If this term was inserted by the context
        else if let Some(entry) = self.ctx_pool.inner.read().unwrap().storage.get(&term) {
            entry.clone()
        } else {
            self.inner.add(term)
        }
    }

    fn sort(&self, term: &Rc<Term>) -> Rc<Term> {
        if let Some(sort) = self.ctx_pool.global_pool.sorts_cache.get(term) {
            sort.clone()
        }
        // A sort inserted by context
        else if let Some(entry) = self.ctx_pool.inner.read().unwrap().storage.get(term) {
            entry.clone()
        } else {
            self.inner.sorts_cache[term].clone()
        }
    }

    fn free_vars(&mut self, term: &Rc<Term>) -> IndexSet<Rc<Term>> {
        self.inner.free_vars_with_priorities(
            term,
            [
                &self.ctx_pool.global_pool,
                &self.ctx_pool.inner.read().unwrap(),
            ],
        )
    }
}
