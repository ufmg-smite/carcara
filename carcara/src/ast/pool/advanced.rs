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

    fn free_vars(&mut self, term: &Rc<Term>) -> AHashSet<Rc<Term>> {
        self.storage
            .write()
            .unwrap()
            .free_vars_with_priorities(term, [&self.global_pool])
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

    fn free_vars(&mut self, term: &Rc<Term>) -> AHashSet<Rc<Term>> {
        self.storage.free_vars_with_priorities(
            term,
            [
                &self.ctx_pool.global_pool,
                &self.ctx_pool.storage.read().unwrap(),
            ],
        )
    }
}
