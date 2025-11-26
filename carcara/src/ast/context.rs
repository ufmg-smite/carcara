use crate::ast::*;
use std::sync::{atomic::AtomicUsize, Arc, RwLock, RwLockReadGuard, RwLockWriteGuard};

#[derive(Debug)]
pub struct Context {
    pub args: Vec<AnchorArg>,
    pub cumulative_substitution: Option<Substitution>,
}

impl Context {
    /// Builds a new context form the arguments to an `anchor`. This does not initalize the
    /// `cumulative_substitution` field.
    fn new(args: Vec<AnchorArg>) -> Self {
        Self { args, cumulative_substitution: None }
    }
}

/// A tuple that will represent a single `Context` and allows a `Context` to be shared between threads.
///
/// `0`: Number of threads that will use this context.
///
/// `1`: Shareable and droppable slot for the context.
type ContextInfo = (AtomicUsize, RwLock<Option<Context>>);

/// Struct that implements a thread-shared context stack. That way, this stack
/// tries to use an already existing global `Context` (built by another thread).
/// If it was still not built, then the current thread is going to build this
/// context so other threads can also use it.
#[derive(Default, Debug)]
pub struct ContextStack {
    /// The context vector that is shared globally between all the threads.
    /// The contexts storage is index based (which the index of each context is
    /// defined by the anchor/subproof id obtained in the parser).
    context_vec: Arc<Vec<ContextInfo>>,
    /// The stack of contexts id (works just like a map to `context_vec`).
    stack: Vec<usize>,
    num_cumulative_calculated: usize,
}

impl ContextStack {
    pub fn new() -> Self {
        Default::default()
    }

    /// Creates an empty stack from contexts usage info (a vector indicating how
    /// many threads are going to use each context).
    pub fn from_usage(context_usage: &Vec<usize>) -> Self {
        let mut context_vec: Arc<Vec<ContextInfo>> = Arc::new(vec![]);
        let ctx_ref = Arc::get_mut(&mut context_vec).unwrap();

        for &usage in context_usage {
            ctx_ref.push((AtomicUsize::new(usage), RwLock::new(None)));
        }

        Self {
            context_vec,
            stack: vec![],
            num_cumulative_calculated: 0,
        }
    }

    /// Creates an empty stack from a previous stack (starts with context infos
    /// already instantiated).
    pub fn from_previous(&self) -> Self {
        Self {
            context_vec: self.context_vec.clone(),
            stack: vec![],
            num_cumulative_calculated: 0,
        }
    }

    pub fn len(&self) -> usize {
        self.stack.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn last(&self) -> Option<RwLockReadGuard<'_, Option<Context>>> {
        self.stack
            .last()
            .map(|id| self.context_vec[*id].1.read().unwrap())
    }

    pub fn last_mut(&mut self) -> Option<RwLockWriteGuard<'_, Option<Context>>> {
        self.stack
            .last_mut()
            .map(|id| self.context_vec[*id].1.write().unwrap())
    }

    /// A function used to force the creation of a new context at the end of the
    /// `context_vec`. This function should be called before a
    /// `ContextStack::push` in a single thread operation. Since a single
    /// thread doesn't require a schedule balancing, then there is no info about
    /// how many contexts there are in the proof (and it's not needed since we
    /// can always add a new context at the end of the vector just like an usual
    /// stack)
    fn force_new_context(&mut self) -> usize {
        let ctx_vec = Arc::get_mut(&mut self.context_vec).unwrap();
        ctx_vec.push((AtomicUsize::new(1), RwLock::new(None)));
        ctx_vec.len() - 1
    }

    pub fn push(&mut self, args: &[AnchorArg]) {
        let id = self.force_new_context();
        self.push_with_id(args, id);
    }

    pub fn push_with_id(&mut self, args: &[AnchorArg], context_id: usize) {
        // The write guard was yielded to this thread
        if let Ok(mut ctx_write_guard) = self.context_vec[context_id].1.try_write() {
            // It's the first thread trying to build this context. It will
            // build this context at the context vec (accessible for all threads)
            if ctx_write_guard.is_none() {
                *ctx_write_guard = Some(Context::new(args.to_vec()));
            }
        }
        // Adds this context in the stack
        // Notice that even though the context is not ready for use, the write
        // guard is still being held by some thread, then if this context is
        // required at any moment, then we are assured it will wait until the
        // fully context construction
        self.stack.push(context_id);
    }

    pub fn pop(&mut self) {
        use std::sync::atomic::Ordering;

        if let Some(id) = self.stack.pop() {
            let this_context = &self.context_vec[id];

            let mut remaining_threads = this_context.0.load(Ordering::Acquire);
            remaining_threads = remaining_threads
                .checked_sub(1)
                .expect("A thread tried to access a context not allocated for it.");

            if remaining_threads == 0 {
                // Drop this context since the last thread stopped using it
                *this_context.1.write().unwrap() = None;
            }
            this_context.0.store(remaining_threads, Ordering::Release);
        }

        self.num_cumulative_calculated =
            std::cmp::min(self.num_cumulative_calculated, self.stack.len());
    }

    fn catch_up_cumulative(&mut self, pool: &mut dyn TermPool, up_to: usize) {
        for i in self.num_cumulative_calculated..std::cmp::max(up_to + 1, self.len()) {
            // Requires read guard. Since the i-th context will be mutated far
            // below this line, we first take the read guard here and then, when
            // necessary, we require the write guard. This tries to avoid bigger
            // overheads
            let context_guard = self.context_vec[self.stack[i]].1.read().unwrap();
            let current_context = context_guard.as_ref().unwrap();

            let mut substitution = if i > 0 {
                // Waits until OS allows to read this previous context. The code structure
                // makes sure that this context, when released for reading, will be already
                // instantiated since there are only 2 cases:
                //  - This thread was responsible for building this previous context. Then
                //      this context has already been built.
                //  - Another thread was assigned to build this context. Then, it doesn't
                //      matter if this other thread has already finished the process, the
                //      current thread will have to wait until the guard is released.
                let guard = self.context_vec[self.stack[i - 1]].1.read().unwrap();
                guard
                    .as_ref()
                    .unwrap()
                    .cumulative_substitution
                    .clone()
                    .unwrap()
            } else {
                Substitution::empty()
            };

            for a in &current_context.args {
                match a {
                    AnchorArg::Variable((name, sort)) => {
                        let var_term = pool.add(Term::new_var(name, sort.clone()));
                        substitution.remove(&var_term);
                    }
                    AnchorArg::Assign(var, value) => {
                        let var_term = pool.add(var.clone().into());
                        let new_value = substitution.apply(pool, value);
                        // It is safe to unwrap here because we ensure by contruction that
                        // `var_term` is a variable term, with he same sort as `value`
                        substitution
                            .insert(pool, var_term, new_value.clone())
                            .unwrap();
                    }
                }
            }

            // Drop the read guard, and acquire a write guard
            drop(context_guard);
            let mut context_guard = self.context_vec[self.stack[i]].1.write().unwrap();
            context_guard.as_mut().unwrap().cumulative_substitution = Some(substitution);
            self.num_cumulative_calculated = i + 1;
        }
    }

    pub fn apply_previous(&mut self, pool: &mut dyn TermPool, term: &Rc<Term>) -> Rc<Term> {
        if self.len() < 2 {
            term.clone()
        } else {
            let index = self.len() - 2;
            self.catch_up_cumulative(pool, index);
            self.context_vec[self.stack[index]]
                .1
                .write()
                .unwrap()
                .as_mut()
                .unwrap()
                .cumulative_substitution
                .as_mut()
                .unwrap()
                .apply(pool, term)
        }
    }

    pub fn apply(&mut self, pool: &mut dyn TermPool, term: &Rc<Term>) -> Rc<Term> {
        if self.is_empty() {
            term.clone()
        } else {
            let index = self.len() - 1;
            self.catch_up_cumulative(pool, index);
            self.context_vec[self.stack[index]]
                .1
                .write()
                .unwrap()
                .as_mut()
                .unwrap()
                .cumulative_substitution
                .as_mut()
                .unwrap()
                .apply(pool, term)
        }
    }
}
