use crate::ast::*;
use ahash::AHashSet;

#[cfg(not(feature = "thread-safety"))]
pub type ContextStack = SingleThreadContextStack::ContextStack;

#[cfg(feature = "thread-safety")]
pub type ContextStack = MultiThreadContextStack::ContextStack;

pub struct Context {
    pub mappings: Vec<(Rc<Term>, Rc<Term>)>,
    pub bindings: AHashSet<SortedVar>,
    pub cumulative_substitution: Option<Substitution>,
}

#[allow(non_snake_case)]
#[allow(dead_code)]
pub mod SingleThreadContextStack {
    use super::Context;
    use crate::ast::*;

    #[derive(Default)]
    pub struct ContextStack {
        stack: Vec<Context>,
        num_cumulative_calculated: usize,
    }

    impl ContextStack {
        pub fn new() -> Self {
            Default::default()
        }

        pub fn len(&self) -> usize {
            self.stack.len()
        }

        pub fn is_empty(&self) -> bool {
            self.len() == 0
        }

        pub fn last(&self) -> Option<&Context> {
            self.stack.last()
        }

        pub fn last_mut(&mut self) -> Option<&mut Context> {
            self.stack.last_mut()
        }

        pub fn push(
            &mut self,
            pool: &mut TermPool,
            assignment_args: &[(String, Rc<Term>)],
            variable_args: &[SortedVar],
        ) -> Result<(), SubstitutionError> {
            // Since some rules (like `refl`) need to apply substitutions until a fixed point, we
            // precompute these substitutions into a separate hash map. This assumes that the assignment
            // arguments are in the correct order.
            let mut substitution = Substitution::empty();
            let mut substitution_until_fixed_point = Substitution::empty();

            // We build the `substitution_until_fixed_point` hash map from the bottom up, by using the
            // substitutions already introduced to transform the result of a new substitution before
            // inserting it into the hash map. So for instance, if the substitutions are `(:= y z)` and
            // `(:= x (f y))`, we insert the first substitution, and then, when introducing the second,
            // we use the current state of the hash map to transform `(f y)` into `(f z)`. The
            // resulting hash map will then contain `(:= y z)` and `(:= x (f z))`
            for (var, value) in assignment_args.iter() {
                let sort = Term::Sort(pool.sort(value).clone());
                let var_term = Term::var(var, pool.add(sort));
                let var_term = pool.add(var_term);
                substitution.insert(pool, var_term.clone(), value.clone())?;
                let new_value = substitution_until_fixed_point.apply(pool, value);
                substitution_until_fixed_point.insert(pool, var_term, new_value)?;
            }

            let mappings = assignment_args
                .iter()
                .map(|(var, value)| {
                    let sort = Term::Sort(pool.sort(value).clone());
                    let var_term = (var.clone(), pool.add(sort)).into();
                    (pool.add(var_term), value.clone())
                })
                .collect();
            let bindings = variable_args.iter().cloned().collect();
            self.stack.push(Context {
                mappings,
                bindings,
                cumulative_substitution: None,
            });
            Ok(())
        }

        pub fn pop(&mut self) {
            self.stack.pop();
            self.num_cumulative_calculated =
                std::cmp::min(self.num_cumulative_calculated, self.stack.len());
        }

        fn catch_up_cumulative(&mut self, pool: &mut TermPool, up_to: usize) {
            for i in self.num_cumulative_calculated..std::cmp::max(up_to + 1, self.len()) {
                let simultaneous =
                    super::build_simultaneous_substitution(pool, &self.stack[i].mappings).map;
                let mut cumulative_substitution = simultaneous.clone();

                if i > 0 {
                    if let Some(previous_context) = self.stack.get(i - 1) {
                        let previous_substitution =
                            previous_context.cumulative_substitution.as_ref().unwrap();

                        for (k, v) in previous_substitution.map.iter() {
                            let value = match simultaneous.get(v) {
                                Some(new_value) => new_value,
                                None => v,
                            };
                            cumulative_substitution.insert(k.clone(), value.clone());
                        }
                    }
                }
                self.stack[i].cumulative_substitution =
                    Some(Substitution::new(pool, cumulative_substitution).unwrap());
                self.num_cumulative_calculated = i + 1;
            }
        }

        fn get_substitution(&mut self, pool: &mut TermPool, index: usize) -> &mut Substitution {
            assert!(index < self.len());
            self.catch_up_cumulative(pool, index);
            self.stack[index].cumulative_substitution.as_mut().unwrap()
        }

        pub fn apply_previous(&mut self, pool: &mut TermPool, term: &Rc<Term>) -> Rc<Term> {
            if self.len() < 2 {
                term.clone()
            } else {
                self.get_substitution(pool, self.len() - 2)
                    .apply(pool, term)
            }
        }

        pub fn apply(&mut self, pool: &mut TermPool, term: &Rc<Term>) -> Rc<Term> {
            if self.is_empty() {
                term.clone()
            } else {
                self.get_substitution(pool, self.len() - 1)
                    .apply(pool, term)
            }
        }
    }
}

#[allow(non_snake_case)]
pub mod MultiThreadContextStack {
    use std::sync::{Arc, Mutex, RwLock, RwLockReadGuard, RwLockWriteGuard};

    use super::Context;
    use crate::ast::*;

    #[derive(Default)]
    pub struct ContextStack {
        /// 0: Number of threads that will use this context.
        /// 1: Slot for the context
        /// 2: Boolean indicating whether the context was already built.
        context_vec: Arc<Vec<(RwLock<usize>, RwLock<Option<Context>>, Mutex<bool>)>>,
        stack: Vec<usize>,
        num_cumulative_calculated: usize,
    }

    impl ContextStack {
        pub fn new() -> Self {
            Default::default()
        }

        /// Creates an empty stack from contexts thread usage infos
        pub fn from_usage(context_usage: &Vec<usize>) -> Self {
            let mut context_vec = Arc::new(vec![]);
            let ctx_ref = Arc::get_mut(&mut context_vec).unwrap();

            for &usage in context_usage {
                ctx_ref.push((RwLock::new(usage), RwLock::new(None), Mutex::new(false)));
            }

            Self {
                context_vec,
                stack: vec![],
                num_cumulative_calculated: 0,
            }
        }

        /// Creates an empty stack but with context infos already instantiated
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

        pub fn last(&self) -> Option<RwLockReadGuard<Option<Context>>> {
            self.stack.last().and_then(|&id| {
                // Wait until the OS allow this thread to read the context vector
                Some(self.context_vec[id].1.read().unwrap())
            })
        }

        pub fn last_mut(&self) -> Option<RwLockWriteGuard<Option<Context>>> {
            self.stack.last().and_then(|&id| {
                // Wait until the OS allow this thread to read and write at the context vector
                Some(self.context_vec[id].1.write().unwrap())
            })
        }

        #[allow(unused_variables)]
        pub fn push(
            &mut self,
            pool: &mut TermPool,
            assignment_args: &[(String, Rc<Term>)],
            variable_args: &[SortedVar],
        ) -> Result<(), SubstitutionError> {
            // Returns a random term, this method is never called
            Err(SubstitutionError::NotAVariable(Rc::new(Term::Sort(
                Sort::Bool,
            ))))
        }

        pub fn push_from_id(
            &mut self,
            pool: &mut TermPool,
            assignment_args: &[(String, Rc<Term>)],
            variable_args: &[SortedVar],
            context_id: usize,
        ) -> Result<(), SubstitutionError> {
            let mut ctx_was_built = self.context_vec[context_id].2.lock().unwrap();
            if !*ctx_was_built {
                // Block the RwLock before unlocking the mutex since there is a chance where the
                // other threads (after the mutex being released) try to access the context being
                // built here and it haven't finished yet
                let mut context = self.context_vec[context_id].1.write().unwrap();
                // Make sure the mutex guard is dropped after indicating that the context is build/being built
                // That way other threads can right away skip this function and when the momment to use
                // the context being built here is finished the RwLock you allow then to read the content
                *ctx_was_built = true;
                drop(ctx_was_built);

                // Since some rules (like `refl`) need to apply substitutions until a fixed point, we
                // precompute these substitutions into a separate hash map. This assumes that the assignment
                // arguments are in the correct order.
                let mut substitution = Substitution::empty();
                let mut substitution_until_fixed_point = Substitution::empty();

                // We build the `substitution_until_fixed_point` hash map from the bottom up, by using the
                // substitutions already introduced to transform the result of a new substitution before
                // inserting it into the hash map. So for instance, if the substitutions are `(:= y z)` and
                // `(:= x (f y))`, we insert the first substitution, and then, when introducing the second,
                // we use the current state of the hash map to transform `(f y)` into `(f z)`. The
                // resulting hash map will then contain `(:= y z)` and `(:= x (f z))`
                for (var, value) in assignment_args.iter() {
                    let sort = Term::Sort(pool.sort(value).clone());
                    let var_term = Term::var(var, pool.add(sort));
                    let var_term = pool.add(var_term);
                    substitution.insert(pool, var_term.clone(), value.clone())?;
                    let new_value = substitution_until_fixed_point.apply(pool, value);
                    substitution_until_fixed_point.insert(pool, var_term, new_value)?;
                }

                let mappings = assignment_args
                    .iter()
                    .map(|(var, value)| {
                        let sort = Term::Sort(pool.sort(value).clone());
                        let var_term = (var.clone(), pool.add(sort)).into();
                        (pool.add(var_term), value.clone())
                    })
                    .collect();
                let bindings = variable_args.iter().cloned().collect();

                *context = Some(Context {
                    mappings,
                    bindings,
                    cumulative_substitution: None,
                });
            }
            self.stack.push(context_id);
            Ok(())
        }

        pub fn pop(&mut self) {
            if let Some(id) = self.stack.pop() {
                let thisContext = &self.context_vec[id];
                let mut remainingThreads = thisContext.0.write().unwrap();

                assert!(
                    *remainingThreads > 0,
                    "A thread tried to access a context not allocated for it."
                );
                *remainingThreads -= 1;
                if *remainingThreads == 0 {
                    // Drop this context since the last thread finished using it
                    *thisContext.1.write().unwrap() = None;
                }
            }

            self.num_cumulative_calculated =
                std::cmp::min(self.num_cumulative_calculated, self.stack.len());
        }

        fn catch_up_cumulative(&mut self, pool: &mut TermPool, up_to: usize) {
            for i in self.num_cumulative_calculated..std::cmp::max(up_to + 1, self.len()) {
                // Waits until the OS allows to write at this context
                let mut curr_context = self.context_vec[self.stack[i]].1.write().unwrap();
                let curr_context = curr_context.as_mut().unwrap();

                let simultaneous =
                    super::build_simultaneous_substitution(pool, &curr_context.mappings).map;
                let mut cumulative_substitution = simultaneous.clone();

                if i > 0 {
                    // Waits until OS allows to read this previous context. The code structure
                    // makes sure that this context, when released for reading, will be already
                    // instantiated since there are only 2 cases:
                    //  - This thread was responsible for building this previous context. Then
                    //      this context has been built
                    //  - Another thread was assigned to build this context. Then, it doesn't
                    //      matter if this other thread has already finished this process, the
                    //      current thread will have to wait until the building process finishes
                    if let Some(previous_context) = self
                        .stack
                        .get(i - 1)
                        .and_then(|&id| Some(self.context_vec[id].1.read().unwrap()))
                    {
                        let previous_context = previous_context.as_ref().unwrap();
                        let previous_substitution =
                            previous_context.cumulative_substitution.as_ref().unwrap();

                        for (k, v) in previous_substitution.map.iter() {
                            let value = match simultaneous.get(v) {
                                Some(new_value) => new_value,
                                None => v,
                            };
                            cumulative_substitution.insert(k.clone(), value.clone());
                        }
                    }
                }
                curr_context.cumulative_substitution =
                    Some(Substitution::new(pool, cumulative_substitution).unwrap());
                self.num_cumulative_calculated = i + 1;
            }
        }

        fn get_substitution(
            &mut self,
            pool: &mut TermPool,
            index: usize,
        ) -> RwLockWriteGuard<Option<Context>> {
            assert!(index < self.len());
            self.catch_up_cumulative(pool, index);

            let writable_ctx = self.context_vec[self.stack[index]].1.write().unwrap();
            writable_ctx
        }

        pub fn apply_previous(&mut self, pool: &mut TermPool, term: &Rc<Term>) -> Rc<Term> {
            if self.len() < 2 {
                term.clone()
            } else {
                self.get_substitution(pool, self.len() - 2)
                    .as_mut()
                    .unwrap()
                    .cumulative_substitution
                    .as_mut()
                    .unwrap()
                    .apply(pool, term)
            }
        }

        pub fn apply(&mut self, pool: &mut TermPool, term: &Rc<Term>) -> Rc<Term> {
            if self.is_empty() {
                term.clone()
            } else {
                self.get_substitution(pool, self.len() - 1)
                    .as_mut()
                    .unwrap()
                    .cumulative_substitution
                    .as_mut()
                    .unwrap()
                    .apply(pool, term)
            }
        }
    }
}

fn build_simultaneous_substitution(
    pool: &mut TermPool,
    mappings: &[(Rc<Term>, Rc<Term>)],
) -> Substitution {
    let mut result = Substitution::empty();

    // We build the simultaneous substitution from the bottom up, by using the mappings already
    // introduced to transform the result of a new mapping before inserting it into the
    // substitution. So for instance, if the mappings are `y -> z` and `x -> (f y)`, we insert the
    // first mapping, and then, when introducing the second, we use the current state of the
    // substitution to transform `(f y)` into `(f z)`. The result will then contain `y -> z` and
    // `x -> (f z)`.
    for (var, value) in mappings {
        let new_value = result.apply(pool, value);

        // We can unwrap here safely because, by construction, the sort of `var` is the
        // same as the sort of `new_value`
        result.insert(pool, var.clone(), new_value).unwrap();
    }
    result
}
