use super::{AnchorArg, Rc, Substitution, Term, pool::Pool};

/// A single Alethe subproof context.
#[derive(Debug)]
pub struct Context {
    /// The anchor arguments that defined this context.
    pub args: Vec<AnchorArg>,

    /// The cumulative substitution of this context and all outer contexts.
    ///
    /// This is computed by [`ContextStack`].
    pub cumulative_substitution: Option<Substitution>,
}

impl Context {
    /// Builds a new context form the arguments to an `anchor`. This does not initialize the
    /// `cumulative_substitution` field.
    fn new(args: Vec<AnchorArg>) -> Self {
        Self { args, cumulative_substitution: None }
    }
}

/// Struct that represents a stack of nested contexts, allowing the user to compute and apply the
/// cumulative substitution defined by them.
#[derive(Default, Debug)]
pub struct ContextStack {
    stack: Vec<Context>,
    num_cumulative_calculated: usize,
}

impl ContextStack {
    /// Constructs a new empty context stack.
    pub fn new() -> Self {
        Default::default()
    }

    /// Returns the number of contexts in the stack.
    pub fn len(&self) -> usize {
        self.stack.len()
    }

    /// Returns `true` if the context stack contains no contexts.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Gets a read-only reference to the top context in the stack.
    pub fn last(&self) -> Option<&Context> {
        self.stack.last()
    }

    /// Gets a mutable reference to the top context in the stack.
    pub fn last_mut(&mut self) -> Option<&mut Context> {
        self.stack.last_mut()
    }

    /// Pushes a new context to the stack.
    pub fn push(&mut self, args: &[AnchorArg]) {
        self.stack.push(Context::new(args.to_vec()));
    }

    /// Pops the top context from the stack.
    pub fn pop(&mut self) {
        self.stack.pop();
        self.num_cumulative_calculated =
            std::cmp::min(self.num_cumulative_calculated, self.stack.len());
    }

    /// Computes the cumulative substitution of all contexts up to the given index `up_to`.
    fn catch_up_cumulative(&mut self, pool: &mut Pool, up_to: usize) {
        /// Maximum depth beyond which the substitution construction will not use a cache.
        ///
        /// This may be surprising, but in some pathological benchmarks with very deep subproof
        /// nesting, the upkeep of using a cache causes a significant overhead, outweighing the
        /// benefit that the cache brings. Still, disabling the cache unconditionally would harm
        /// performance in most other benchmarks. So, we use this heursitic to try and detect these
        /// cases---if the total subproof depth of this context is beyond this value, we disable
        /// the cache.
        ///
        /// The exact value was found by extensive benchmarking.
        const UNCACHE_DEPTH_HEURISTIC: usize = 20;

        let max_depth = std::cmp::max(up_to + 1, self.len());
        let uncached = max_depth > UNCACHE_DEPTH_HEURISTIC;

        for i in self.num_cumulative_calculated..max_depth {
            let mut substitution = if i > 0 {
                self.stack[i - 1].cumulative_substitution.clone().unwrap()
            } else {
                Substitution::empty()
            };

            for a in &self.stack[i].args {
                match a {
                    AnchorArg::Variable((name, sort)) => {
                        let var_term = pool.add(Term::new_var(name, sort.clone()));
                        substitution.remove(&var_term);
                    }
                    AnchorArg::Assign(var, value) => {
                        let var_term = pool.add(var.clone().into());

                        let new_value = if uncached {
                            substitution.apply_uncached(pool, value)
                        } else {
                            substitution.apply(pool, value)
                        };
                        // It is safe to unwrap here because we ensure by construction that
                        // `var_term` is a variable term, with he same sort as `value`
                        substitution
                            .insert(pool, var_term, new_value.clone())
                            .unwrap();
                    }
                }
            }

            self.stack[i].cumulative_substitution = Some(substitution);
            self.num_cumulative_calculated = i + 1;
        }
    }

    /// Apply the immediately previous context to a term.
    ///
    /// This applies the cumulative substitution of all contexts in the stack, except for the top one.
    pub fn apply_previous(&mut self, pool: &mut Pool, term: &Rc<Term>) -> Rc<Term> {
        if self.len() < 2 {
            term.clone()
        } else {
            let index = self.len() - 2;
            self.catch_up_cumulative(pool, index);
            self.stack[index]
                .cumulative_substitution
                .as_mut()
                .unwrap()
                .apply(pool, term)
        }
    }

    /// Apply the current context to a term.
    ///
    /// This applies the cumulative substitution of all contexts in the stack.
    pub fn apply(&mut self, pool: &mut Pool, term: &Rc<Term>) -> Rc<Term> {
        if self.is_empty() {
            term.clone()
        } else {
            let index = self.len() - 1;
            self.catch_up_cumulative(pool, index);
            self.stack[index]
                .cumulative_substitution
                .as_mut()
                .unwrap()
                .apply(pool, term)
        }
    }
}
