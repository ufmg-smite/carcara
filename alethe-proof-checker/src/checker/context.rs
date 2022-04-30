use crate::ast::*;
use ahash::AHashSet;

pub struct Context {
    pub substitution: Substitution,
    pub substitution_until_fixed_point: Substitution,
    pub cumulative_substitution: Option<Substitution>,
    pub bindings: AHashSet<SortedVar>,
}

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

    pub fn last(&self) -> Option<&Context> {
        self.stack.last()
    }

    pub fn last_mut(&mut self) -> Option<&mut Context> {
        self.stack.last_mut()
    }

    pub fn get_mut(&mut self, index: usize) -> Option<&mut Context> {
        self.stack.get_mut(index)
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
            let var_term = terminal!(var var; pool.add_term(sort));
            let var_term = pool.add_term(var_term);
            substitution.insert(pool, var_term.clone(), value.clone())?;
            let new_value = substitution_until_fixed_point.apply(pool, value);
            substitution_until_fixed_point.insert(pool, var_term, new_value)?;
        }

        let bindings = variable_args.iter().cloned().collect();
        self.stack.push(Context {
            substitution,
            substitution_until_fixed_point,
            cumulative_substitution: None,
            bindings,
        });
        Ok(())
    }

    pub fn pop(&mut self) {
        self.stack.pop();
        self.num_cumulative_calculated =
            std::cmp::min(self.num_cumulative_calculated, self.stack.len());
    }

    pub fn catch_up_cumulative(&mut self, pool: &mut TermPool) -> Result<(), SubstitutionError> {
        for i in self.num_cumulative_calculated..self.stack.len() {
            let until_fixed_point = &self.stack[i].substitution_until_fixed_point.map;
            let mut cumulative_substitution = until_fixed_point.clone();

            if let Some(previous_context) = self.stack.get(i - 1) {
                let previous_substitution =
                    previous_context.cumulative_substitution.as_ref().unwrap();

                for (k, v) in previous_substitution.map.iter() {
                    let value = match until_fixed_point.get(v) {
                        Some(new_value) => new_value,
                        None => v,
                    };
                    cumulative_substitution.insert(k.clone(), value.clone());
                }
            }
            self.stack[i].cumulative_substitution =
                Some(Substitution::new(pool, cumulative_substitution)?);
            self.num_cumulative_calculated = i + 1;
        }
        Ok(())
    }
}
