use crate::ast::*;
use ahash::AHashSet;

pub struct Context {
    pub mappings: Vec<(Rc<Term>, Rc<Term>)>,
    pub bindings: AHashSet<SortedVar>,
    pub cumulative_substitution: Option<Substitution>,
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

        let mappings = assignment_args
            .iter()
            .map(|(var, value)| {
                let sort = Term::Sort(pool.sort(value).clone());
                let var_term = (var.clone(), pool.add_term(sort)).into();
                (pool.add_term(var_term), value.clone())
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

    pub fn catch_up_cumulative(&mut self, pool: &mut TermPool) -> Result<(), SubstitutionError> {
        for i in self.num_cumulative_calculated..self.stack.len() {
            let simultaneous = build_simultaneous_substitution(pool, &self.stack[i].mappings).map;
            let mut cumulative_substitution = simultaneous.clone();

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
            self.stack[i].cumulative_substitution =
                Some(Substitution::new(pool, cumulative_substitution)?);
            self.num_cumulative_calculated = i + 1;
        }
        Ok(())
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
