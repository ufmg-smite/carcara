use super::{BindingList, Rc, Term, TermPool};
use ahash::{AHashMap, AHashSet};
use thiserror::Error;

#[derive(Debug, PartialEq, Error)]
pub enum SubstitutionError {
    #[error("trying to substitute term '{0}' with a term of different sort: '{1}'")]
    DifferentSorts(Rc<Term>, Rc<Term>),
}

type SubstitutionResult<T> = Result<T, SubstitutionError>;

pub struct Substitution {
    pub(crate) map: AHashMap<Rc<Term>, Rc<Term>>,
    // Variables that should be renamed to preserve capture-avoidance if they are bound by a binder
    // term
    should_be_renamed: AHashSet<String>,
    cache: AHashMap<Rc<Term>, Rc<Term>>,
}

impl Substitution {
    pub fn new(pool: &mut TermPool, map: AHashMap<Rc<Term>, Rc<Term>>) -> SubstitutionResult<Self> {
        for (k, v) in map.iter() {
            if k.sort() != v.sort() {
                return Err(SubstitutionError::DifferentSorts(k.clone(), v.clone()));
            }
        }

        // To avoid captures when applying the substitution, we may need to rename some of the
        // variables that are bound in the term.
        //
        // For example, consider the substitution `{x -> y}`. If `x` and `y` are both variables,
        // when applying the substitution to `(forall ((y Int)) (= x y))`, we would need to rename
        // `y` to avoid a capture, because the substitution would change the semantics of the term.
        // The resulting term should then be `(forall ((y' Int)) (= y y'))`.
        //
        // More precisely, for a substitution `{x -> t}`, if a bound variable `y` satisfies one the
        // following conditions, it must be renamed:
        //
        // * `y` = `x`
        // * `y` appears in the free variables of `t`
        //
        // See https://en.wikipedia.org/wiki/Lambda_calculus#Capture-avoiding_substitutions for
        // more details.
        let mut should_be_renamed = AHashSet::new();
        for (x, t) in map.iter() {
            if x == t {
                continue; // We ignore reflexive substitutions
            }
            should_be_renamed.extend(pool.free_vars(t).iter().cloned());
            if let Some(x) = x.as_var() {
                should_be_renamed.insert(x.to_string());
            }
        }

        Ok(Self {
            map,
            should_be_renamed,
            cache: AHashMap::new(),
        })
    }

    pub fn apply(&mut self, pool: &mut TermPool, term: &Rc<Term>) -> SubstitutionResult<Rc<Term>> {
        macro_rules! apply_to_sequence {
            ($sequence:expr) => {
                $sequence
                    .iter()
                    .map(|a| self.apply(pool, a))
                    .collect::<Result<Vec<_>, _>>()
            };
        }

        if let Some(t) = self.cache.get(term) {
            return Ok(t.clone());
        }
        if let Some(t) = self.map.get(term) {
            return Ok(t.clone());
        }

        let result = match term.as_ref() {
            Term::App(func, args) => {
                let new_args = apply_to_sequence!(args)?;
                let new_func = self.apply(pool, func)?;
                pool.add_term(Term::App(new_func, new_args))
            }
            Term::Op(op, args) => {
                let new_args = apply_to_sequence!(args)?;
                pool.add_term(Term::Op(*op, new_args))
            }
            Term::Quant(q, b, t) => {
                let (new_bindings, renaming) = self.rename_bindings(pool, b);
                let new_term = if !renaming.is_empty() {
                    // If there are variables that would be captured by the substitution, we need
                    // to rename them first. For that, we create a new `Substitution` with the
                    // renaming substitution that was computed, and apply it to the inner term
                    let mut renaming = Substitution::new(pool, renaming)?;
                    let renamed = renaming.apply(pool, t)?;
                    self.apply(pool, &renamed)?
                } else {
                    self.apply(pool, t)?
                };
                pool.add_term(Term::Quant(*q, new_bindings, new_term))
            }
            // TODO: Handle "choice" and "let" terms
            _ => term.clone(),
        };

        // Since frequently a term will have more than one identical subterms, we insert the
        // calculated substitution in the cache hash map so it may be reused later. This means we
        // don't re-visit already seen terms, so this method traverses the term as a DAG, not as a
        // tree
        self.cache.insert(term.clone(), result.clone());
        Ok(result)
    }

    /// Creates a new substitution that renames all variables in the binding list that may be
    /// captured by this substitution to a new, arbitrary name. Returns that substitution, and the
    /// new binding list, with the bindings renamed. If no variable needs to be renamed, this just
    /// returns a clone of the binding list and an empty hash map. The name chosen when renaming a
    /// variable is the old name with '@' appended.
    fn rename_bindings(
        &mut self,
        pool: &mut TermPool,
        b: &BindingList,
    ) -> (BindingList, AHashMap<Rc<Term>, Rc<Term>>) {
        let mut map = AHashMap::new();
        let mut new_vars = AHashSet::new();
        let new_binding_list = b
            .iter()
            .map(|(var, value)| {
                // If this is called with the binding list of a `let` term, `value` will be the
                // value of the variable. Otherwise, it will be its sort
                if self.should_be_renamed.contains(var) {
                    // TODO: currently, there is no mechanism to avoid collisions when renaming the
                    // variables to the arbitrary name
                    let new_var = var.clone() + "@";
                    let old = pool.add_term((var.clone(), value.clone()).into());
                    let new = pool.add_term((new_var.clone(), value.clone()).into());
                    map.insert(old, new);
                    new_vars.insert(new_var.clone());

                    // TODO: apply current substitution to `value`, if this is used in a `let` term
                    (new_var, value.clone())
                } else {
                    (var.clone(), value.clone())
                }
            })
            .collect();
        (BindingList(new_binding_list), map)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::tests::{parse_definitions, parse_term_with_state};

    fn run_test(definitions: &str, original: &str, x: &str, t: &str, result: &str) {
        let mut state = parse_definitions(definitions);
        let original = parse_term_with_state(&mut state, original);
        let x = parse_term_with_state(&mut state, x);
        let t = parse_term_with_state(&mut state, t);
        let result = parse_term_with_state(&mut state, result);

        let mut map = AHashMap::new();
        map.insert(x, t);

        let mut pool = state.term_pool;
        let got = Substitution::new(&mut pool, map)
            .unwrap()
            .apply(&mut pool, &original)
            .unwrap();

        assert_eq!(&result, &got);
    }

    macro_rules! run_tests {
        (
            definitions = $defs:literal,
            $($original:literal [$x:tt -> $t:tt] => $result:literal,)*
        ) => {{
            let definitions = $defs;
            $(run_test(definitions, $original, stringify!($x), stringify!($t), $result);)*
        }};
    }

    #[test]
    fn test_substitutions() {
        run_tests! {
            definitions = "
                (declare-fun x () Int)
                (declare-fun y () Int)
                (declare-fun p () Bool)
                (declare-fun q () Bool)
                (declare-fun r () Bool)
            ",
            "x" [x -> x] => "x",
            "(+ 2 x)" [x -> y] => "(+ 2 y)",
            "(+ 2 x)" [x -> (+ 3 4 5)] => "(+ 2 (+ 3 4 5))",
            "(forall ((p Bool)) (and p q))" [q -> r] => "(forall ((p Bool)) (and p r))",

            // Simple renaming
            "(forall ((x Int)) (> x 0))" [x -> y] => "(forall ((x@ Int)) (> x@ 0))",

            // Capture-avoidance
            "(forall ((y Int)) (> y x))" [x -> y] => "(forall ((y@ Int)) (> y@ y))",
            "(forall ((x Int) (y Int)) (= x y))" [x -> y] =>
                "(forall ((x@ Int) (y@ Int)) (= x@ y@))",
            "(forall ((x Int) (y Int)) (= x y))" [x -> x] => "(forall ((x Int) (y Int)) (= x y))",
            "(forall ((y Int)) (> y x))" [x -> (+ y 0)] => "(forall ((y@ Int)) (> y@ (+ y 0)))",

            // In theory, since x does not appear in this term, renaming y to y@ is unnecessary
            "(forall ((y Int)) (> y 0))" [x -> y] => "(forall ((y@ Int)) (> y@ 0))",
        }
    }
}
