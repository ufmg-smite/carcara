use super::{BindingList, Rc, Term, TermPool};
use ahash::{AHashMap, AHashSet};
use thiserror::Error;

#[derive(Debug, PartialEq, Error)]
pub enum SubstitutionError {
    #[error("trying to substitute term '{0}' with a term of different sort: '{1}'")]
    DifferentSorts(Rc<Term>, Rc<Term>),

    #[error("can't rename binding '{0}' with term '{1}'")]
    InvalidBindingRename(String, Rc<Term>),
}

type SubstitutionResult<T> = Result<T, SubstitutionError>;

pub(super) struct Substitution<'a> {
    pool: &'a mut TermPool,
    substitutions: &'a AHashMap<Rc<Term>, Rc<Term>>,
    substitution_image_vars: AHashSet<String>,
    cache: AHashMap<Rc<Term>, Rc<Term>>,
}

impl<'a> Substitution<'a> {
    pub(super) fn new(
        pool: &'a mut TermPool,
        substitutions: &'a AHashMap<Rc<Term>, Rc<Term>>,
    ) -> SubstitutionResult<Self> {
        for (k, v) in substitutions {
            if k.sort() != v.sort() {
                return Err(SubstitutionError::DifferentSorts(k.clone(), v.clone()));
            }
        }

        // In order to implement capture-avoidance, we need to know which variables may be captured
        // after applying the substitution. For example, consider the substitution { x -> y }. If x
        // and y are both variables, when applying the substitution to (forall ((x Int)) (= x y)),
        // we would need to rename y to avoid a capture, because the substitution would rename the
        // bound variable x to y. The resulting term should then be (forall ((y Int)) (= y y')). In
        // order to prepare for that situation, we compute all entries in the substitution where
        // both the orignal term and the reuslting term are variables. We take care to exclude
        // identity entries, i.e., entries like x -> x.
        let substitution_image_vars = substitutions
            .iter()
            .filter_map(|(k, v)| match (k.as_var(), v.as_var()) {
                (Some(k), Some(v)) if k != v => Some(v.to_string()),
                _ => None,
            })
            .collect();
        Ok(Self {
            pool,
            substitutions,
            substitution_image_vars,
            cache: AHashMap::new(),
        })
    }

    pub(super) fn apply(&mut self, term: &Rc<Term>) -> SubstitutionResult<Rc<Term>> {
        macro_rules! apply_to_sequence {
            ($sequence:expr) => {
                $sequence
                    .iter()
                    .map(|a| self.apply(a))
                    .collect::<Result<Vec<_>, _>>()
            };
        }

        if let Some(t) = self.cache.get(term) {
            return Ok(t.clone());
        }
        if let Some(t) = self.substitutions.get(term) {
            return Ok(t.clone());
        }

        let result = match term.as_ref() {
            Term::App(func, args) => {
                let new_args = apply_to_sequence!(args)?;
                let new_func = self.apply(func)?;
                self.pool.add_term(Term::App(new_func, new_args))
            }
            Term::Op(op, args) => {
                let new_args = apply_to_sequence!(args)?;
                self.pool.add_term(Term::Op(*op, new_args))
            }
            Term::Quant(q, b, t) => {
                let capture_avoiding_substitution = self.capture_avoiding_substitution(b);
                if !capture_avoiding_substitution.is_empty() {
                    // If there are variables that would be captured by the substitution, we need
                    // to rename them first. For that, we create a new `Substitution` with the
                    // capture avoiding substitution and apply it to the outer term
                    let mut sub = Substitution::new(self.pool, &capture_avoiding_substitution)?;
                    let new_term = sub.apply(term)?;
                    self.apply(&new_term)?
                } else {
                    let new_bindings = self.rename_quantifier_bindings(b)?;
                    let new_term = self.apply(t)?;
                    self.pool.add_term(Term::Quant(*q, new_bindings, new_term))
                }
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

    fn rename_quantifier_bindings(&mut self, b: &BindingList) -> SubstitutionResult<BindingList> {
        b.iter()
            .map(|binding| {
                // For each variable in the binding list, we see if the substitution will rename it
                // or not
                let binding_term = self.pool.add_term(binding.clone().into());
                if let Some(value) = self.substitutions.get(&binding_term) {
                    if let Some(iden) = value.as_var() {
                        // If we are substituting one of the bound variables with a
                        // different variable of the same sort, we rename it. Note that the sort is
                        // guaranteed to be the same because of the invariants of `Substitution`
                        return Ok((iden.to_string(), binding.1.clone()));
                    }
                    // If we are substituting one of the bound variables with something
                    // else, we can't simply rename it, so we return an error
                    return Err(SubstitutionError::InvalidBindingRename(
                        binding.0.to_string(),
                        value.clone(),
                    ));
                }
                Ok(binding.clone())
            })
            .collect::<Result<Vec<_>, _>>()
            .map(BindingList)
    }

    /// Returns a new substitution that renames all variables in the binding list that may be
    /// captured by this substitution to a new, arbitrary name. The name chosen is the old name
    /// with '@' appended.
    fn capture_avoiding_substitution(&mut self, b: &BindingList) -> AHashMap<Rc<Term>, Rc<Term>> {
        b.iter()
            .filter_map(|(var, sort)| {
                if !self.substitution_image_vars.contains(var) {
                    return None;
                }
                let old = self.pool.add_term((var.clone(), sort.clone()).into());
                let new = self.pool.add_term((var.clone() + "@", sort.clone()).into());
                Some((old.into(), new.into()))
            })
            .collect()
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

        let mut substitutions = AHashMap::new();
        substitutions.insert(x, t);

        let mut pool = state.term_pool;
        let got = pool.apply_substitutions(&original, &substitutions).unwrap();

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
            "(forall ((x Int)) (> x 0))" [x -> y] => "(forall ((y Int)) (> y 0))",

            // Capture-avoidance
            "(forall ((y Int)) (> y x))" [x -> y] => "(forall ((y@ Int)) (> y@ y))",
            "(forall ((x Int) (y Int)) (= x y))" [x -> y] => "(forall ((y Int) (y@ Int)) (= y y@))",
            "(forall ((y Int) (y@ Int)) (= x y y@))" [x -> y] =>
                "(forall ((y@ Int) (y@@ Int)) (= y y@ y@@))",
            "(forall ((x Int) (y Int)) (= x y))" [x -> x] => "(forall ((x Int) (y Int)) (= x y))",

            // In theory, since x does not appear in this term, renaming y to y@ is unnecessary
            "(forall ((y Int)) (> y 0))" [x -> y] => "(forall ((y@ Int)) (> y@ 0))",
        }
    }
}
