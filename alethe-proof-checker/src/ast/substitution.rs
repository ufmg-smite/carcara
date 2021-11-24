use super::{BindingList, Identifier, Rc, Term, TermPool, Terminal};
use ahash::AHashMap;
use thiserror::Error;

#[derive(Debug, PartialEq, Error)]
pub enum SubstitutionError {
    #[error("can't rename binding '{0}' with term '{1}'")]
    InvalidBindingRename(String, Rc<Term>),
}

type SubstitutionResult<T> = Result<T, SubstitutionError>;

pub(super) struct Substitution<'a> {
    pool: &'a mut TermPool,
    substitutions: &'a AHashMap<Rc<Term>, Rc<Term>>,
    cache: AHashMap<Rc<Term>, Rc<Term>>,
}

impl<'a> Substitution<'a> {
    pub(super) fn new(
        pool: &'a mut TermPool,
        substitutions: &'a AHashMap<Rc<Term>, Rc<Term>>,
    ) -> Self {
        Self {
            pool,
            substitutions,
            cache: AHashMap::new(),
        }
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
                let new_bindings = self.rename_quantifier_bindings(b)?;
                let new_term = self.apply(t)?;
                self.pool.add_term(Term::Quant(*q, new_bindings, new_term))
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
            .map(|var| {
                // For each variable in the binding list, we see if the substitution will rename it
                // or not
                let var_term = self.pool.add_term(var.clone().into());
                if let Some(value) = self.substitutions.get(&var_term) {
                    if let Term::Terminal(Terminal::Var(Identifier::Simple(iden), sort)) =
                        value.as_ref()
                    {
                        if sort == &var.1 {
                            // If we are substituting one of the bound variables with a
                            // different variable of the same sort, we rename it
                            return Ok((iden.clone(), sort.clone()));
                        }
                    }
                    // If we are substituting one of the bound variables with something
                    // else, we can't simply rename it, so we return an error
                    return Err(SubstitutionError::InvalidBindingRename(
                        var.0.to_string(),
                        value.clone(),
                    ));
                }
                Ok(var.clone())
            })
            .collect::<Result<Vec<_>, _>>()
            .map(BindingList)
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
            "(+ 2 x)" [x -> y] => "(+ 2 y)",
            "(+ 2 x)" [x -> (+ 3 4 5)] => "(+ 2 (+ 3 4 5))",
            "(forall ((p Bool)) (and p q))" [q -> r] => "(forall ((p Bool)) (and p r))",
        }
    }
}
