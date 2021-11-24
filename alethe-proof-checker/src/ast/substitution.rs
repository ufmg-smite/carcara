use super::{Rc, Term, TermPool};
use ahash::AHashMap;
use thiserror::Error;

#[derive(Debug, PartialEq, Error)]
#[error("trying to substitute bound variable '{var}', which is bound in term '{binding_term}'")]
pub struct SubstitutionError {
    pub var: String,
    pub binding_term: Rc<Term>,
}

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

    pub(super) fn apply(&mut self, term: &Rc<Term>) -> Result<Rc<Term>, SubstitutionError> {
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
                for var in b {
                    let var_term = self.pool.add_term(var.clone().into());
                    if self.substitutions.contains_key(&var_term) {
                        return Err(SubstitutionError {
                            var: var.0.clone(),
                            binding_term: term.clone(),
                        });
                    }
                }
                let new_term = self.apply(t)?;
                self.pool.add_term(Term::Quant(*q, b.clone(), new_term))
            }
            _ => term.clone(),
        };

        // Since frequently a term will have more than one identical subterms, we insert the
        // calculated substitution in the cache hash map so it may be reused later. This means we
        // don't re-visit already seen terms, so this method traverses the term as a DAG, not as a
        // tree
        self.cache.insert(term.clone(), result.clone());
        Ok(result)
    }
}
