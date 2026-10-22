//! Custom operators, defined in `custom_operators.toml` and loaded at compile time.

use super::{Rc, Sort, pool::Pool};

/// A sort in the type signature of a custom operator.
#[derive(Debug)]
pub enum SortSig {
    Var(usize),
    Bool,
    Int,
    Real,
    String,
    RegLan,
    Array(&'static SortSig, &'static SortSig),
    Set(&'static SortSig),
    Tuple(&'static [SortSig]),
}

impl SortSig {
    /// Matches `sort` against this signature, binding the sort parameters in `params` as needed.
    pub fn match_with(&self, params: &mut [Option<Rc<Sort>>], sort: &Rc<Sort>) -> bool {
        match (self, sort.as_ref()) {
            (SortSig::Var(i), _) => match &params[*i] {
                Some(existing) => existing.is_compatible(sort),
                None => {
                    params[*i] = Some(sort.clone());
                    true
                }
            },
            (SortSig::Bool, Sort::Bool)
            | (SortSig::Int, Sort::Int)
            | (SortSig::Real, Sort::Real)
            | (SortSig::String, Sort::String)
            | (SortSig::RegLan, Sort::RegLan) => true,
            (SortSig::Array(a_sig, b_sig), Sort::Array(a, b)) => {
                a_sig.match_with(params, a) && b_sig.match_with(params, b)
            }
            (SortSig::Set(sig), Sort::Set(sort)) => sig.match_with(params, sort),
            (SortSig::Tuple(sigs), Sort::Tuple(sorts)) if sigs.len() != sorts.len() => false,
            (SortSig::Tuple(sigs), Sort::Tuple(sorts)) => sigs
                .iter()
                .zip(sorts)
                .all(|(sig, sort)| sig.match_with(params, sort)),
            (_, Sort::Var(_)) => true,
            (_, _) => false,
        }
    }

    /// Builds the sort described by this signature, replacing each sort parameter by the sort it
    /// was bound to. Unbound parameters become sort variables named after the parameter.
    pub fn instantiate(
        &self,
        pool: &mut Pool,
        params: &[Option<Rc<Sort>>],
        names: &[&str],
    ) -> Rc<Sort> {
        match self {
            SortSig::Var(i) => match &params[*i] {
                Some(s) => s.clone(),
                None => pool.add_sort(Sort::Var(names[*i].to_owned())),
            },
            SortSig::Bool => pool.add_sort(Sort::Bool),
            SortSig::Int => pool.add_sort(Sort::Int),
            SortSig::Real => pool.add_sort(Sort::Real),
            SortSig::String => pool.add_sort(Sort::String),
            SortSig::RegLan => pool.add_sort(Sort::RegLan),
            SortSig::Array(a, b) => {
                let a = a.instantiate(pool, params, names);
                let b = b.instantiate(pool, params, names);
                pool.add_sort(Sort::Array(a, b))
            }
            SortSig::Set(sort) => {
                let sort = sort.instantiate(pool, params, names);
                pool.add_sort(Sort::Set(sort))
            }
            SortSig::Tuple(sorts) => {
                let sorts = sorts
                    .iter()
                    .map(|s| s.instantiate(pool, params, names))
                    .collect();
                pool.add_sort(Sort::Tuple(sorts))
            }
        }
    }
}

/// The type signature of a custom operator.
#[derive(Debug)]
pub struct OperatorSig {
    pub name: &'static str,
    pub params: &'static [&'static str],
    pub arg_sorts: &'static [SortSig],
    pub return_sort: SortSig,
}

impl OperatorSig {
    /// Computes the sort of an application of this operator to arguments with sorts `arg_sorts`.
    pub fn compute_sort(&self, pool: &mut Pool, arg_sorts: &[Rc<Sort>]) -> Rc<Sort> {
        let mut params = vec![None; self.params.len()];
        for (sig, sort) in self.arg_sorts.iter().zip(arg_sorts) {
            sig.match_with(&mut params, sort);
        }
        self.return_sort.instantiate(pool, &params, self.params)
    }
}

carcara_macros::custom_operators!("custom_operators.toml");

/// Looks up an operator by name, checking built-in operators first, then custom ones.
pub fn lookup_operator(name: &str) -> Option<super::Operator> {
    use std::str::FromStr;
    if let Ok(op) = super::Operator::from_str(name) {
        return Some(op);
    }
    CustomOperator::lookup(name).map(super::Operator::Custom)
}

#[cfg(test)]
mod tests {
    use super::{CustomOperator, OperatorSig, Pool, SortSig};
    use crate::ast::{Operator, Rc, Sort};
    use std::str::FromStr;

    /// The signature of `store`: `(Array X Y) X Y -> (Array X Y)`.
    static STORE: OperatorSig = OperatorSig {
        name: "store",
        params: &["X", "Y"],
        arg_sorts: &[
            SortSig::Array(&SortSig::Var(0), &SortSig::Var(1)),
            SortSig::Var(0),
            SortSig::Var(1),
        ],
        return_sort: SortSig::Array(&SortSig::Var(0), &SortSig::Var(1)),
    };

    /// Matches every argument sort against the signature, failing on the first mismatch.
    fn matches(sig: &OperatorSig, sorts: &[Rc<Sort>]) -> bool {
        let mut params = vec![None; sig.params.len()];
        sig.arg_sorts
            .iter()
            .zip(sorts)
            .all(|(arg_sig, sort)| arg_sig.match_with(&mut params, sort))
    }

    #[test]
    fn custom_operator_names_do_not_shadow_built_ins() {
        for op in CustomOperator::ALL {
            assert!(Operator::from_str(op.sig().name).is_err());
        }
    }

    #[test]
    fn match_concrete_sorts() {
        let mut pool = Pool::new();
        let [int, string] = [Sort::Int, Sort::String].map(|s| pool.add_sort(s));
        let array = pool.add_sort(Sort::Array(int.clone(), string.clone()));

        let args = [array.clone(), int.clone(), string.clone()];
        assert!(matches(&STORE, &args));
        assert_eq!(STORE.compute_sort(&mut pool, &args), array);

        // `X` is bound to `Int` by the first argument
        assert!(!matches(
            &STORE,
            &[array.clone(), string.clone(), string.clone()]
        ));
        assert!(!matches(&STORE, &[int.clone(), int, string]));
    }

    #[test]
    fn match_sort_variables() {
        let mut pool = Pool::new();
        let [t0, t1, t2, t3] =
            ["@T0", "@T1", "@T2", "@T3"].map(|v| pool.add_sort(Sort::Var(v.into())));
        let array = pool.add_sort(Sort::Array(t0.clone(), t1));

        // Like in RARE rules, each variable has its own sort variable
        let args = [array.clone(), t2, t3];
        assert!(matches(&STORE, &args));
        assert_eq!(STORE.compute_sort(&mut pool, &args), array);

        // Sort variables match signatures that don't use sort parameters
        assert!(SortSig::Int.match_with(&mut [], &t0));
        assert!(SortSig::Set(&SortSig::Int).match_with(&mut [], &t0));
    }

    #[test]
    fn compute_sort_ignores_mismatches() {
        let mut pool = Pool::new();
        let [int, string] = [Sort::Int, Sort::String].map(|s| pool.add_sort(s));
        let array = pool.add_sort(Sort::Array(int, string.clone()));

        let args = [array.clone(), string.clone(), string];
        assert_eq!(STORE.compute_sort(&mut pool, &args), array);
    }

    #[test]
    fn instantiate_unbound_params() {
        let mut pool = Pool::new();
        let x = pool.add_sort(Sort::Var("X".into()));
        let expected = pool.add_sort(Sort::Set(x));

        let got = SortSig::Set(&SortSig::Var(0)).instantiate(&mut pool, &[None], &["X"]);
        assert_eq!(got, expected);
    }
}
