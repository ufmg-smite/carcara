//! Algorithms for creating and applying capture-avoiding substitutions over terms.

use super::{BindingList, MatchCase, MatchPattern, Rc, Sort, Term, pool::Pool};
use crate::utils::{HashMapStack, MultiSet};
use rapidhash::{HashMapExt, HashSetExt, RapidHashMap, RapidHashSet};
use thiserror::Error;

/// The error type for errors when constructing or applying substitutions.
#[derive(Debug, PartialEq, Eq, Error)]
pub enum SubstitutionError {
    /// One of the mappings in the substitution was mapping a term to a term of a different sort.
    #[error("trying to substitute term '{0}' with a term of a different sort: '{1}'")]
    DifferentSorts(Rc<Term>, Rc<Term>),
}

type SubstitutionResult<T> = Result<T, SubstitutionError>;

/// Represents a capture-avoiding substitution over terms.
///
/// A substitution is a mapping from variables to terms, that, when applied to a term, will replace
/// all instances of these variables to the terms that they map to. For example, applying the
/// substitution `{x -> (+ y 3)}` to the term `(and (> x 0) (= x z))` would result in the term
/// `(and (> (+ y 3) 0) (= (+ y 3) z))`.
///
/// Note that naively applying a substitution to a term that contains binders may result in what's
/// called a capture: when a variable that was supposed to be free is captured as the result of
/// applying the substitution to the binder term. Consider applying the substitution `{x -> y}` to
/// the term `(forall ((y Int)) (= x y))`. Doing so naively would result in the term
/// `(forall ((y Int)) (= y y))`, which has a different meaning than the original term, because the
/// `x` variable was captured by the binder when it was renamed. To prevent this, these
/// substitutions are also capture-avoiding. This is done by renaming the binder variable when
/// necessary before applying the substitution. In the earlier example, the resulting term would
/// actually be `(forall ((y' Int)) (= y y'))`.
#[derive(Debug, Clone)]
pub struct Substitution {
    /// The substitution's mappings.
    map: RapidHashMap<Rc<Term>, Rc<Term>>,

    /// Whether the substitution should be applied in a capture-avoiding way or not. By default this
    /// will be true but can be set to false.
    avoid_capture: bool,

    /// The variables that should be renamed to preserve capture-avoidance, if they are bound by a
    /// binder term.
    should_be_renamed: Option<RapidHashSet<String>>,

    /// Variables that are part of the substitution, but have been shadowed by a binder.
    ///
    /// For example, when applying `{x -> t}` to `(forall x . B)`, the bound variable `x` shadows
    /// the substitution, so we don't actually apply the substitution to `B`.
    ///
    /// This is a `MultiSet` to correctly deal with nested binders with the same variables, which we
    /// represent with multiple occurrences in the multiset. This field is only used when applying a
    /// substitution, so it should be empty otherwise.
    renaming_shadow: MultiSet<String>,

    cache: HashMapStack<Rc<Term>, Rc<Term>>,
}

impl Substitution {
    /// Constructs an empty substitution.
    pub fn empty() -> Self {
        Self {
            map: RapidHashMap::new(),
            avoid_capture: true,
            should_be_renamed: None,
            renaming_shadow: MultiSet::new(),
            cache: HashMapStack::new(),
        }
    }

    /// Constructs a singleton substitution mapping `x` to `t`. This returns an error if the sorts
    /// of the given terms are not the same.
    pub fn single(pool: &mut Pool, x: Rc<Term>, t: Rc<Term>) -> SubstitutionResult<Self> {
        let mut this = Self::empty();
        this.insert(pool, x, t)?;
        Ok(this)
    }

    /// Constructs a new substitution from an arbitrary mapping of terms to other terms. This
    /// returns an error if any term is mapped to a term of a different sort.
    pub fn new(pool: &mut Pool, map: RapidHashMap<Rc<Term>, Rc<Term>>) -> SubstitutionResult<Self> {
        for (k, v) in &map {
            if !pool.sort(k).is_compatible(&pool.sort(v)) {
                return Err(SubstitutionError::DifferentSorts(k.clone(), v.clone()));
            }
        }

        Ok(Self {
            map,
            avoid_capture: true,
            should_be_renamed: None,
            renaming_shadow: MultiSet::new(),
            cache: HashMapStack::new(),
        })
    }

    /// Returns `true` if the substitution is empty.
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Returns `true` if all the mappings in the substitution have been shadowed by a binder.
    fn is_fully_shadowed(&self) -> bool {
        self.map
            .keys()
            .all(|k| k.as_var().is_some_and(|k| self.renaming_shadow.contains(k)))
    }

    /// Returns `true` if the term is a shadowed variable.
    fn is_shadowed(&self, term: &Rc<Term>) -> bool {
        term.as_var()
            .is_some_and(|v| self.renaming_shadow.contains(v))
    }

    /// Extends the substitution by adding a new mapping from `x` to `t`. This returns an error if
    /// the sorts of the given terms are not the same.
    pub(crate) fn insert(
        &mut self,
        pool: &mut Pool,
        x: Rc<Term>,
        t: Rc<Term>,
    ) -> SubstitutionResult<()> {
        if !pool.sort(&x).is_compatible(&pool.sort(&t)) {
            return Err(SubstitutionError::DifferentSorts(x, t));
        }

        // Introducing new mappings may invalidate previously defined cache entries. In particular,
        // if a term contains `x` as a free variable, the result of applying the substitution to
        // it may be different after adding the `x -> t` mapping, so we remove these cache entries.
        // Additionally, any term that is itself a free variable of `t` should also be removed,
        // since it might need to be renamed.
        let t_free_vars = pool.free_vars(&t).clone();
        self.cache
            .retain_top(|k, _| !pool.free_vars(k).contains(&x) && !t_free_vars.contains(k));

        // Inserting may change which variables should be renamed in a complicated way, so we just
        // drop the computed `should_be_renamed` entirely.
        //
        // A previous version of this code simply added the free variables of `t` to
        // `should_be_renamed`, but that was not accurate since we need to exclude shadowed mappings
        // from `should_be_renamed`, and `x` might be shadowed by a later insertion.
        //
        // In the future, it might be worthwhile to try a more sophisticated approach to avoid
        // recomputing this, but for now we go with the obviously safe solution, which is to just
        // drop it and recompute when needed. Some initial benchmarking showed no big performance
        // regressions.
        self.should_be_renamed = None;

        self.map.insert(x, t);
        Ok(())
    }

    /// Removes a mapping from the substitution.
    ///
    /// This will clear the internal cache and `self.should_be_renamed`, such that it might need to
    /// be recomputed later. Therefore, you should avoid using this method if possible.
    pub(super) fn remove(&mut self, x: &Rc<Term>) {
        let was_present = self.map.remove(x).is_some();
        if was_present {
            self.should_be_renamed = None;
            self.cache.clear();
        }
    }

    /// Sets whether the substitution is applied in a capture-avoiding way.
    pub fn set_capture_avoidance(&mut self, avoid_capture: bool) {
        self.avoid_capture = avoid_capture;
    }

    /// Computes which binder variables will need to be renamed, and stores the result in
    /// `self.should_be_renamed`.
    fn compute_should_be_renamed(&mut self, pool: &mut Pool) {
        if self.should_be_renamed.is_some() {
            return;
        }

        // To avoid captures when applying the substitution, we may need to rename some of the
        // variables that are bound in the term.
        //
        // For example, consider the substitution `{x -> y}`. If `x` and `y` are both variables,
        // when applying the substitution to `(forall ((y Int)) (= x y))`, we would need to rename
        // `y` to avoid a capture, because the substitution would change the semantics of the term.
        // The resulting term should then be `(forall ((y' Int)) (= y y'))`.
        //
        // More precisely, for a substitution `{x -> t}`, if a bound variable `y` appears as free
        // variable in `t`, it must be renamed:
        //
        // See https://en.wikipedia.org/wiki/Lambda_calculus#Capture-avoiding_substitutions for
        // more details.
        let mut should_be_renamed = RapidHashSet::new();
        for (x, t) in &self.map {
            // If this variable is shadowed, we treat it like it's not in `map`
            if self.is_shadowed(x) {
                continue;
            }
            if x == t {
                continue; // We ignore reflexive substitutions
            }
            let free_vars = pool.free_vars(t);
            let free_vars = free_vars.iter().map(|v| v.as_var().unwrap().to_owned());
            should_be_renamed.extend(free_vars);
        }
        self.should_be_renamed = Some(should_be_renamed);
    }

    /// Applies the substitution to `term`, and returns the result as a new term.
    pub fn apply(&mut self, pool: &mut Pool, term: &Rc<Term>) -> Rc<Term> {
        self.renaming_shadow = MultiSet::new();
        let result = self.apply_impl(pool, term, true);
        assert!(self.renaming_shadow.is_empty());
        result
    }

    /// Applies the substitution to `term`, and returns the result as a new term, without using
    /// a cache.
    ///
    /// In some cases, like when constructing a substitution from anchor arguments, the overhead of
    /// maintaining a cache can be bigger than the benefit of using it, in which case this function
    /// is used. In most cases, however, using a cache improves performance, so avoid using this
    /// function unless you know what you are doing.
    pub fn apply_uncached(&mut self, pool: &mut Pool, term: &Rc<Term>) -> Rc<Term> {
        self.renaming_shadow = MultiSet::new();
        let result = self.apply_impl(pool, term, false);
        assert!(self.renaming_shadow.is_empty());
        result
    }

    fn apply_impl(&mut self, pool: &mut Pool, term: &Rc<Term>, use_cache: bool) -> Rc<Term> {
        macro_rules! apply_to_sequence {
            ($sequence:expr) => {
                $sequence
                    .iter()
                    .map(|a| self.apply_impl(pool, a, use_cache))
                    .collect::<Vec<_>>()
            };
        }

        // Note that we only look at the top most scope in the cache, because entering a binder may
        // invalidate any cache entry from outside the binder.
        if let Some(t) = self.cache.get_top(term) {
            return t.clone();
        }
        if let Some(t) = self.map.get(term) {
            // If this variable is shadowed, we treat it like it's not in `map`
            if !self.is_shadowed(term) {
                return t.clone();
            }
        }

        let result = match term.as_ref() {
            Term::App(func, args) => {
                let new_args = apply_to_sequence!(args);
                let new_func = self.apply_impl(pool, func, use_cache);
                pool.add(Term::App(new_func, new_args))
            }
            Term::Op(op, args) => {
                let new_args = apply_to_sequence!(args);
                pool.add(Term::Op(*op, new_args))
            }
            Term::Binder(binder, binding_list, inner) => {
                match self.apply_to_binder(pool, binding_list, inner, use_cache) {
                    Some((new_binds, new_inner)) => {
                        pool.add(Term::Binder(*binder, new_binds, new_inner))
                    }
                    None => term.clone(),
                }
            }
            Term::Let(binding_list, inner) => {
                match self.apply_to_binder(pool, binding_list, inner, use_cache) {
                    Some((new_binds, new_inner)) => pool.add(Term::Let(new_binds, new_inner)),
                    None => term.clone(),
                }
            }
            Term::Match(term, cases) => {
                let new_term = self.apply_impl(pool, term, use_cache);
                let new_cases = cases
                    .iter()
                    .map(|case| {
                        let (new_bindings, mut renaming) =
                            self.rename_binding_list(pool, case.bindings());
                        let pattern = if renaming.is_empty() {
                            case.pattern.clone()
                        } else {
                            // To apply the renaming to the pattern, we just use the renamed
                            // bindings returned by `rename_binding_list`
                            match &case.pattern {
                                MatchPattern::Wildcard => MatchPattern::Wildcard,
                                MatchPattern::Variable(_) => {
                                    MatchPattern::Variable(new_bindings.last().unwrap().clone())
                                }
                                MatchPattern::Cons(cons, _) => {
                                    MatchPattern::Cons(cons.clone(), new_bindings.0)
                                }
                            }
                        };

                        let body = if renaming.is_empty() {
                            self.apply_impl(pool, &case.body, use_cache)
                        } else {
                            let renamed = renaming.apply(pool, &case.body);
                            self.apply_impl(pool, &renamed, use_cache)
                        };
                        MatchCase { pattern, body }
                    })
                    .collect();
                pool.add(Term::Match(new_term, new_cases))
            }
            Term::Const(_) | Term::Var(..) => term.clone(),
            Term::ParamOp { op, op_args, args } => {
                // TODO: maybe we should also apply to op_args?
                let new_args = apply_to_sequence!(args);
                pool.add(Term::ParamOp {
                    op: *op,
                    op_args: op_args.clone(),
                    args: new_args,
                })
            }
            Term::AsOp(op, sort, args) => {
                let new_args = apply_to_sequence!(args);
                pool.add(Term::AsOp(*op, sort.clone(), new_args))
            }
        };

        // Since frequently a term will have more than one identical subterms, we insert the
        // calculated substitution in the cache hash map so it may be reused later. This means we
        // don't re-visit already seen terms, so this method traverses the term as a DAG, not as a
        // tree.
        //
        // However, in some cases (like constructing a context substitution), the cost of
        // maintaining a cache can cause more overhead than it saves. For this reason, we allow the
        // user to disable cache use for a specific call to `apply`.
        if use_cache {
            self.cache.insert(term.clone(), result.clone());
        }
        result
    }

    /// Applies the substitution to a binder term, renaming any bound variables as needed.
    ///
    /// If this returns `None`, the substitution can be skipped, and the original term should be
    /// used.
    fn apply_to_binder<T: BindingValue>(
        &mut self,
        pool: &mut Pool,
        binding_list: &BindingList<T>,
        inner: &Rc<Term>,
        use_cache: bool,
    ) -> Option<(BindingList<T>, Rc<Term>)> {
        if self.avoid_capture {
            self.compute_should_be_renamed(pool);
        }

        // All variables in the binding list are now shadowed, disabling their corresponding
        // substitution mappings
        for (var, _) in binding_list {
            self.renaming_shadow.insert(var.clone());
        }

        // Entering a binder invalidates all cache entries from before, so we push a new scope
        self.cache.push_scope();

        // If all mappings in the substitution have become shadowed, we can skip applying the
        // substitution to this term altogether
        if self.is_fully_shadowed() {
            for (var, _) in binding_list {
                self.renaming_shadow.remove(var);
            }
            self.cache.pop_scope();
            return None;
        }

        let (new_bindings, mut renaming) = self.rename_binding_list(pool, binding_list);
        let new_term = if renaming.is_empty() {
            self.apply_impl(pool, inner, use_cache)
        } else {
            // If there are variables that would be captured by the substitution, we need
            // to rename them first
            let renamed = renaming.apply(pool, inner);
            self.apply_impl(pool, &renamed, use_cache)
        };

        // We must remember to unshadow the binding list variables, and pop the cache scope
        for (var, _) in binding_list {
            self.renaming_shadow.remove(var);
        }
        self.cache.pop_scope();

        Some((new_bindings, new_term))
    }

    /// Creates a new substitution that renames all variables in the binding list that may be
    /// captured by this substitution to a new, arbitrary name. Returns that substitution, and the
    /// new binding list, with the bindings renamed. If no variable needs to be renamed, this just
    /// returns a clone of the binding list and an empty substitution. The name chosen when renaming
    /// a variable is the old name with `_renamed` appended.
    fn rename_binding_list<V: BindingValue>(
        &mut self,
        pool: &mut Pool,
        binding_list: &[(String, V)],
    ) -> (BindingList<V>, Self) {
        if !self.avoid_capture {
            return (BindingList(binding_list.to_vec()), Self::empty());
        }
        let mut new_substitution = Self::empty();
        let mut new_vars = RapidHashSet::new();
        let new_binding_list = binding_list
            .iter()
            .map(|(var, value)| {
                let sort = value.get_sort(pool);

                let mut changed = false;
                let mut new_var = var.clone();

                // We keep adding `_renamed`s to the variable name as long as it is necessary
                loop {
                    if !new_vars.contains(&new_var)
                        && !self.should_be_renamed.as_ref().unwrap().contains(&new_var)
                    {
                        break;
                    }
                    new_var.push_str("_renamed");
                    changed = true;
                }

                if changed {
                    // If the variable was renamed, we have to add this renaming to the resulting
                    // substitution
                    let old = pool.add((var.clone(), sort.clone()).into());
                    let new = pool.add((new_var.clone(), sort).into());

                    // We can safely unwrap here because `old` and `new` are guaranteed to have the
                    // same sort
                    new_substitution.insert(pool, old, new).unwrap();
                    new_vars.insert(new_var.clone());
                }

                // We also need to apply the current substitution to each variable's value
                let new_value = value.apply_subst(pool, &mut new_substitution);
                (new_var, new_value)
            })
            .collect();
        (BindingList(new_binding_list), new_substitution)
    }
}

/// A trait for objects that can be the value in a binding list, namely `Rc<Term>` or `Rc<Sort>`.
trait BindingValue: Clone {
    fn get_sort(&self, pool: &mut Pool) -> Rc<Sort>;

    fn apply_subst(&self, pool: &mut Pool, substitution: &mut Substitution) -> Self;
}

impl BindingValue for Rc<Term> {
    fn get_sort(&self, pool: &mut Pool) -> Rc<Sort> {
        pool.sort(self)
    }

    fn apply_subst(&self, pool: &mut Pool, substitution: &mut Substitution) -> Self {
        substitution.apply(pool, self)
    }
}

impl BindingValue for Rc<Sort> {
    fn get_sort(&self, _: &mut Pool) -> Rc<Sort> {
        self.clone()
    }

    fn apply_subst(&self, _: &mut Pool, _: &mut Substitution) -> Self {
        self.clone()
    }
}

/// Represents a non-capture-avoiding substitution over sorts.
#[derive(Debug, Clone)]
pub struct SortSubstitution {
    /// The substitution's mappings.
    map: RapidHashMap<String, Rc<Sort>>,
    cache: RapidHashMap<Rc<Sort>, Rc<Sort>>,
}

impl SortSubstitution {
    /// Constructs a new substitution from an arbitrary mapping of sort variables to other sorts.
    pub fn new(map: RapidHashMap<String, Rc<Sort>>) -> Self {
        Self { map, cache: RapidHashMap::new() }
    }

    /// Applies the substitution to `sort`, and returns the result as a new sort.
    pub fn apply(&mut self, pool: &mut Pool, sort: &Rc<Sort>) -> Rc<Sort> {
        macro_rules! apply_to_sequence {
            ($sequence:expr) => {
                $sequence
                    .iter()
                    .map(|a| self.apply(pool, a))
                    .collect::<Vec<_>>()
            };
        }

        if let Some(t) = self.cache.get(sort) {
            return t.clone();
        }

        let result = match sort.as_ref() {
            Sort::Var(var) if self.map.contains_key(var) => return self.map[var].clone(),
            Sort::Atom(sort, args) => {
                let new_args = apply_to_sequence!(args).into_boxed_slice();
                pool.add_sort(Sort::Atom(sort.clone(), new_args))
            }
            Sort::Function(args) => {
                let new_args = apply_to_sequence!(args);
                pool.add_sort(Sort::Function(new_args))
            }
            Sort::Array(x, y) => {
                let [x, y] = [x, y].map(|s| self.apply(pool, s));
                pool.add_sort(Sort::Array(x, y))
            }
            Sort::Datatype { name, args } => {
                let new_args = apply_to_sequence!(args);
                pool.add_sort(Sort::Datatype { name: name.clone(), args: new_args })
            }
            Sort::Par(vars, sort) => {
                let new_sort = self.apply(pool, sort);
                let new_vars: Vec<_> = vars
                    .iter()
                    .filter(|v| !self.map.contains_key(*v))
                    .cloned()
                    .collect();
                if new_vars.is_empty() {
                    new_sort
                } else {
                    pool.add_sort(Sort::Par(new_vars, new_sort))
                }
            }
            Sort::Var(_)
            | Sort::Bool
            | Sort::Int
            | Sort::Real
            | Sort::String
            | Sort::RegLan
            | Sort::BitVec(_)
            | Sort::ParamBitVec
            | Sort::Type => sort.clone(),
            Sort::Set(s) => {
                let s = self.apply(pool, s);
                pool.add_sort(Sort::Set(s))
            }
            Sort::Tuple(sorts) => {
                let new_sorts = apply_to_sequence!(sorts);
                pool.add_sort(Sort::Tuple(new_sorts))
            }
        };

        self.cache.insert(sort.clone(), result.clone());
        result
    }
}

#[cfg(test)]
mod tests {
    use super::Substitution;
    use crate::{
        ast::pool::Pool,
        parser::{Config, Parser},
    };
    use rapidhash::{HashMapExt, RapidHashMap};

    fn run_test(definitions: &str, original: &str, x: &str, t: &str, result: &str) {
        let mut pool = Pool::new();
        let mut parser = Parser::new(&mut pool, Config::new(), definitions.into()).unwrap();
        parser.parse_problem().unwrap();

        let [original, x, t, result] = [original, x, t, result].map(|s| {
            parser.reset(s.into()).unwrap();
            parser.parse_term().unwrap()
        });

        let mut map = RapidHashMap::new();
        map.insert(x, t);

        let got = Substitution::new(&mut pool, map)
            .unwrap()
            .apply(&mut pool, &original);

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
            "(forall ((y Int)) (> y 0))" [x -> y] => "(forall ((y_renamed Int)) (> y_renamed 0))",

            // Renaming may be skipped
            "(forall ((x Int)) (> x 0))" [x -> y] => "(forall ((x Int)) (> x 0))",
            "(forall ((x Int) (y Int)) (= x y))" [x -> y] => "(forall ((x Int) (y Int)) (= x y))",

            // Capture-avoidance
            "(forall ((y Int)) (> y x))" [x -> y] => "(forall ((y_renamed Int)) (> y_renamed y))",
            "(forall ((x Int) (y Int)) (= x y))" [x -> x] => "(forall ((x Int) (y Int)) (= x y))",
            "(forall ((y Int)) (> y x))" [x -> (+ y 0)] =>
                "(forall ((y_renamed Int)) (> y_renamed (+ y 0)))",

            "(forall ((y Int) (y_renamed Int)) (= y y_renamed))" [x -> y] =>
                "(forall ((y_renamed Int) (y_renamed_renamed Int)) (= y_renamed y_renamed_renamed))",
            "(forall ((y Int) (y_renamed Int) (y_renamed_renamed Int))
                (= y y_renamed y_renamed_renamed))" [x -> y]
            => "(forall ((y_renamed Int) (y_renamed_renamed Int) (y_renamed_renamed_renamed Int))
                    (= y_renamed y_renamed_renamed y_renamed_renamed_renamed))",

            // The capture-avoidance may disambiguate repeated bindings
            "(forall ((y Int) (y_renamed Int) (y_renamed Int)) (= y y_renamed y_renamed))" [x -> y] =>
                "(forall ((y_renamed Int) (y_renamed_renamed Int) (y_renamed_renamed_renamed Int))
                    (= y_renamed y_renamed_renamed_renamed y_renamed_renamed_renamed))",

            // In theory, since x does not appear in this term, renaming y to y_renamed is unnecessary
            "(forall ((y Int)) (> y 0))" [x -> y] => "(forall ((y_renamed Int)) (> y_renamed 0))",

            // Name collision with variables with different types
            "(forall ((y Bool)) (and y (> x 0)))" [x -> y] =>
                "(forall ((y_renamed Bool)) (and y_renamed (> y 0)))",

            // TODO: Add tests for `choice`, `let`, and `lambda` terms
        }
    }
}
