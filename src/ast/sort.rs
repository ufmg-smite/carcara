use super::Rc;
use rapidhash::RapidHashMap;
use std::collections::hash_map::Entry;

/// The sort of a term.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Sort {
    /// A function sort.
    ///
    /// The last term indicates the return sort of the function. The remaining terms are the sorts
    /// of the parameters of the function.
    Function(Vec<Rc<Sort>>),

    /// A user-declared sort, from a `declare-sort` command.
    ///
    /// The associated string is the sort name, and the associated terms are the sort arguments for
    /// this sort.
    Atom(Box<str>, Box<[Rc<Sort>]>),

    /// A sort variable
    Var(String),

    /// The `Bool` primitive sort.
    Bool,

    /// The `Int` primitive sort.
    Int,

    /// The `Real` primitive sort.
    Real,

    /// The `String` primitive sort.
    String,

    /// The `RegLan` primitive sort.
    RegLan,

    /// An `Array` sort.
    ///
    /// The two associated terms are the sort arguments for this sort.
    Array(Rc<Sort>, Rc<Sort>),

    /// A `BitVec` sort with a constant width parameter.
    ///
    /// The associated `usize` is the bitvector width of this sort.
    BitVec(usize),

    /// A `BitVec`, parameterized by width parameter that is not statically known.
    ///
    /// The motivation for the existence of this sort is that Rare files can contain bitvector sorts
    /// whose width is parameterized by integer variables. For example:
    /// ```text
    /// (declare-rare-rule bv-extract-whole ((@n0 Int) (x1 (BitVec @n0)) (n1 Int))
    ///   :premises ((= (>= n1 (- (@bvsize x1) 1)) true))
    ///   :args (x1 n1)
    ///   :conclusion (= (extract n1 0 x1) x1)
    /// )
    /// ```
    /// Here, `x1` is a bitvector with width `@n0`, which is not statically known.
    ///
    /// The most precise way of representing this type would be to use a dependent type constructor
    /// that takes a series of variables and produces a parametric sort that uses these variables.
    /// For example, a bitvector term with parametric width `x` would have sort `Π x. BitVec(x)`,
    /// where `Π` is the dependent type constructor.
    ///
    /// Due to operators such as `concat` and `extract`, the term passed to the `BitVec` constructor
    /// can be a more complicated expression than just a simple variable. For example, for
    /// bitvectors `u`, `v` of widths `x`, `y`, `(concat u v)` would have sort `Π x, y. BitVec(x +
    /// y)`, and `(extract i j v)` would have sort `Π i, j. BitVec(i - j + 1)`. As you can imagine,
    /// the nesting of these operators can lead to arbitrarily complex width expressions.
    ///
    /// Type checking these parametric sorts can be difficult. Say we want to ensure the two terms
    /// `(extract i j v)` and `(concat (extract i (+ j 2) v) (extract (+ j 1) j v))` have compatible
    /// sorts. Their parametric widths will be, respectively, `i - j + 1` and `(i - (j + 2) + 1) +
    /// ((j + 1) - j + 1)`. These two expressions are equivalent, but determining that would require
    /// implementing a general simplification procedure for width expressions, which will get even
    /// harder as we consider more operators such as `repeat`.
    ///
    /// Finally, since SMT-LIB and Alethe do not currently include full support for dependent types,
    /// there is no actual use for keeping these parametric width expressions, and for accurately
    /// type checking such dependent types. The upcoming SMT-LIB version 3.0 aims to officially
    /// include dependent types in the language specification, and will determine precisely to
    /// which extent this needs to be supported. Until that is settled, however, we choose a more
    /// pragmatic approach, and don't store the parametric width expressions, instead considering
    /// all parametric bitvector sorts to be compatible.
    ///
    /// Carcara only has support for parametric bitvector sorts to allow correct parsing of Rare
    /// files, and this simplified representation is sufficient in this case, as long as we make
    /// sure to type check the concretely-sorted terms that are created when instantiating the
    /// parametric sorts in the Rare rules.
    // TODO: actually perform this extra type checking
    ParamBitVec,

    /// A datatype sort, specified by its name and the provided sort arguments.
    ///
    /// The actual contents of the datatype (that is, its constructors) are stored in the term pool,
    /// indexed by the datatype name.
    Datatype {
        /// The unique name of this sort.
        name: Box<str>,

        /// The arguments that were provided to this sort (e.g., the `Int` in `(Option Int)`)
        args: Vec<Rc<Sort>>,
    },

    /// A parametric sort, with a set of sort variables that can appear in the second argument.
    Par(Vec<String>, Rc<Sort>),

    /// The sort of sorts.
    Type,

    // Sorts from cvc5's theory extensions
    /// The `Set` sort.
    ///
    /// The `Relation` sort is represented by this sort, applied to a `Tuple` sort.
    Set(Rc<Sort>),

    /// The `Tuple` sort.
    ///
    /// The `UnitTuple` sort is represented by this sort with an empty vector of arguments.
    Tuple(Vec<Rc<Sort>>),
}

impl Sort {
    /// Returns `true` if the sort is a bitvector sort of any width.
    pub fn is_bitvec(&self) -> bool {
        matches!(self, Sort::BitVec(_) | Sort::ParamBitVec)
    }

    /// Returns `true` if the sort is a parametric sort.
    pub fn is_par(&self) -> bool {
        matches!(self, Sort::Par(_, _))
    }

    /// Whether this sort is equal to another, modulo bitvector sorts with width parameters that are
    /// not statically known.
    pub fn param_eq(&self, other: &Self) -> bool {
        self == other
            || *self == Sort::ParamBitVec && other.is_bitvec()
            || *other == Sort::ParamBitVec && self.is_bitvec()
    }

    /// Computes whether this sort is compatible with another.
    ///
    /// That is, this method returns `true` if there exists a substitution to the sort variables of
    /// `self` that will make it equal to `other`.
    pub fn is_compatible(&self, other: &Self) -> bool {
        fn all_compatible(xs: &[Rc<Sort>], ys: &[Rc<Sort>]) -> bool {
            xs.len() == ys.len() && xs.iter().zip(ys).all(|(x, y)| x.is_compatible(y))
        }

        if self.param_eq(other) {
            return true;
        }

        match (self, other) {
            (Sort::Var(_), _) | (_, Sort::Var(_)) => true,
            (Sort::Par(_, a), b) => a.is_compatible(b),
            (a, Sort::Par(_, b)) => a.is_compatible(b),

            (Sort::Atom(a, sorts_a), Sort::Atom(b, sorts_b)) => {
                a == b && all_compatible(sorts_a, sorts_b)
            }
            (Sort::Function(sorts_a), Sort::Function(sorts_b)) => all_compatible(sorts_a, sorts_b),
            (
                Sort::Datatype { name: name_a, args: args_a },
                Sort::Datatype { name: name_b, args: args_b },
            ) => name_a == name_b && all_compatible(args_a, args_b),
            (Sort::Array(x_a, y_a), Sort::Array(x_b, y_b)) => {
                x_a.is_compatible(x_b) && y_a.is_compatible(y_b)
            }
            (Sort::Set(a), Sort::Set(b)) => a.is_compatible(b),
            (Sort::Tuple(sorts_a), Sort::Tuple(sorts_b)) => all_compatible(sorts_a, sorts_b),
            _ => false,
        }
    }

    /// Computes whether this sort can be matched with another, given the set of sort parameters,
    /// and constructs the needed substitution.
    ///
    /// That is, this method returns `true` if we can find a substitution to the sort parameters
    /// that will make `self` equal to `target`. In that case, the `map` argument will store the
    /// constructed substitution.
    pub fn match_with(
        &self,
        params: &[String],
        target: &Rc<Sort>,
        map: &mut RapidHashMap<String, Rc<Sort>>,
    ) -> bool {
        fn all_match(
            xs: &[Rc<Sort>],
            ys: &[Rc<Sort>],
            params: &[String],
            map: &mut RapidHashMap<String, Rc<Sort>>,
        ) -> bool {
            xs.len() == ys.len() && xs.iter().zip(ys).all(|(x, y)| x.match_with(params, y, map))
        }

        if self == target.as_ref() {
            return true;
        }

        if let Sort::Var(a) = self {
            if !params.contains(a) {
                return false;
            }
            match map.entry(a.clone()) {
                Entry::Vacant(e) => e.insert(target.clone()),
                Entry::Occupied(e) => return e.get().param_eq(target),
            };
            return true;
        }

        match (self, target.as_ref()) {
            (Sort::Par(vars, a), _) => {
                // A `par` on the pattern side introduces further bindable variables.
                let mut params = params.to_vec();
                params.extend(vars.iter().cloned());
                a.match_with(&params, target, map)
            }
            (a, Sort::Par(vars, b)) => {
                // A target `par` is only instantiable if all of its bound variables are pattern
                // parameters. Otherwise they are private to the target and could be captured by
                // the substitution.
                if !vars.iter().all(|v| params.contains(v)) {
                    return false;
                }
                a.match_with(params, b, map)
            }
            (Sort::Atom(a, sorts_a), Sort::Atom(b, sorts_b)) => {
                a == b && all_match(sorts_a, sorts_b, params, map)
            }
            (Sort::Function(sorts_a), Sort::Function(sorts_b)) => {
                all_match(sorts_a, sorts_b, params, map)
            }

            // The datatype name and arguments are sufficient to uniquely specify a datatype sort,
            // so we don't need to look at the constructors
            (
                Sort::Datatype { name: name_a, args: args_a, .. },
                Sort::Datatype { name: name_b, args: args_b, .. },
            ) => name_a == name_b && all_match(args_a, args_b, params, map),
            (Sort::Array(x_a, y_a), Sort::Array(x_b, y_b)) => {
                x_a.match_with(params, x_b, map) && y_a.match_with(params, y_b, map)
            }
            (Sort::Set(a), Sort::Set(b)) => a.match_with(params, b, map),
            (Sort::Tuple(sorts_a), Sort::Tuple(sorts_b)) => {
                all_match(sorts_a, sorts_b, params, map)
            }
            _ => self.param_eq(target),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::build_sort;
    use crate::ast::pool::Pool;
    use rapidhash::{HashMapExt, RapidHashMap};

    /// Collects the free sort variables occurring in `sort`
    fn free_vars(sort: &Sort) -> Vec<String> {
        match sort {
            Sort::Var(name) => vec![name.clone()],
            Sort::Atom(_, args) => args.iter().flat_map(|s| free_vars(s)).collect(),
            Sort::Function(args) | Sort::Tuple(args) => {
                args.iter().flat_map(|s| free_vars(s)).collect()
            }
            Sort::Datatype { args, .. } => args.iter().flat_map(|s| free_vars(s)).collect(),
            Sort::Array(x, y) => {
                let mut names = free_vars(x);
                names.extend(free_vars(y));
                names
            }
            Sort::Set(s) => free_vars(s),
            Sort::Par(vars, s) => {
                let mut names = free_vars(s);
                names.retain(|n| !vars.contains(n));
                names
            }
            _ => Vec::new(),
        }
    }

    #[test]
    fn compatible_cases() {
        let mut pool = Pool::new();

        let cases = [
            (build_sort!(pool, Int), build_sort!(pool, Int)),
            (build_sort!(pool, Bool), build_sort!(pool, Bool)),
            (build_sort!(pool, (BitVec 8)), build_sort!(pool, (BitVec 8))),
            (
                build_sort!(pool, ParamBitVec),
                build_sort!(pool, (BitVec 8)),
            ),
            (
                build_sort!(pool, (BitVec 8)),
                build_sort!(pool, ParamBitVec),
            ),
            (build_sort!(pool, a), build_sort!(pool, Int)),
            (build_sort!(pool, a), build_sort!(pool, a)),
            (build_sort!(pool, (par (a) Int)), build_sort!(pool, Int)),
            (
                build_sort!(pool, (Atom "S" Int)),
                build_sort!(pool, (Atom "S" Int)),
            ),
            (
                build_sort!(pool, (-> Int Bool)),
                build_sort!(pool, (-> Int Bool)),
            ),
            (
                build_sort!(pool, (Datatype "D" Int)),
                build_sort!(pool, (Datatype "D" Int)),
            ),
            (
                build_sort!(pool, (Array Int Bool)),
                build_sort!(pool, (Array Int Bool)),
            ),
            (build_sort!(pool, (Set Int)), build_sort!(pool, (Set Int))),
            (
                build_sort!(pool, (Tuple Int Bool)),
                build_sort!(pool, (Tuple Int Bool)),
            ),
            // A sort variable can be bound to make both sides compatible.
            (
                build_sort!(pool, (Atom "S" a)),
                build_sort!(pool, (Atom "S" Int)),
            ),
            (build_sort!(pool, (-> a)), build_sort!(pool, (-> Int))),
        ];

        for (a, b) in cases {
            assert!(a.is_compatible(&b));
            let mut map = RapidHashMap::new();
            assert!(a.match_with(&free_vars(&a), &b, &mut map));
        }
    }

    #[test]
    fn arity_mismatch_is_incompatible() {
        let mut pool = Pool::new();

        let cases = [
            (
                build_sort!(pool, (-> Int)),
                build_sort!(pool, (-> Int Bool)),
            ),
            (
                build_sort!(pool, (Atom "S" Int)),
                build_sort!(pool, (Atom "S" Int Bool)),
            ),
            (
                build_sort!(pool, (Datatype "D" Int)),
                build_sort!(pool, (Datatype "D" Int Bool)),
            ),
            (
                build_sort!(pool, (Tuple Int Bool)),
                build_sort!(pool, (Tuple Int)),
            ),
        ];

        for (a, b) in cases {
            assert!(!a.is_compatible(&b));
            let mut map = RapidHashMap::new();
            assert!(!a.match_with(&free_vars(&a), &b, &mut map));
        }
    }

    #[test]
    fn repeated_var_consistency_uses_param_eq() {
        let mut pool = Pool::new();
        let func = build_sort!(pool, (-> n n));

        // `n` is first bound to `ParamBitVec`, then matched against `BitVec(8)`.
        let target = build_sort!(pool, (-> ParamBitVec (BitVec 8)));
        let mut map = RapidHashMap::new();
        assert!(func.match_with(&free_vars(&func), &target, &mut map));
        assert_eq!(map["n"], build_sort!(pool, ParamBitVec));

        // Same, but with the two bitvector sorts swapped.
        let target = build_sort!(pool, (-> (BitVec 8) ParamBitVec));
        let mut map = RapidHashMap::new();
        assert!(func.match_with(&free_vars(&func), &target, &mut map));
        assert_eq!(map["n"], build_sort!(pool, (BitVec 8)));
    }

    #[test]
    fn par_target_bound_variables_are_not_captured() {
        let mut pool = Pool::new();

        // self = (-> x x), with parameter x
        let self_sort = build_sort!(pool, (-> x x));
        // target = (par (y) (-> y y))
        let target = build_sort!(pool, (par (y) (-> y y)));

        let mut map = RapidHashMap::new();
        assert!(!self_sort.match_with(&free_vars(&self_sort), &target, &mut map),);
    }

    /// A `Par` on the target side is still instantiable when its variables are already accounted
    /// for. This mirrors using a polymorphic constant (such as `nil`, of sort `(par (T) (List T))`)
    /// where the surrounding context has already fixed `T`.
    #[test]
    fn target_par_is_instantiable_when_its_variable_is_known() {
        let mut pool = Pool::new();
        let list_t = build_sort!(pool, (Datatype "List" T));
        let target = build_sort!(pool, (par (T) (Datatype "List" T)));

        let mut map = RapidHashMap::new();
        map.insert("T".into(), build_sort!(pool, Bool));
        assert!(list_t.match_with(&free_vars(&list_t), &target, &mut map));
    }
}
