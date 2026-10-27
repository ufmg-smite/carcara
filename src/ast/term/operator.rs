use crate::ast::{Rc, Sort, pool::Pool};

/// The operator of an operation term.
#[carcara_macros::extend_operator_enum("operators.toml")]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Operator {
    // Most operators supported by Carcara are defined in the `operators.toml` file, and generated
    // automatically using the `carcara_macros::extend_operator_enum` attribute. Type checking and
    // type inference for these operators is done using a generated `OperatorSig`.
    //
    // Here, we manually declare the remaining operators, the ones which cannot be expressed with a
    // fixed signature. These are operators whose type signature is not fixed (e.g. `set.insert`),
    // whose return type depends on the number of arguments (e.g. `tuple`), that use bitvector width
    // arithmetic (e.g. `concat`), or whose behavior is specially handled by the parser (e.g. `@bv`
    // and `re.from_automaton`)

    // Regular Expressions
    /// The `re.from_automaton` operator.
    #[name("re.from_automaton")]
    ReFromAutomaton,

    // BV operators
    /// The `concat` operator.
    #[name("concat")]
    BvConcat,

    /// The `@pbbterm` operator.
    #[name("@pbbterm")]
    BvPBbTerm,

    /// The `@bbterm` operator.
    #[name("@bbterm")]
    BvBbTerm,

    /// The `@bv` operator.
    #[name("@bv")]
    BvConst,

    // Misc.
    /// The `rare-list` operator, used to represent RARE lists.
    #[name("rare-list")]
    RareList,

    // The clausal operators
    /// The `cl` operator.
    #[name("cl")]
    Cl,

    // Sets and relations
    //
    // These operators are from cvc5's "Sets and Relations" theory extension, see:
    // https://cvc5.github.io/docs-ci/docs-main/theories/sets-and-relations.html
    /// The `set.insert` operator.
    #[name("set.insert")]
    SetInsert,

    /// The `tuple` operator.
    #[name("tuple")]
    Tuple,

    /// The `rel.transpose` operator.
    #[name("rel.transpose")]
    RelTranspose,

    /// The `rel.join` operator.
    #[name("rel.join")]
    RelJoin,

    /// The `rel.product` operator.
    #[name("rel.product")]
    RelProduct,
}

impl Operator {
    /// Returns this operator's signature, if it exists.
    ///
    /// Some operators cannot be represented with an [`OperatorSig`], in which case this method
    /// returns `None`.
    pub fn sig(&self) -> Option<&'static OperatorSig> {
        // We wrap the generated `raw_sig` method instead of using it directly, so that
        // rust-analyzer can properly suggest the `sig` method and infer its type
        self.raw_sig()
    }

    /// If this is a binary operator that can be applied to multiple arguments, returns an
    /// `[NaryCase]` representing its behaviour in that situation. Otherwise, returns `None`.
    pub fn nary_case(&self) -> Option<NaryCase> {
        match self {
            Operator::Cl | Operator::Delete => Some(NaryCase::LeftAssoc),
            _ => self.sig().and_then(|sig| sig.nary),
        }
    }
}

/// Represents the behaviour of an (otherwise binary) operator when applied to more than two
/// arguments.
///
/// This corresponds to SMT-LIB's function symbol annotation, which can be: `:chainable`,
/// `:left-assoc`, `:right-assoc` or `:pairwise`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NaryCase {
    /// `:chainable` operators.
    ///
    /// This means `(op a_1 ... a_n)` is syntax sugar for `(and (op a_1 a_2) ... (op a_n-1 a_n))`
    Chainable,

    /// `:left-assoc` operators.
    ///
    /// This means `(op a_1 ... a_n)` is syntax sugar for `(op (op a_1 ... a_n-1) a_n)`,
    /// recursively.
    LeftAssoc,

    /// `:right-assoc` operators.
    ///
    /// This means `(op a_1 ... a_n)` is syntax sugar for `(op a_1 (op a_2 ... a_n))`, recursively.
    RightAssoc,

    /// `:pairwise` operators.
    ///
    /// This means `(op a_1 ... a_n)` is syntax sugar for `(and (op a_1 a_2) ... (op a_1 a_n) ...
    /// (op a_n-1 a_n))`. That is, a conjunction of `op` applied to all possible pairs of `a_i`,
    /// `a_j`, with i != j.
    Pairwise,
}

/// A sort in the type signature of an operator.
#[derive(Debug)]
pub enum SortSig {
    Var(usize),
    /// A bitvector of any width. All bitvectors in a signature must have the same width, so they
    /// all share an extra sort parameter, always the last in the parameter list.
    BitVec,
    /// A bitvector of width 1. Its width is independent of the width shared by the `BitVec`s.
    Bit,
    /// Either `Int` or `Real`. All occurrences of `IntOrReal` in a signature share a sort, stored in
    /// an extra sort parameter, always the last in the parameter list. With Int/Real subtyping,
    /// mixing `Int` and `Real` widens that sort to `Real`.
    IntOrReal,
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
    pub fn match_with(
        &self,
        params: &mut [Option<Rc<Sort>>],
        sort: &Rc<Sort>,
        subtyping: bool,
    ) -> bool {
        match (self, sort.as_ref()) {
            (SortSig::Var(i), _) => match &params[*i] {
                Some(existing) => existing.is_compatible(sort),
                None => {
                    params[*i] = Some(sort.clone());
                    true
                }
            },
            (SortSig::BitVec, Sort::BitVec(_) | Sort::ParamBitVec) => {
                let slot = params.last_mut().unwrap();
                match slot {
                    // A bitvector with a known width replaces one with an unknown width
                    Some(existing) if existing.as_ref() != &Sort::ParamBitVec => {
                        existing.is_compatible(sort)
                    }
                    _ => {
                        *slot = Some(sort.clone());
                        true
                    }
                }
            }
            (SortSig::Bit, Sort::BitVec(1) | Sort::ParamBitVec) => true,
            (SortSig::IntOrReal, Sort::Int | Sort::Real) => {
                let slot = params.last_mut().unwrap();
                match slot {
                    Some(existing) if existing.as_ref() == sort.as_ref() => true,
                    // With subtyping, mixing `Int` and `Real` widens the shared sort to `Real`
                    Some(_) if subtyping => {
                        if sort.as_ref() == &Sort::Real {
                            *slot = Some(sort.clone());
                        }
                        true
                    }
                    Some(_) => false,
                    None => {
                        *slot = Some(sort.clone());
                        true
                    }
                }
            }
            (SortSig::Bool, Sort::Bool)
            | (SortSig::Int, Sort::Int)
            | (SortSig::Real, Sort::Real)
            | (SortSig::String, Sort::String)
            | (SortSig::RegLan, Sort::RegLan) => true,
            (SortSig::Array(a_sig, b_sig), Sort::Array(a, b)) => {
                a_sig.match_with(params, a, subtyping) && b_sig.match_with(params, b, subtyping)
            }
            (SortSig::Set(sig), Sort::Set(sort)) => sig.match_with(params, sort, subtyping),
            (SortSig::Tuple(sigs), Sort::Tuple(sorts)) if sigs.len() != sorts.len() => false,
            (SortSig::Tuple(sigs), Sort::Tuple(sorts)) => sigs
                .iter()
                .zip(sorts)
                .all(|(sig, sort)| sig.match_with(params, sort, subtyping)),
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
            SortSig::BitVec => match params.last().unwrap() {
                Some(s) => s.clone(),
                None => pool.add_sort(Sort::ParamBitVec),
            },
            SortSig::Bit => pool.add_sort(Sort::BitVec(1)),
            SortSig::IntOrReal => match params.last().unwrap() {
                Some(s) => s.clone(),
                None => pool.add_sort(Sort::Int),
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

/// The type signature of an operator.
#[derive(Debug)]
pub struct OperatorSig {
    pub name: &'static str,
    pub params: &'static [&'static str],
    pub arg_sorts: &'static [SortSig],
    pub return_sort: SortSig,
    pub nary: Option<NaryCase>,
}

impl OperatorSig {
    /// The maximum number of sort parameters in an operator signature, counting the extra parameter
    /// used by `BitVec` or `IntOrReal`.
    ///
    /// This allows the parameters to be stored in a stack-allocated array, for performance reasons.
    pub const MAX_SORT_PARAMS: usize = 4;

    /// Returns the signature of each argument. For n-ary operators, the last one is repeated
    /// indefinitely.
    pub fn arg_sigs(&self) -> impl Iterator<Item = &SortSig> {
        let rest = self.nary.and(self.arg_sorts.last());
        self.arg_sorts.iter().chain(rest.into_iter().cycle())
    }

    /// Computes the sort of an application of this operator to arguments with sorts `arg_sorts`.
    pub fn compute_sort(
        &self,
        pool: &mut Pool,
        arg_sorts: &[Rc<Sort>],
        subtyping: bool,
    ) -> Rc<Sort> {
        let mut params = [const { None }; Self::MAX_SORT_PARAMS];
        let params = &mut params[..self.params.len()];
        for (sig, sort) in self.arg_sigs().zip(arg_sorts) {
            sig.match_with(params, sort, subtyping);
        }
        self.return_sort.instantiate(pool, params, self.params)
    }
}

#[cfg(test)]
mod tests {
    use super::{NaryCase, OperatorSig, Pool, SortSig};
    use crate::ast::{Rc, Sort};

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
        nary: None,
    };

    /// The signature of `bvadd`: `BitVec BitVec -> BitVec`, left-associative.
    static BVADD: OperatorSig = OperatorSig {
        name: "bvadd",
        params: &["BitVec"],
        arg_sorts: &[SortSig::BitVec, SortSig::BitVec],
        return_sort: SortSig::BitVec,
        nary: Some(NaryCase::LeftAssoc),
    };

    /// The signature of `bvcomp`: `BitVec BitVec -> Bit`.
    static BVCOMP: OperatorSig = OperatorSig {
        name: "bvcomp",
        params: &["BitVec"],
        arg_sorts: &[SortSig::BitVec, SortSig::BitVec],
        return_sort: SortSig::Bit,
        nary: None,
    };

    /// The signature of `and`: `Bool Bool -> Bool`, left-associative.
    static AND: OperatorSig = OperatorSig {
        name: "and",
        params: &[],
        arg_sorts: &[SortSig::Bool, SortSig::Bool],
        return_sort: SortSig::Bool,
        nary: Some(NaryCase::LeftAssoc),
    };

    /// The signature of `=`: `X X -> Bool`, chainable.
    static EQUALS: OperatorSig = OperatorSig {
        name: "=",
        params: &["X"],
        arg_sorts: &[SortSig::Var(0), SortSig::Var(0)],
        return_sort: SortSig::Bool,
        nary: Some(NaryCase::Chainable),
    };

    /// The signature of `+`: `IntOrReal IntOrReal -> IntOrReal`, left-associative.
    static ADD: OperatorSig = OperatorSig {
        name: "+",
        params: &["IntOrReal"],
        arg_sorts: &[SortSig::IntOrReal, SortSig::IntOrReal],
        return_sort: SortSig::IntOrReal,
        nary: Some(NaryCase::LeftAssoc),
    };

    /// Matches every argument sort against the signature, failing on the first mismatch.
    fn matches(sig: &OperatorSig, sorts: &[Rc<Sort>]) -> bool {
        matches_with_subtyping(sig, sorts, false)
    }

    /// Like `matches`, but with Int/Real subtyping allowed if `subtyping` is true.
    fn matches_with_subtyping(sig: &OperatorSig, sorts: &[Rc<Sort>], subtyping: bool) -> bool {
        let mut params = vec![None; sig.params.len()];
        sig.arg_sigs()
            .zip(sorts)
            .all(|(arg_sig, sort)| arg_sig.match_with(&mut params, sort, subtyping))
    }

    #[test]
    fn match_concrete_sorts() {
        let mut pool = Pool::new();
        let [int, string] = [Sort::Int, Sort::String].map(|s| pool.add_sort(s));
        let array = pool.add_sort(Sort::Array(int.clone(), string.clone()));

        let args = [array.clone(), int.clone(), string.clone()];
        assert!(matches(&STORE, &args));
        assert_eq!(STORE.compute_sort(&mut pool, &args, false), array);

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
        assert_eq!(STORE.compute_sort(&mut pool, &args, false), array);

        // Sort variables match signatures that don't use sort parameters
        assert!(SortSig::Int.match_with(&mut [], &t0, false));
        assert!(SortSig::Set(&SortSig::Int).match_with(&mut [], &t0, false));
    }

    #[test]
    fn compute_sort_ignores_mismatches() {
        let mut pool = Pool::new();
        let [int, string] = [Sort::Int, Sort::String].map(|s| pool.add_sort(s));
        let array = pool.add_sort(Sort::Array(int, string.clone()));

        let args = [array.clone(), string.clone(), string];
        assert_eq!(STORE.compute_sort(&mut pool, &args, false), array);
    }

    #[test]
    fn instantiate_unbound_params() {
        let mut pool = Pool::new();
        let x = pool.add_sort(Sort::Var("X".into()));
        let expected = pool.add_sort(Sort::Set(x));

        let got = SortSig::Set(&SortSig::Var(0)).instantiate(&mut pool, &[None], &["X"]);
        assert_eq!(got, expected);
    }

    #[test]
    fn match_bitvectors() {
        let mut pool = Pool::new();
        let [bv4, bv8, param, int] = [
            Sort::BitVec(4),
            Sort::BitVec(8),
            Sort::ParamBitVec,
            Sort::Int,
        ]
        .map(|s| pool.add_sort(s));
        let var = pool.add_sort(Sort::Var("@T0".into()));

        // All bitvectors must have the same width
        assert!(matches(&BVADD, &[bv8.clone(), bv8.clone()]));
        assert_eq!(
            BVADD.compute_sort(&mut pool, &[bv8.clone(), bv8.clone()], false),
            bv8
        );
        assert!(!matches(&BVADD, &[bv8.clone(), bv4]));
        assert!(!matches(&BVADD, &[bv8.clone(), int]));

        // Bitvectors with unknown widths, like in RARE rules, match any width. The result has the
        // first known width, if there is one
        assert!(matches(&BVADD, &[param.clone(), bv8.clone()]));
        assert_eq!(
            BVADD.compute_sort(&mut pool, &[param.clone(), bv8.clone()], false),
            bv8
        );
        assert_eq!(
            BVADD.compute_sort(&mut pool, &[bv8.clone(), param.clone()], false),
            bv8
        );
        assert_eq!(
            BVADD.compute_sort(&mut pool, &[param.clone(), param.clone()], false),
            param
        );

        // Sort variables match any bitvector, without binding its width
        assert!(matches(&BVADD, &[var.clone(), bv8.clone()]));
        assert_eq!(
            BVADD.compute_sort(&mut pool, &[var.clone(), bv8.clone()], false),
            bv8
        );
        assert_eq!(
            BVADD.compute_sort(&mut pool, &[var.clone(), var], false),
            param
        );
    }

    #[test]
    fn match_nary() {
        let mut pool = Pool::new();
        let [bool_sort, int, string, bv4, bv8] = [
            Sort::Bool,
            Sort::Int,
            Sort::String,
            Sort::BitVec(4),
            Sort::BitVec(8),
        ]
        .map(|s| pool.add_sort(s));
        let var = pool.add_sort(Sort::Var("@T0".into()));

        // The last argument sort is repeated only for n-ary operators
        assert_eq!(STORE.arg_sigs().count(), STORE.arg_sorts.len());
        assert_eq!(AND.arg_sigs().take(5).count(), 5);

        let bools = [bool_sort.clone(), bool_sort.clone(), bool_sort.clone()];
        assert!(matches(&AND, &bools));
        assert!(!matches(&AND, &[bool_sort.clone(), bool_sort, int.clone()]));

        // All arguments of `=` must have the same sort
        assert!(matches(&EQUALS, &[int.clone(), int.clone(), int.clone()]));
        assert!(!matches(&EQUALS, &[int.clone(), int.clone(), string]));
        assert!(matches(&EQUALS, &[int.clone(), var, int]));

        // All bitvectors must have the same width
        let bvs = [bv8.clone(), bv8.clone(), bv8.clone()];
        assert!(matches(&BVADD, &bvs));
        assert_eq!(BVADD.compute_sort(&mut pool, &bvs, false), bv8);
        assert!(!matches(&BVADD, &[bv8.clone(), bv8, bv4]));
    }

    #[test]
    fn match_bit() {
        let mut pool = Pool::new();
        let [bv1, bv8, param] =
            [Sort::BitVec(1), Sort::BitVec(8), Sort::ParamBitVec].map(|s| pool.add_sort(s));
        let var = pool.add_sort(Sort::Var("@T0".into()));

        // `Bit` only matches bitvectors of width 1, or of unknown width
        for sort in [&bv1, &param, &var] {
            assert!(SortSig::Bit.match_with(&mut [], sort, false));
        }
        assert!(!SortSig::Bit.match_with(&mut [], &bv8, false));

        // The width of `Bit` is independent of the width shared by the other bitvectors
        assert!(matches(&BVCOMP, &[bv8.clone(), bv8.clone()]));
        assert_eq!(
            BVCOMP.compute_sort(&mut pool, &[bv8.clone(), bv8], false),
            bv1
        );
    }

    #[test]
    fn match_int_or_real() {
        let mut pool = Pool::new();
        let [int, real, string] = [Sort::Int, Sort::Real, Sort::String].map(|s| pool.add_sort(s));
        let var = pool.add_sort(Sort::Var("@T0".into()));

        // Without subtyping, all arguments must have the same sort
        assert!(matches(&ADD, &[int.clone(), int.clone()]));
        assert!(matches(&ADD, &[real.clone(), real.clone()]));
        assert!(!matches(&ADD, &[int.clone(), real.clone()]));
        assert!(!matches(&ADD, &[int.clone(), string.clone()]));
        assert_eq!(
            ADD.compute_sort(&mut pool, &[int.clone(), int.clone()], false),
            int
        );
        assert_eq!(
            ADD.compute_sort(&mut pool, &[real.clone(), real.clone()], false),
            real
        );

        // With subtyping, mixing `Int` and `Real` gives `Real`
        for args in [
            vec![int.clone(), real.clone()],
            vec![real.clone(), int.clone()],
            vec![int.clone(), int.clone(), real.clone()],
        ] {
            assert!(matches_with_subtyping(&ADD, &args, true));
            assert_eq!(ADD.compute_sort(&mut pool, &args, true), real);
        }
        assert!(!matches_with_subtyping(&ADD, &[int.clone(), string], true));

        // Sort variables don't set the shared sort, which defaults to `Int`
        assert_eq!(
            ADD.compute_sort(&mut pool, &[var.clone(), real.clone()], false),
            real
        );
        assert_eq!(ADD.compute_sort(&mut pool, &[var.clone(), var], false), int);
    }
}
