use crate::ast::{Rc, Sort, pool::Pool};

/// The operator of an operation term.
#[carcara_macros::extend_operator_enum("operators.toml")]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Operator {
    // Logic
    /// The `=>` operator.
    #[name("=>")]
    Implies,

    /// The `and` operator.
    #[name("and")]
    And,

    /// The `or` operator.
    #[name("or")]
    Or,

    /// The `xor` operator.
    #[name("xor")]
    Xor,

    /// The `=` operator.
    #[name("=")]
    Equals,

    /// The `distinct` operator.
    #[name("distinct")]
    Distinct,

    // Arithmetic
    /// The `+` operator.
    #[name("+")]
    Add,

    /// The `-` operator.
    #[name("-")]
    Sub,

    /// The `*` operator.
    #[name("*")]
    Mult,

    /// The `div` operator.
    #[name("div")]
    IntDiv,

    /// The `/` operator.
    #[name("/")]
    RealDiv,

    /// The `abs` operator.
    #[name("abs")]
    Abs,

    /// The `<` operator.
    #[name("<")]
    LessThan,

    /// The `>` operator.
    #[name(">")]
    GreaterThan,

    /// The `<=` operator.
    #[name("<=")]
    LessEq,

    /// The `>=` operator.
    #[name(">=")]
    GreaterEq,

    /// The `to_real` operator.
    #[name("to_real")]
    ToReal,

    // Strings
    /// The `str.++` operator.
    #[name("str.++")]
    StrConcat,

    // Regular Expressions
    /// The `re.++` operator.
    #[name("re.++")]
    ReConcat,

    /// The `re.union` operator.
    #[name("re.union")]
    ReUnion,

    /// The `re.inter` operator.
    #[name("re.inter")]
    ReIntersection,

    /// The `re.diff` operator.
    #[name("re.diff")]
    ReDiff,

    /// The `re.from_automaton` operator.
    #[name("re.from_automaton")]
    ReFromAutomaton,

    // BV operators (unary)
    /// The `bvnot` operator.
    #[name("bvnot")]
    BvNot,

    /// The `bvneg` operator.
    #[name("bvneg")]
    BvNeg,

    // BV operators (binary, left-assoc)
    /// The `bvand` operator.
    #[name("bvand")]
    BvAnd,

    /// The `bvor` operator.
    #[name("bvor")]
    BvOr,

    /// The `bvadd` operator.
    #[name("bvadd")]
    BvAdd,

    /// The `bvmul` operator.
    #[name("bvmul")]
    BvMul,

    // BV operators (binary)
    /// The `bvudiv` operator.
    #[name("bvudiv")]
    BvUDiv,

    /// The `bvurem` operator.
    #[name("bvurem")]
    BvURem,

    /// The `bvshl` operator.
    #[name("bvshl")]
    BvShl,

    /// The `bvlshr` operator.
    #[name("bvlshr")]
    BvLShr,

    /// The `bvult` operator.
    #[name("bvult")]
    BvULt,

    /// The `concat` operator.
    #[name("concat")]
    BvConcat,

    /// The `bvnand` operator.
    #[name("bvnand")]
    BvNAnd,

    /// The `bvnor` operator.
    #[name("bvnor")]
    BvNOr,

    /// The `bvxor` operator.
    #[name("bvxor")]
    BvXor,

    /// The `bvxnor` operator.
    #[name("bvxnor")]
    BvXNor,

    /// The `bvcomp` operator.
    #[name("bvcomp")]
    BvComp,

    /// The `bvsub` operator.
    #[name("bvsub")]
    BvSub,

    /// The `bvsdiv` operator.
    #[name("bvsdiv")]
    BvSDiv,

    /// The `bvsrem` operator.
    #[name("bvsrem")]
    BvSRem,

    /// The `bvsmod` operator.
    #[name("bvsmod")]
    BvSMod,

    /// The `bvashr` operator.
    #[name("bvashr")]
    BvAShr,

    /// The `bvule` operator.
    #[name("bvule")]
    BvULe,

    /// The `bvugt` operator.
    #[name("bvugt")]
    BvUGt,

    /// The `bvuge` operator.
    #[name("bvuge")]
    BvUGe,

    /// The `bvslt` operator.
    #[name("bvslt")]
    BvSLt,

    /// The `bvsle` operator.
    #[name("bvsle")]
    BvSLe,

    /// The `bvsgt` operator.
    #[name("bvsgt")]
    BvSGt,

    /// The `bvsge` operator.
    #[name("bvsge")]
    BvSGe,

    /// The `ubv_to_int` operator.
    #[name("ubv_to_int")]
    UBvToInt,

    /// The `sbv_to_int` operator.
    #[name("sbv_to_int")]
    SBvToInt,

    /// The `@pbbterm` operator.
    #[name("@pbbterm")]
    BvPBbTerm,

    /// The `@bbterm` operator.
    #[name("@bbterm")]
    BvBbTerm,

    /// The `@bv` operator.
    #[name("@bv")]
    BvConst,

    /// The `@bvsize` operator.
    #[name("@bvsize")]
    BvSize,

    /// The `bvite` operator.
    ///
    /// This operator is not standard SMT-LIB, but from an extension of the bit-vectors theory used
    /// by cvc5. We have support for it to facilitate checking cvc5 proofs.
    #[name("bvite")]
    BvIte,

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
            // Logical
            Operator::Implies => Some(NaryCase::RightAssoc),
            Operator::And | Operator::Or | Operator::Xor => Some(NaryCase::LeftAssoc),
            Operator::Equals => Some(NaryCase::Chainable),
            Operator::Distinct => Some(NaryCase::Pairwise),

            // Integers/Reals
            Operator::Add
            | Operator::Sub
            | Operator::Mult
            | Operator::IntDiv
            | Operator::RealDiv => Some(NaryCase::LeftAssoc),
            Operator::LessThan | Operator::GreaterThan | Operator::LessEq | Operator::GreaterEq => {
                Some(NaryCase::Chainable)
            }

            // Strings
            Operator::StrConcat
            | Operator::ReConcat
            | Operator::ReUnion
            | Operator::ReIntersection
            | Operator::ReDiff => Some(NaryCase::LeftAssoc),
            Operator::StrLessThan | Operator::StrLessEq => Some(NaryCase::Chainable),

            // Bitvectors
            Operator::BvAnd | Operator::BvOr | Operator::BvAdd | Operator::BvMul => {
                Some(NaryCase::LeftAssoc)
            }

            // Clausal
            Operator::Cl | Operator::Delete => Some(NaryCase::LeftAssoc),

            _ => None,
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

/// The type signature of an operator.
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

#[cfg(test)]
mod tests {
    use super::{OperatorSig, Pool, SortSig};
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
