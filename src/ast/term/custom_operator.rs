use crate::ast::{Rc, Sort, macros::impl_str_conversion_traits, pool::Pool};

/// The operator of an operation term.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Operator {
    /// The `true` boolean constant.
    True,

    /// The `false` boolean constant.
    False,

    // Logic
    /// The `not` operator.
    Not,

    /// The `=>` operator.
    Implies,

    /// The `and` operator.
    And,

    /// The `or` operator.
    Or,

    /// The `xor` operator.
    Xor,

    /// The `=` operator.
    Equals,

    /// The `distinct` operator.
    Distinct,

    /// The `ite` operator.
    Ite,

    // Arithmetic
    /// The `+` operator.
    Add,

    /// The `-` operator.
    Sub,

    /// The `*` operator.
    Mult,

    /// The `div` operator.
    IntDiv,

    /// The `/` operator.
    RealDiv,

    /// The `mod` operator.
    Mod,

    /// The `abs` operator.
    Abs,

    /// The `<` operator.
    LessThan,

    /// The `>` operator.
    GreaterThan,

    /// The `<=` operator.
    LessEq,

    /// The `>=` operator.
    GreaterEq,

    /// The `to_real` operator.
    ToReal,

    /// The `to_int` operator.
    ToInt,

    /// The `is_int` operator.
    IsInt,

    // Arrays
    /// The `select` operator.
    Select,

    /// The `store` operator.
    Store,

    // Strings
    /// The `str.++` operator.
    StrConcat,

    /// The `str.len` operator.
    StrLen,

    /// The `str.<` operator.
    StrLessThan,

    /// The `str.<=` operator.
    StrLessEq,

    /// The `str.at` operator.
    CharAt,

    /// The `str.substr` operator.
    Substring,

    /// The `str.prefixof` operator.
    PrefixOf,

    /// The `str.suffixof` operator.
    SuffixOf,

    /// The `str.contains` operator.
    Contains,

    /// The `str.indexof` operator.
    IndexOf,

    /// The `str.replace` operator.
    Replace,

    /// The `str.replace_all` operator.
    ReplaceAll,

    /// The `str.replace_re` operator.
    ReplaceRe,

    /// The `str.replace_re_all` operator.
    ReplaceReAll,

    /// The `str.is_digit` operator.
    StrIsDigit,

    /// The `str.to_code` operator.
    StrToCode,

    /// The `str.from_code` operator.
    StrFromCode,

    /// The `str.to_int` operator.
    StrToInt,

    /// The `str.from_int` operator.
    StrFromInt,

    // Regular Expressions
    /// The `str.to_re` operator.
    StrToRe,

    /// The `str.in_re` operator.
    StrInRe,

    /// The `re.none` operator.
    ReNone,

    /// The `re.all` operator.
    ReAll,

    /// The `re.allchar` operator.
    ReAllChar,

    /// The `re.++` operator.
    ReConcat,

    /// The `re.union` operator.
    ReUnion,

    /// The `re.inter` operator.
    ReIntersection,

    /// The `re.*` operator.
    ReKleeneClosure,

    /// The `re.comp` operator.
    ReComplement,

    /// The `re.diff` operator.
    ReDiff,

    /// The `re.+` operator.
    ReKleeneCross,

    /// The `re.opt` operator.
    ReOption,

    /// The `re.range` operator.
    ReRange,

    /// The `re.from_automaton` operator.
    ReFromAutomaton,

    // BV operators (unary)
    /// The `bvnot` operator.
    BvNot,

    /// The `bvneg` operator.
    BvNeg,

    // BV operators (binary, left-assoc)
    /// The `bvand` operator.
    BvAnd,

    /// The `bvor` operator.
    BvOr,

    /// The `bvadd` operator.
    BvAdd,

    /// The `bvmul` operator.
    BvMul,

    // BV operators (binary)
    /// The `bvudiv` operator.
    BvUDiv,

    /// The `bvurem` operator.
    BvURem,

    /// The `bvshl` operator.
    BvShl,

    /// The `bvlshr` operator.
    BvLShr,

    /// The `bvult` operator.
    BvULt,

    /// The `concat` operator.
    BvConcat,

    /// The `bvnand` operator.
    BvNAnd,

    /// The `bvnor` operator.
    BvNOr,

    /// The `bvxor` operator.
    BvXor,

    /// The `bvxnor` operator.
    BvXNor,

    /// The `bvcomp` operator.
    BvComp,

    /// The `bvsub` operator.
    BvSub,

    /// The `bvsdiv` operator.
    BvSDiv,

    /// The `bvsrem` operator.
    BvSRem,

    /// The `bvsmod` operator.
    BvSMod,

    /// The `bvashr` operator.
    BvAShr,

    /// The `bvule` operator.
    BvULe,

    /// The `bvugt` operator.
    BvUGt,

    /// The `bvuge` operator.
    BvUGe,

    /// The `bvslt` operator.
    BvSLt,

    /// The `bvsle` operator.
    BvSLe,

    /// The `bvsgt` operator.
    BvSGt,

    /// The `bvsge` operator.
    BvSGe,

    /// The `ubv_to_int` operator.
    UBvToInt,

    /// The `sbv_to_int` operator.
    SBvToInt,

    /// The `@pbbterm` operator.
    BvPBbTerm,

    /// The `@bbterm` operator.
    BvBbTerm,

    /// The `@bv` operator.
    BvConst,

    /// The `@bvsize` operator.
    BvSize,

    /// The `bvite` operator.
    ///
    /// This operator is not standard SMT-LIB, but from an extension of the bit-vectors theory used
    /// by cvc5. We have support for it to facilitate checking cvc5 proofs.
    BvIte,

    // Misc.
    /// The `rare-list` operator, used to represent RARE lists.
    RareList,

    // The clausal operators
    /// The `cl` operator.
    Cl,

    /// The `@d` operator.
    Delete,

    // Sets and relations
    //
    // These operators are from cvc5's "Sets and Relations" theory extension, see:
    // https://cvc5.github.io/docs-ci/docs-main/theories/sets-and-relations.html
    /// The `set.insert` operator.
    SetInsert,

    /// The `tuple` operator.
    Tuple,

    /// The `rel.transpose` operator.
    RelTranspose,

    /// The `rel.join` operator.
    RelJoin,

    /// The `rel.product` operator.
    RelProduct,

    /// A custom operator, defined via `custom_operators.toml`.
    Custom(CustomOperator),
}

impl_str_conversion_traits!(Operator {
    True: "true",
    False: "false",

    Not: "not",
    Implies: "=>",
    And: "and",
    Or: "or",
    Xor: "xor",
    Equals: "=",
    Distinct: "distinct",
    Ite: "ite",

    Add: "+",
    Sub: "-",
    Mult: "*",
    IntDiv: "div",
    RealDiv: "/",
    Mod: "mod",
    Abs: "abs",
    LessThan: "<",
    GreaterThan: ">",
    LessEq: "<=",
    GreaterEq: ">=",
    ToReal: "to_real",
    ToInt: "to_int",
    IsInt: "is_int",

    Select: "select",
    Store: "store",

    StrConcat: "str.++",
    StrLen: "str.len",
    StrLessThan: "str.<",
    StrLessEq: "str.<=",
    CharAt: "str.at",
    Substring: "str.substr",
    PrefixOf: "str.prefixof",
    SuffixOf: "str.suffixof",
    Contains: "str.contains",
    IndexOf: "str.indexof",
    Replace: "str.replace",
    ReplaceAll: "str.replace_all",
    ReplaceRe: "str.replace_re",
    ReplaceReAll: "str.replace_re_all",
    StrIsDigit: "str.is_digit",
    StrToCode: "str.to_code",
    StrFromCode: "str.from_code",
    StrToInt: "str.to_int",
    StrFromInt: "str.from_int",

    StrToRe: "str.to_re",
    StrInRe: "str.in_re",
    ReNone: "re.none",
    ReAll: "re.all",
    ReAllChar: "re.allchar",
    ReConcat: "re.++",
    ReUnion: "re.union",
    ReIntersection: "re.inter",
    ReKleeneClosure: "re.*",
    ReComplement: "re.comp",
    ReDiff: "re.diff",
    ReKleeneCross: "re.+",
    ReOption: "re.opt",
    ReRange: "re.range",
    ReFromAutomaton: "re.from_automaton",

    BvNot: "bvnot",
    BvNeg: "bvneg",
    BvAnd: "bvand",
    BvOr: "bvor",
    BvAdd: "bvadd",
    BvMul: "bvmul",
    BvUDiv: "bvudiv",
    BvURem: "bvurem",
    BvShl: "bvshl",
    BvLShr: "bvlshr",
    BvULt: "bvult",

    BvConcat: "concat",
    BvNAnd: "bvnand",
    BvNOr: "bvnor",
    BvXor: "bvxor",
    BvXNor: "bvxnor",
    BvComp: "bvcomp",
    BvSub: "bvsub",
    BvSDiv: "bvsdiv",
    BvSRem: "bvsrem",
    BvSMod: "bvsmod",
    BvAShr: "bvashr",

    BvULe: "bvule",
    BvUGt: "bvugt",
    BvUGe: "bvuge",
    BvSLt: "bvslt",
    BvSLe: "bvsle",
    BvSGt: "bvsgt",
    BvSGe: "bvsge",

    UBvToInt: "ubv_to_int",
    SBvToInt: "sbv_to_int",

    BvPBbTerm: "@pbbterm",
    BvBbTerm: "@bbterm",
    BvConst: "@bv",
    BvSize: "@bvsize",

    BvIte: "bvite",

    RareList: "rare-list",

    Cl: "cl",
    Delete: "@d",

    SetInsert: "set.insert",
    Tuple: "tuple",
    RelTranspose: "rel.transpose",
    RelJoin: "rel.join",
    RelProduct: "rel.product",
}, extra_display: |f| {
    Operator::Custom(op) => write!(f, "{}", op.sig().name),
});

impl Operator {
    /// If this is a binary operator that can be applied to multiple arguments, returns an
    /// `[NaryCase]` representing its behaviour in that situation. Otherwise, returns `None`.
    pub fn nary_case(&self) -> Option<NaryCase> {
        // We avoid using the wildcard pattern (i.e. `_`) in this match expression so that when
        // someone adds a new operator, they are reminded to add it to this match
        match self {
            // Logical
            Operator::Implies => Some(NaryCase::RightAssoc),
            Operator::And | Operator::Or | Operator::Xor => Some(NaryCase::LeftAssoc),
            Operator::Equals => Some(NaryCase::Chainable),
            Operator::Distinct => Some(NaryCase::Pairwise),
            Operator::True | Operator::False | Operator::Not | Operator::Ite => None,

            // Integers/Reals
            Operator::Add
            | Operator::Sub
            | Operator::Mult
            | Operator::IntDiv
            | Operator::RealDiv => Some(NaryCase::LeftAssoc),
            Operator::LessThan | Operator::GreaterThan | Operator::LessEq | Operator::GreaterEq => {
                Some(NaryCase::Chainable)
            }
            Operator::Mod
            | Operator::Abs
            | Operator::ToReal
            | Operator::ToInt
            | Operator::IsInt => None,

            // Arrays
            Operator::Select | Operator::Store => None,

            // Strings
            Operator::StrConcat
            | Operator::ReConcat
            | Operator::ReUnion
            | Operator::ReIntersection
            | Operator::ReDiff => Some(NaryCase::LeftAssoc),
            Operator::StrLessThan | Operator::StrLessEq => Some(NaryCase::Chainable),
            Operator::StrLen
            | Operator::CharAt
            | Operator::Substring
            | Operator::PrefixOf
            | Operator::SuffixOf
            | Operator::Contains
            | Operator::IndexOf
            | Operator::Replace
            | Operator::ReplaceAll
            | Operator::ReplaceRe
            | Operator::ReplaceReAll
            | Operator::StrIsDigit
            | Operator::StrToCode
            | Operator::StrFromCode
            | Operator::StrToInt
            | Operator::StrFromInt
            | Operator::StrToRe
            | Operator::StrInRe
            | Operator::ReNone
            | Operator::ReAll
            | Operator::ReAllChar
            | Operator::ReKleeneClosure
            | Operator::ReComplement
            | Operator::ReKleeneCross
            | Operator::ReOption
            | Operator::ReRange
            | Operator::ReFromAutomaton => None,

            // Bitvectors
            Operator::BvAnd | Operator::BvOr | Operator::BvAdd | Operator::BvMul => {
                Some(NaryCase::LeftAssoc)
            }
            Operator::BvNot
            | Operator::BvNeg
            | Operator::BvUDiv
            | Operator::BvURem
            | Operator::BvShl
            | Operator::BvLShr
            | Operator::BvULt
            | Operator::BvConcat
            | Operator::BvNAnd
            | Operator::BvNOr
            | Operator::BvXor
            | Operator::BvXNor
            | Operator::BvComp
            | Operator::BvSub
            | Operator::BvSDiv
            | Operator::BvSRem
            | Operator::BvSMod
            | Operator::BvAShr
            | Operator::BvULe
            | Operator::BvUGt
            | Operator::BvUGe
            | Operator::BvSLt
            | Operator::BvSLe
            | Operator::BvSGt
            | Operator::BvSGe
            | Operator::UBvToInt
            | Operator::SBvToInt
            | Operator::BvPBbTerm
            | Operator::BvBbTerm
            | Operator::BvConst
            | Operator::BvSize
            | Operator::BvIte
            | Operator::RareList => None,

            // Clausal
            Operator::Cl | Operator::Delete => Some(NaryCase::LeftAssoc),

            // Sets and relations
            Operator::SetInsert
            | Operator::Tuple
            | Operator::RelTranspose
            | Operator::RelJoin
            | Operator::RelProduct => None,

            Operator::Custom(_) => None,
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
