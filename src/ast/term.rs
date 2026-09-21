use super::{
    Rc, Sort,
    macros::impl_str_conversion_traits,
    match_term, match_term_err,
    pool::{PrimitivePool, TermPool},
};
use crate::{CheckerError, automata::Automaton};
use rug::{Integer, Rational};
use std::{collections::HashSet, hash::Hash, ops::Deref};

/// A term.
///
/// Many additional methods are implemented in [`Rc<Term>`].
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Term {
    /// A constant term.
    Const(Constant),

    /// A variable, consisting of an identifier and a sort.
    Var(String, Rc<Sort>),

    /// An application of a function to one or more terms.
    App(Rc<Term>, Vec<Rc<Term>>),

    /// An application of a built-in operator to one or more terms.
    Op(Operator, Vec<Rc<Term>>),

    /// A binder term. This can be either a quantifier term (`forall`/`exists`), a `choice` term, or
    /// a `lambda` term.
    Binder(Binder, BindingList, Rc<Term>),

    /// A `let` binder term.
    Let(BindingList<Rc<Term>>, Rc<Term>),

    /// A `match` term, consisting of a term to be matched and a
    /// sequence of (pattern,result) pairs, where each each pattern
    /// binds a number of variables
    Match(Rc<Term>, Vec<MatchCase>),

    /// A parameterized operation term, that is, an operation term whose operator receives extra
    /// arguments (besides the regular operation arguments), denoted by the `((_ <op> <op_args>)
    /// <args>)` syntax.
    ///
    /// This can be either:
    /// - An *indexed* operation term, that uses an indexed operator. In this case, the operator
    ///   parameters must be constants.
    /// - A *tester* of a datatype constructor `C`, denoted by `(_ is C)`.
    ParamOp {
        /// The operator.
        op: ParamOperator,

        /// The arguments given to the operator itself.
        ///
        /// These are the `<op_args>` in the syntax `((_ <op> <op_args>) <args>)`.
        op_args: Vec<Rc<Term>>,

        /// The arguments provided for the operation as a whole.
        ///
        /// These are the `<args>` in the syntax `((_ <op> <op_args>) <args>)`.
        args: Vec<Rc<Term>>,
    },

    /// A qualified operation term, that is, an operation whose operator has a type hint, denoted
    /// by the `(as <op> <sort>)` syntax.
    AsOp(QualifiedOperator, Rc<Sort>, Vec<Rc<Term>>),
}

/// A variable and an associated sort.
pub type SortedVar = (String, Rc<Sort>);

/// A constant term.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Constant {
    /// An integer constant term.
    Integer(Integer),

    /// A real constant term.
    Real(Rational),

    /// A string literal term.
    String(String),

    /// A regular expression term.
    ///
    /// The associated values are the textual term representation (e.g. `re.from_automaton ...`)
    /// and its internal [`Automaton`] representation, respectively
    RegLan(String, Automaton),

    /// A bitvector literal term.
    ///
    /// The associated values are the bitvector's value and width respectively.
    BitVec(Integer, usize),
}

/// A binder, either a quantifier (`forall` or `exists`), `choice`, or `lambda`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Binder {
    /// The `forall` quantifier.
    Forall,

    /// The `exists` quantifier.
    Exists,

    /// The `choice` binder.
    Choice,

    /// The `lambda` binder.
    Lambda,
}

/// A list of bindings, where each binding is a variable associated with a value.
///
/// Depending on the context, it can be a "sort" binding list (like the ones present in quantifier
/// terms) where each variable is associated with its sort; or a "value" binding list (like the
/// ones present in `let` terms) where each variable is associated with its bound value. This is
/// controlled by the generic parameter.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BindingList<V = Rc<Sort>>(pub Vec<(String, V)>);

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

    /// The `int.pow2` operator.
    Pow2,

    /// The `int.ispow2` operator.
    IsPow2,

    /// The `int.log2` operator.
    Log2,

    // Transcendentals
    //
    // These operators are from cvc5's "Transcendentals" theory extension, see:
    // https://cvc5.github.io/docs-ci/docs-main/theories/transcendentals.html
    /// The `real.pi` constant.
    RealPi,

    /// The `sqrt` operator.
    Sqrt,

    /// The `exp` operator.
    Exp,

    /// The `sin` operator.
    Sin,

    /// The `cos` operator.
    Cos,

    /// The `tan` operator.
    Tan,

    /// The `csc` operator.
    Csc,

    /// The `sec` operator.
    Sec,

    /// The `cot` operator.
    Cot,

    /// The `arcsin` operator.
    Arcsin,

    /// The `arccos` operator.
    Arccos,

    /// The `arctan` operator.
    Arctan,

    /// The `arccsc` operator.
    Arccsc,

    /// The `arcsec` operator.
    Arcsec,

    /// The `arccot` operator.
    Arccot,

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

    /// The `str.indexof_re` operator.
    ///
    /// This operator is not standard SMT-LIB, but from an extension of the Strings theory used
    /// by cvc5. We have support for it to facilitate checking cvc5 proofs.
    IndexOfRe,

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
    /// The `set.union` operator.
    SetUnion,

    /// The `set.inter` operator.
    SetInter,

    /// The `set.minus` operator.
    SetMinus,

    /// The `set.member` operator.
    SetMember,

    /// The `set.subset` operator.
    SetSubset,

    /// The `set.singleton` operator.
    SetSingleton,

    /// The `set.is_empty` operator.
    SetIsEmpty,

    /// The `set.is_singleton` operator.
    SetIsSingleton,

    /// The `set.card` operator.
    SetCard,

    /// The `set.insert` operator.
    SetInsert,

    /// The `set.complement` operator.
    SetComplement,

    /// The `tuple` operator.
    Tuple,

    /// The `tuple.unit` operator.
    TupleUnit,

    /// The `rel.transpose` operator.
    RelTranspose,

    /// The `rel.tclosure` operator.
    RelTclosure,

    /// The `rel.join` operator.
    RelJoin,

    /// The `rel.product` operator.
    RelProduct,
}

/// A case for a `match` term.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct MatchCase {
    /// The case pattern.
    pub pattern: MatchPattern,

    /// The case body.
    pub body: Rc<Term>,
}

impl MatchCase {
    /// Returns a slice of variables bound by the case pattern.
    pub fn bindings(&self) -> &[SortedVar] {
        self.pattern.bindings()
    }
}

/// A pattern for a `match` term.
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum MatchPattern {
    /// The `_` pattern.
    Wildcard,

    /// A single named variable.
    Variable(SortedVar),

    /// A constructor applied to a set of variables.
    Cons(String, Vec<SortedVar>),
}

impl MatchPattern {
    /// Returns a slice of variables bound by the pattern.
    pub fn bindings(&self) -> &[SortedVar] {
        match self {
            MatchPattern::Wildcard => &[],
            MatchPattern::Variable(var) => std::slice::from_ref(var),
            MatchPattern::Cons(_, args) => args,
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

            // Transcendentals
            Operator::RealPi
            | Operator::Sqrt
            | Operator::Exp
            | Operator::Sin
            | Operator::Cos
            | Operator::Tan
            | Operator::Csc
            | Operator::Sec
            | Operator::Cot
            | Operator::Arcsin
            | Operator::Arccos
            | Operator::Arctan
            | Operator::Arccsc
            | Operator::Arcsec
            | Operator::Arccot => None,

            // Arrays
            Operator::Select | Operator::Store => None,

            // Strings
            Operator::StrConcat
            | Operator::StrLessThan
            | Operator::StrLessEq
            | Operator::ReConcat
            | Operator::ReUnion
            | Operator::ReIntersection
            | Operator::ReDiff => Some(NaryCase::LeftAssoc),
            Operator::StrLen
            | Operator::CharAt
            | Operator::Substring
            | Operator::PrefixOf
            | Operator::SuffixOf
            | Operator::Contains
            | Operator::IndexOf
            | Operator::IndexOfRe
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
            | Operator::Pow2
            | Operator::IsPow2
            | Operator::Log2
            | Operator::RareList => None,

            // Clausal
            Operator::Cl | Operator::Delete => Some(NaryCase::LeftAssoc),

            // Sets and relations
            Operator::SetUnion
            | Operator::SetInter
            | Operator::SetMinus
            | Operator::SetMember
            | Operator::SetSubset
            | Operator::SetSingleton
            | Operator::SetIsEmpty
            | Operator::SetIsSingleton
            | Operator::SetCard
            | Operator::SetInsert
            | Operator::SetComplement
            | Operator::Tuple
            | Operator::TupleUnit
            | Operator::RelTranspose
            | Operator::RelTclosure
            | Operator::RelJoin
            | Operator::RelProduct => None,
        }
    }
}

/// The operator of a parameterized operation term.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ParamOperator {
    // Indexed operators
    /// The `extract` operator.
    BvExtract,

    /// The `@bit_of` operator.
    BvBitOf,

    /// The `@int_of` operator.
    BvIntOf,

    /// The `zero_extend` operator.
    ZeroExtend,

    /// The `sign_extend` operator.
    SignExtend,

    /// The `rotate_left` operator.
    RotateLeft,

    /// The `rotate_right` operator.
    RotateRight,

    /// The `repeat` operator.
    Repeat,

    /// The `bv` operator.
    BvConst,

    /// The `int_to_bv` operator.
    IntToBv,

    /// The `re.^` operator.
    RePower,

    /// The `re.loop` operator.
    ReLoop,

    // Datatypes
    /// The `is` tester for datatypes.
    Tester,

    // Sets and relations
    /// The `tuple.select` operator.
    TupleSelect,
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
    Pow2: "int.pow2",
    IsPow2: "int.ispow2",
    Log2: "int.log2",

    RealPi: "real.pi",
    Sqrt: "sqrt",
    Exp: "exp",
    Sin: "sin",
    Cos: "cos",
    Tan: "tan",
    Csc: "csc",
    Sec: "sec",
    Cot: "cot",
    Arcsin: "arcsin",
    Arccos: "arccos",
    Arctan: "arctan",
    Arccsc: "arccsc",
    Arcsec: "arcsec",
    Arccot: "arccot",

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
    IndexOfRe: "str.indexof_re",
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

    SetUnion: "set.union",
    SetInter: "set.inter",
    SetMinus: "set.minus",
    SetMember: "set.member",
    SetSubset: "set.subset",
    SetSingleton: "set.singleton",
    SetIsEmpty: "set.is_empty",
    SetIsSingleton: "set.is_singleton",
    SetCard: "set.card",
    SetInsert: "set.insert",
    SetComplement: "set.complement",
    Tuple: "tuple",
    TupleUnit: "tuple.unit",
    RelTranspose: "rel.transpose",
    RelTclosure: "rel.tclosure",
    RelJoin: "rel.join",
    RelProduct: "rel.product",
});

impl_str_conversion_traits!(ParamOperator {
    BvExtract: "extract",
    BvBitOf: "@bit_of",
    BvIntOf: "@int_of",
    ZeroExtend: "zero_extend",
    SignExtend: "sign_extend",
    RotateLeft: "rotate_left",
    RotateRight: "rotate_right",
    Repeat: "repeat",
    BvConst: "bv",

    IntToBv: "int_to_bv",

    RePower: "re.^",
    ReLoop: "re.loop",

    Tester: "is",

    TupleSelect: "tuple.select",
});

impl ParamOperator {
    /// Returns the number of "op args" the operator receives.
    pub fn num_op_args(&self) -> usize {
        use ParamOperator::*;
        match self {
            BvBitOf | BvIntOf | ZeroExtend | SignExtend | RotateLeft | RotateRight | Repeat
            | IntToBv | RePower | Tester | TupleSelect => 1,
            BvExtract | BvConst | ReLoop => 2,
        }
    }
}

/// An operator that can be used with the `(as <op> <sort>)` syntax
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum QualifiedOperator {
    /// The `const` operator.
    Const,

    /// The `set.empty` operator.
    SetEmpty,

    /// The `set.universe` operator.
    SetUniverse,
}

impl_str_conversion_traits!(QualifiedOperator {
    Const: "const",
    SetEmpty: "set.empty",
    SetUniverse: "set.universe",
});

impl std::ops::Not for Binder {
    type Output = Self;

    fn not(self) -> Self::Output {
        match self {
            Binder::Forall => Binder::Exists,
            Binder::Exists => Binder::Forall,
            _ => panic!("logical negation is only defined for quantifier binders"),
        }
    }
}

impl<V> AsRef<[(String, V)]> for BindingList<V> {
    fn as_ref(&self) -> &[(String, V)] {
        &self.0
    }
}

impl<V> Deref for BindingList<V> {
    type Target = Vec<(String, V)>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<'a, V> IntoIterator for &'a BindingList<V> {
    type Item = &'a (String, V);

    type IntoIter = std::slice::Iter<'a, (String, V)>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl<V: 'static> BindingList<V> {
    /// A constant empty binding list.
    pub(crate) const EMPTY: &'static Self = &BindingList(Vec::new());
}

impl From<SortedVar> for Term {
    fn from(var: SortedVar) -> Self {
        Term::Var(var.0, var.1)
    }
}

impl Term {
    /// Constructs a new boolean term.
    pub fn new_bool(value: impl Into<bool>) -> Self {
        let op = match value.into() {
            true => Operator::True,
            false => Operator::False,
        };
        Term::Op(op, Vec::new())
    }

    /// Constructs a new integer term.
    pub fn new_int(value: impl Into<Integer>) -> Self {
        Term::Const(Constant::Integer(value.into()))
    }

    /// Constructs a new real term.
    pub fn new_real(value: impl Into<Rational>) -> Self {
        Term::Const(Constant::Real(value.into()))
    }

    /// Constructs a new string term.
    pub fn new_string(value: impl Into<String>) -> Self {
        Term::Const(Constant::String(value.into()))
    }

    /// Constructs a new bv term.
    pub fn new_bv(value: impl Into<Integer>, width: usize) -> Self {
        Term::Const(Constant::BitVec(value.into(), width))
    }

    /// Constructs a new variable term.
    pub fn new_var(name: impl Into<String>, sort: Rc<Sort>) -> Self {
        Term::Var(name.into(), sort)
    }

    /// Returns the sort of this term. This does not make use of a cache --- if possible, prefer to
    /// use `TermPool::sort`.
    pub fn raw_sort(&self) -> Sort {
        let mut pool = PrimitivePool::new();
        let added = pool.add(self.clone());
        pool.sort(&added).as_ref().clone()
    }

    /// Returns `true` if the term is the empty String.
    pub fn is_empty_string(&self) -> bool {
        match self {
            Term::Const(Constant::String(s)) => s.is_empty(),
            _ => false,
        }
    }

    /// Returns `true` if the term is an integer or real constant.
    pub fn is_number(&self) -> bool {
        matches!(self, Term::Const(Constant::Real(_) | Constant::Integer(_)))
    }

    /// Returns `true` if the term is an integer or real constant, or one such constant negated
    /// with the `-` operator.
    pub fn is_signed_number(&self) -> bool {
        match match_term!((-x) = self) {
            Some(x) => x.is_number(),
            None => self.is_number(),
        }
    }

    /// Tries to extract a `Rational` from a term. Returns `Some` if the term is an integer or real
    /// constant.
    pub fn as_number(&self) -> Option<Rational> {
        match self {
            Term::Const(Constant::Real(r)) => Some(r.clone()),
            Term::Const(Constant::Integer(i)) => Some(i.clone().into()),
            _ => None,
        }
    }

    /// Tries to extract a `bool` from a term. Returns `Some` if the term is a boolean constant.
    pub fn as_bool(&self) -> Option<bool> {
        match self {
            Term::Op(Operator::True, _) => Some(true),
            Term::Op(Operator::False, _) => Some(false),
            _ => None,
        }
    }

    /// Tries to extract a `Integer` from a term. Returns `Some` if the term is an integer constant.
    pub fn as_integer(&self) -> Option<Integer> {
        match self {
            Term::Const(Constant::Integer(i)) => Some(i.clone()),
            _ => None,
        }
    }

    /// Tries to extract a `Rational` from a term, allowing negative values represented with the
    /// unary `-` operator. Returns `Some` if the term is an integer or real constant, or one such
    /// constant negated with the `-` operator.
    pub fn as_signed_number(&self) -> Option<Rational> {
        match match_term!((-x) = self) {
            Some(x) => x.as_number().map(|r| -r),
            None => self.as_number(),
        }
    }

    /// Tries to extract a `Integer` from a term, allowing negative values represented with the
    /// unary `-` operator. Returns `Some` if the term is an integer constant, or one such
    /// constant negated with the `-` operator.
    pub fn as_signed_integer(&self) -> Option<Integer> {
        match match_term!((-x) = self) {
            Some(x) => x.as_integer().map(|r| -r),
            None => self.as_integer(),
        }
    }

    /// Tries to extract a `BitVec` from a term. Returns `Some` if the
    /// term is a bitvector constant.
    pub fn as_bitvector(&self) -> Option<(Integer, usize)> {
        match self {
            Term::Const(Constant::BitVec(v, w)) => Some((v.clone(), *w)),
            _ => None,
        }
    }

    /// Tries to extract a `String` from a term. Returns `Some` if the term is a String constant.
    pub fn as_string(&self) -> Option<String> {
        match self {
            Term::Const(Constant::String(s)) => Some(s.to_owned()),
            _ => None,
        }
    }

    /// Tries to extract a `Rational` from a term, allowing fractions. This method will return
    /// `Some` if the term is:
    ///
    /// - A real or integer constant
    /// - An application of the `/` or `div` operators on two real or integer constants
    /// - An application of the unary `-` operator on one of the two previous cases
    pub fn as_fraction(&self) -> Option<Rational> {
        fn as_unsigned_fraction(term: &Term) -> Option<Rational> {
            match term {
                Term::Op(Operator::IntDiv | Operator::RealDiv, args) if args.len() == 2 => {
                    Some(args[0].as_signed_number()? / args[1].as_signed_number()?)
                }
                _ => term.as_number(),
            }
        }

        match match_term!((-x) = self) {
            Some(x) => as_unsigned_fraction(x).map(|r| -r),
            None => as_unsigned_fraction(self),
        }
    }

    /// Returns `true` if the term is a constant.
    pub fn is_const(&self) -> bool {
        matches!(self, Term::Const(_))
    }

    /// Returns `true` if the term is a variable.
    pub fn is_var(&self) -> bool {
        matches!(self, Term::Var(_, _))
    }

    /// Tries to extract the variable name from a term. Returns `Some` if the term is a variable.
    pub fn as_var(&self) -> Option<&str> {
        match self {
            Term::Var(var, _) => Some(var.as_str()),
            _ => None,
        }
    }

    /// Tries to unwrap an operation term, returning the `Operator` and the arguments. Returns
    /// `None` if the term is not an operation term.
    pub fn as_op(&self) -> Option<(Operator, &[Rc<Term>])> {
        match self {
            Term::Op(op, args) => Some((*op, args.as_slice())),
            _ => None,
        }
    }

    /// Tries to unwrap a quantifier term, returning the `Binder`, the bindings and the inner term.
    /// Returns `None` if the term is not a quantifier term.
    pub fn as_quant(&self) -> Option<(Binder, &BindingList, &Rc<Term>)> {
        match self {
            Term::Binder(q @ (Binder::Forall | Binder::Exists), b, t) => Some((*q, b, t)),
            _ => None,
        }
    }

    /// Tries to unwrap a binder term, returning the `Binder`, the bindings and the inner term.
    /// Returns `None` if the term is not a binder term.
    pub fn as_binder(&self) -> Option<(Binder, &BindingList, &Rc<Term>)> {
        match self {
            Term::Binder(binder, bindings, inner) => Some((*binder, bindings, inner)),
            _ => None,
        }
    }

    /// Tries to unwrap a `let` term, returning the bindings and the inner term. Returns `None` if
    /// the term is not a `let` term.
    pub fn as_let(&self) -> Option<(&BindingList<Rc<Term>>, &Rc<Term>)> {
        match self {
            Term::Let(b, t) => Some((b, t)),
            _ => None,
        }
    }

    /// Tries to unwrap an [`Automaton`] from a term. Returns `None` if the term is not a `RegLan` term.
    pub fn as_automaton(&self) -> Option<Automaton> {
        match self {
            Term::Const(Constant::RegLan(_, a)) => Some(a.clone()),
            _ => None,
        }
    }

    /// Returns `true` if the term is the boolean constant `true`.
    pub fn is_bool_true(&self) -> bool {
        *self == Term::Op(Operator::True, Vec::new())
    }

    /// Returns `true` if the term is the boolean constant `false`.
    pub fn is_bool_false(&self) -> bool {
        *self == Term::Op(Operator::False, Vec::new())
    }

    /// Returns `true` if the term is the given boolean constant `b`.
    pub fn is_bool_constant(&self, b: bool) -> bool {
        match b {
            true => self.is_bool_true(),
            false => self.is_bool_false(),
        }
    }
}

impl Rc<Term> {
    /// Returns whether the term is closed, that is, whether it contains no free variables aside
    /// from global variables.
    pub fn is_closed(&self, pool: &mut PrimitivePool, global_vars: &HashSet<Rc<Term>>) -> bool {
        pool.free_vars(self).iter().all(|x| global_vars.contains(x))
    }

    /// Removes a leading negation from the term, if it exists. Same thing as `match_term!((not t)
    /// = term)`.
    pub fn remove_negation(&self) -> Option<&Self> {
        match_term!((not t) = self)
    }

    /// Removes a leading negation from the term, if it exists. If it doesn't, returns a
    /// `CheckerError::TermOfWrongForm` error. Same thing as `match_term_err!((not t) = term)`.
    pub fn remove_negation_err(&self) -> Result<&Self, CheckerError> {
        match_term_err!((not t) = self)
    }

    /// Removes all leading negations from the term, and returns how many there were.
    pub fn remove_all_negations(&self) -> (u32, &Self) {
        let mut term = self;
        let mut n = 0;
        while let Some(t) = term.remove_negation() {
            term = t;
            n += 1;
        }
        (n, term)
    }

    /// Removes all leading negations from the term, and returns a boolean representing the term
    /// polarity.
    pub fn remove_all_negations_with_polarity(&self) -> (bool, &Self) {
        let (n, term) = self.remove_all_negations();
        (n % 2 == 0, term)
    }

    /// Similar to `Term::as_number`, but returns a `CheckerError` on failure.
    pub fn as_number_err(&self) -> Result<Rational, CheckerError> {
        self.as_number()
            .ok_or_else(|| CheckerError::ExpectedAnyNumber(self.clone()))
    }

    /// Similar to `Term::as_integer`, but returns a `CheckerError` on failure.
    pub fn as_integer_err(&self) -> Result<Integer, CheckerError> {
        self.as_integer()
            .ok_or_else(|| CheckerError::ExpectedAnyInteger(self.clone()))
    }

    /// Similar to `Term::as_signed_integer`, but returns a `CheckerError` on failure.
    pub fn as_signed_integer_err(&self) -> Result<Integer, CheckerError> {
        self.as_signed_integer()
            .ok_or_else(|| CheckerError::ExpectedAnyInteger(self.clone()))
    }

    /// Similar to `Term::as_integer_err`, but also checks if non-negative.
    pub fn as_usize_err(&self) -> Result<usize, CheckerError> {
        if let Some(i) = self.as_integer()
            && i >= 0
        {
            return Ok(i.to_usize().unwrap());
        }
        Err(CheckerError::ExpectedNonnegInteger(self.clone()))
    }

    /// Similar to `Term::as_signed_number`, but returns a `CheckerError` on failure.
    pub fn as_signed_number_err(&self) -> Result<Rational, CheckerError> {
        self.as_signed_number()
            .ok_or_else(|| CheckerError::ExpectedAnyNumber(self.clone()))
    }

    /// Similar to `Term::as_bitvector`, but returns a `CheckerError` on failure.
    pub fn as_bitvector_err(&self) -> Result<(Integer, usize), CheckerError> {
        self.as_bitvector()
            .ok_or_else(|| CheckerError::ExpectedBitvector(self.clone()))
    }

    /// Similar to `Term::as_string`, but returns a `CheckerError` on failure.
    pub fn as_string_err(&self) -> Result<String, CheckerError> {
        self.as_string()
            .ok_or_else(|| CheckerError::ExpectedAnyString(self.clone()))
    }

    /// Similar to `Term::as_fraction`, but returns a `CheckerError` on failure.
    pub fn as_fraction_err(&self) -> Result<Rational, CheckerError> {
        self.as_fraction()
            .ok_or_else(|| CheckerError::ExpectedAnyNumber(self.clone()))
    }

    /// Similar to `Term::as_bool`, but returns a `CheckerError` on failure.
    pub fn as_bool_err(&self) -> Result<bool, CheckerError> {
        self.as_bool()
            .ok_or_else(|| CheckerError::ExpectedAnyBoolConstant(self.clone()))
    }

    /// Tries to unwrap an operation term, returning the `Operator` and the arguments. Returns a
    /// `CheckerError` if the term is not an operation term.
    pub fn as_op_err(&self) -> Result<(Operator, &[Rc<Term>]), CheckerError> {
        self.as_op()
            .ok_or_else(|| CheckerError::ExpectedOperationTerm(self.clone()))
    }

    /// Tries to unwrap a quantifier term, returning the `Binder`, the bindings and the inner term.
    /// Returns a `CheckerError` if the term is not a quantifier term.
    pub fn as_quant_err(&self) -> Result<(Binder, &BindingList, &Rc<Term>), CheckerError> {
        self.as_quant()
            .ok_or_else(|| CheckerError::ExpectedQuantifierTerm(self.clone()))
    }

    /// Tries to unwrap a binder term, returning the `Binder`, the bindings and the inner term.
    /// Returns a `CheckerError` if the term is not a binder term.
    pub fn as_binder_err(&self) -> Result<(Binder, &BindingList, &Rc<Term>), CheckerError> {
        self.as_binder()
            .ok_or_else(|| CheckerError::ExpectedBinderTerm(self.clone()))
    }

    /// Tries to unwrap a `let` term, returning the bindings and the inner
    /// term. Returns a `CheckerError` if the term is not a `let` term.
    pub fn as_let_err(&self) -> Result<(&BindingList<Rc<Term>>, &Rc<Term>), CheckerError> {
        self.as_let()
            .ok_or_else(|| CheckerError::ExpectedLetTerm(self.clone()))
    }

    /// Similar to `Term::as_automaton`, but returns a `CheckerError` on failure.
    pub fn as_automaton_err(&self) -> Result<Automaton, CheckerError> {
        self.as_automaton()
            .ok_or_else(|| CheckerError::ExpectedAutomaton(self.clone()))
    }
}

impl Constant {
    /// Returns the sort of a constant. In case it's a `BitVec`, we only return the width.
    pub fn sort(&self) -> Sort {
        match self {
            Constant::Integer(_) => Sort::Int,
            Constant::Real(_) => Sort::Real,
            Constant::String(_) => Sort::String,
            Constant::RegLan(_, _) => Sort::RegLan,
            Constant::BitVec(_, width) => Sort::BitVec(*width),
        }
    }

    /// If this is an integer constant, returns its value as an [`Integer`]. Otherwise, returns
    /// `None`.
    pub fn as_integer(&self) -> Option<Integer> {
        match self {
            Constant::Integer(i) => Some(i.clone()),
            _ => None,
        }
    }
}
