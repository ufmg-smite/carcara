//! Tstp concrete syntax's AST.
pub type Symbol = String;

/// Tstp annotated formula.
pub struct TstpAnnotatedFormula {
    pub language: TstpLanguage,
    pub name: Symbol,
    pub role: TstpFormulaRole,
    pub formula: TstpFormula,
    // TODO: not including this, for the moment
    pub source: Symbol,
    pub useful_info: Symbol,
}

/// Possible TPTP languages.
pub enum TstpLanguage {
    // First-order logic
    Fof,
    // Typed first-order logic
    Tff,
}

/// Possible formulae roles.
pub enum TstpFormulaRole {
    Axiom,
    Lemma,
    Conjecture,
    Hypothesis,
    // Logic used.
    Logic,
    Type,
}

/// Syntactic category of expressions that denote formulas but, also, values inhabiting
/// other types: numeric and string literals.
#[derive(Clone)]
pub enum TstpFormula {
    Variable(Symbol),

    // Logic
    True,

    False,

    UniversalQuant(Symbol, Box<TstpFormula>),

    ExistentialQuant(Symbol, Box<TstpFormula>),

    TstpOperator(Vec<TstpFormula>),

    //  Typing statements
    Typing(Box<TstpFormula>, TstpType),

    // Literals
    // Numeric
    Integer(rug::Integer),
    // TODO: only <unsigned_rational>  ::- <decimal><slash><positive_decimal>
    Rational(rug::Integer, rug::Integer),
    // TODO: Only <decimal_fraction>   ::- <decimal><dot_decimal>
    Real(rug::Rational),

    // Distinct object: inhabitant of type Individual ($i, in TPTP)
    DistinctObject(String),
}

pub enum TstpOperator {
    // Logic
    Not,
    Or,
    Xor,
    And,
    Implies,
    Consequence,
    Iff,
    // From TPTP docs: Conditional expressions have $ite as the functor.
    Ite,

    // Arith
    Sum,
    // Difference between two numbers.
    Difference,
    // Unary minus of a number.
    Uminus,
    Product,
    // Exact quotient of two numbers of the same type.
    Quotient,
    // Integral quotient of two numbers:
    // $quotient_e(N,D) - the Euclidean quotient, which has a non-negative remainder.
    QuotientE,

    // Relations (putting in the same category as operator, as happens in Alethe)
    Equality,
    Inequality,
    Less,
    LessEq,
    Greater,
    GreaterEq,
}

/// Type terms.
/// From TPTP docs:
/// "The defined types are $o - the Boolean type, $i - the type of individuals, $real - the type
/// of reals, $rat - the type of rational, and $int - the type of integers. New types are introduced
/// in formulae with the type role, based on $tType - the type of all types."
#[derive(Clone)]
pub enum TstpType {
    // TODO: just one universe?
    // $tType
    Universe,

    // User-defined constant types
    UserDefined(Symbol),

    // Primitive types
    Bool,

    // Numeric types
    Int,
    Rational,
    Real,

    // $i: the type of individuals
    Invidual,

    // TODO:? Function type: (TstpType ... ) > TstpType
    Fun(Vec<TstpType>, Box<TstpType>),
}

pub type TstpProof = Vec<TstpAnnotatedFormula>;
