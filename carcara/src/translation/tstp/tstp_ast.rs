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
    // From the docs:
    // "The introduction of new non-variable symbols should be recorded in
    // a <new_symbol_record> in the <useful_info> field of the <inference_record>
    // of a derived formula, or in the <optional_info> field of the <internal_source>
    // of an introduced formula."
    pub useful_info: Symbol,
}

impl TstpAnnotatedFormula {
    /// Builds a new annotated formula. Implements a mechanism
    /// for providing names to the formula.
    /// TODO: should it generate the corresponding `useful_info`?
    pub fn new(
        provided_language: TstpLanguage,
        provided_name: Symbol,
        provided_role: TstpFormulaRole,
        provided_formula: TstpFormula,
        provided_source: Symbol,
        provided_useful_info: Symbol,
    ) -> Self {
        Self {
            language: provided_language,
            name: provided_name,
            role: provided_role,
            formula: provided_formula,
            source: provided_source,
            useful_info: provided_useful_info,
        }
    }
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
#[derive(Clone, Debug)]
pub enum TstpFormula {
    Variable(Symbol),

    // Logic
    UniversalQuant(Symbol, Box<TstpFormula>),

    ExistentialQuant(Symbol, Box<TstpFormula>),

    OperatorApp(TstpOperator, Vec<TstpFormula>),

    // TPTP jargon: functor.
    // TODO: do we need to introduce a special syntactic
    // category for functors?
    FunctorApp(Symbol, Vec<TstpFormula>),

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

#[derive(Clone, Debug)]
pub enum TstpOperator {
    // Logic
    // From TPTP docs:
    // Defined predicates recognized: $true and $false, with the obvious interpretations.
    True,
    False,
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
#[derive(Clone, Debug)]
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
