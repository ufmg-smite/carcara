//! Tstp concrete syntax's AST.

pub type Symbol = String;
pub type TstpInferenceRuleName = String;

/// Tstp annotated formula.
pub struct TstpAnnotatedFormula {
    pub language: TstpLanguage,
    pub name: Symbol,
    pub role: TstpFormulaRole,
    pub formula: TstpFormula,
    pub source: TstpAnnotatedFormulaSource,
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
        provided_source: TstpAnnotatedFormulaSource,
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
/// The TPTP language spec. introduces formula roles
/// using the the so-called "semantic grammar rules":
/// "These define specific values that make semantic sense when more general
/// syntactic rules apply".
#[derive(PartialEq, Eq, Hash, Clone)] // To use them as HashMap keys.
pub enum TstpFormulaRole {
    // From the docs:
    // "assumption"s can be used like axioms, but must be discharged before a derivation is complete.
    Assumption,
    // From the docs:
    // "axiom"s are accepted, without proof. There is no guarantee that the
    // axioms of a problem are consistent.
    Axiom,
    Lemma,
    Conjecture,
    // From the docs:
    // "hypothesis"s are assumed to be true for a particular problem, and are
    // used like "axiom"s.
    Hypothesis,
    // Logic used.
    Logic,
    Type,
    // From TPTP's docs:
    // "plain formulae have no special user semantics, and are typically used
    // in derivation output"
    Plain,
}

/// Syntactic category of expressions that denote formulas but, also, values
/// inhabiting other types: numeric and string literals.
#[derive(Clone, Debug)]
pub enum TstpFormula {
    Variable(Symbol),

    // Logic
    UniversalQuant(Symbol, Box<TstpFormula>),

    ExistentialQuant(Symbol, Box<TstpFormula>),

    // Application of built-in operators. Arity captured through ASTs, for more robust
    // type checking.
    NullaryOperatorApp(TstpNullaryOperator),
    UnaryOperatorApp(TstpUnaryOperator, Box<TstpFormula>),
    BinaryOperatorApp(TstpBinaryOperator, Box<TstpFormula>, Box<TstpFormula>),

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

// NOTE: To simplify internal architecture, we define this sum-type of operators.
#[derive(Clone, Debug)]
pub enum TstpOperator {
    NullaryOperator(TstpNullaryOperator),

    UnaryOperator(TstpUnaryOperator),

    BinaryOperator(TstpBinaryOperator),
}

#[derive(Clone, Debug)]
pub enum TstpNullaryOperator {
    // Logical nullary connectives
    // From TPTP docs:
    // Defined predicates recognized: $true and $false, with the obvious interpretations.
    True,
    False,
}

#[derive(Clone, Debug)]
pub enum TstpUnaryOperator {
    // Logical connectives
    Not,

    // Unary minus of a number.
    Uminus,
}

#[derive(Clone, Debug)]
pub enum TstpBinaryOperator {
    // Logical connectives
    // From TPTP docs:
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

/// From TPTP's docs:
/// "The source field is used to record where the annotated formula came from, and is most
///   commonly a file record or an inference record. A file record stores the name of the file
///   from which the annotated formula was read, and optionally the name of the annotated
///   formula as it occurs in that file - this might be different from the name of the annotated
///   formula itself, e.g., if an ATP systems reads an annotated formula, renames it, and then
///   prints it out. An inference record stores information about an inferred formula."
#[derive(Clone, Debug)]
pub enum TstpAnnotatedFormulaSource {
    // We are collapsing a little bit the structure of the grammar rules for "source".
    // Its original rules are:
    // <source> ::= <dag_source> | <internal_source> | <external_source> | unknown | [<sources>]

    // The following corresponds to the "internal_source" category from the grammar.
    // <internal_source>  ::= introduced(<intro_type>,<useful_info>,<parents>)
    InternalSourceIntroduced(
        TstpInternalSourceIntroducedType,
        TstpSourceUsefulInfo,
        Vec<TstpAnnotatedFormulaSource>,
    ),

    // The following corresponds to the "dag_source" category from the grammar.
    // <dag_source>           ::= <name> | <inference_record>

    // Inference record: inference(rule name, general data, parent formulas)
    // From docs:
    // "<parents> can be empty in cases when there is a justification for a
    // tautologous theorem. In cases when a tautology is introduced as a leaf,
    // e.g., for splitting, then use an <internal_source>.
    DagSourceInference(
        TstpInferenceRuleName,
        TstpSourceUsefulInfo,
        Vec<TstpParentFormula>,
    ),

    DagSourceName(Symbol),

    // No source provided
    Empty,
}

// TODO: we are just modelling the case when
// <parent_details> produces an empty literal
// <parent_info> ::= <source><parent_details>
// <parent_details> ::= :<general_term> | <nothing>
pub type TstpParentFormula = TstpAnnotatedFormulaSource;

#[derive(Clone, Debug)]
pub enum TstpInferenceStatus {
    Thm,
}

#[derive(Clone, Debug)]
pub enum TstpInternalSourceIntroducedType {
    Name(Symbol),
    Definition,
    Tautology,
    Assumption,
}

// useful_info has 2 kinds of productions:
// - regular grammar rules: <useful_info> ::= <general_list>
// - semantic grammar rules: <useful_info> :== [] | [<info_items>]
#[derive(Clone, Debug)]
pub enum TstpSourceUsefulInfo {
    // Regular grammar rules: "general data"
    GeneralDataNewSymbols(Vec<Symbol>),
    // TODO: arbitrary list of symbols?
    GeneralDataGeneralList(Vec<Symbol>),

    // Semantics grammar rules: "info items"
    InfoItems(Vec<TstpInfoItem>),
}

/// Productions of <`info_item`>.
#[derive(Clone, Debug)]
pub enum TstpInfoItem {
    // Productions of <inference_item>:
    // <inference_status>
    InferenceItemInferenceStatusStatus(TstpInferenceStatus),
    InferenceItemInferenceStatusInferenceInfo(
        TstpInferenceRuleName,
        TstpInferenceInfoGeneralListQualifier,
        // General list
        Vec<Symbol>,
    ),

    // <assumptions_record>
    InferenceItemAssumptionsRecord(Vec<Symbol>),
}

// Represents the possible values of <atomic_word> in the <inference_info>
// production rule. From the docs
// "<atomic_word> indicates the information being recorded in the
//  <general_list>. The <atomic_word> are (loosely) set by TPTP
// conventions, and include esplit, sr_split, and discharge."
#[derive(Clone, Debug)]
pub enum TstpInferenceInfoGeneralListQualifier {
    Discharge,
}

pub type TstpProof = Vec<TstpAnnotatedFormula>;
