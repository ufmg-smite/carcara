use num_rational::Ratio;

#[derive(Debug, PartialEq, Eq)]
pub enum Term {
    Constant(Constant),
    Identifier(QualifiedIdentifier),
    // TODO: application, let, forall, exists, match, ! and choice
}

#[derive(Debug, PartialEq, Eq)]
pub enum Constant {
    Numeral(u64),
    Decimal(Ratio<u64>),
    String(String),
}

#[derive(Debug, PartialEq, Eq)]
pub struct QualifiedIdentifier {
    pub identifier: Identifier,
    pub sort: Option<Sort>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Identifier {
    Simple(String),
    Indexed(String, Vec<Index>),
}

#[derive(Debug, PartialEq, Eq)]
pub enum Index {
    Numeral(u64),
    Symbol(String),
}

#[derive(Debug, PartialEq, Eq)]
pub enum Sort {
    NonParametric(Identifier),
    Parametric(Identifier, Vec<Sort>),
}
