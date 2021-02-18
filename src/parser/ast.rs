use num_rational::Ratio;

pub enum Term {
    Constant(Constant),
    Identifier(QualifiedIdentifier),
    // TODO: application, let, forall, exists, match, ! and choice
}

pub enum Constant {
    Numeral(u64),
    Decimal(Ratio<u64>),
    String(String),
}

pub struct QualifiedIdentifier {
    pub identifier: Identifier,
    pub sort: Option<Sort>,
}

pub enum Identifier {
    Simple(String),
    Indexed(String, Vec<Index>),
}

pub enum Index {
    Numeral(u64),
    Symbol(String),
}

pub enum Sort {
    NonParametric(Identifier),
    Parametric(Identifier, Vec<Sort>),
}
