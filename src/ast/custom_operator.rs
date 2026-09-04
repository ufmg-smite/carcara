//! Custom operators, defined in `custom_operators.toml` and loaded at compile time.

use super::Sort;

/// The declared type signature of a custom operator.
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct CustomOperatorDef {
    pub name: &'static str,
    pub arg_sorts: &'static [Sort],
    pub return_sort: Sort,
}

/// A custom operator, defined via `custom_operators.toml`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct CustomOperator(pub &'static CustomOperatorDef);

include!(concat!(env!("OUT_DIR"), "/custom_operators.rs"));

/// Looks up an operator by name, checking built-in operators first, then custom ones.
pub fn lookup_operator(name: &str) -> Option<super::Operator> {
    use std::str::FromStr;
    if let Ok(op) = super::Operator::from_str(name) {
        return Some(op);
    }
    CUSTOM_OPERATORS
        .iter()
        .find(|def| def.name == name)
        .map(|def| super::Operator::Custom(CustomOperator(def)))
}

#[cfg(test)]
mod tests {
    use super::CUSTOM_OPERATORS;
    use crate::ast::Operator;
    use std::str::FromStr;

    #[test]
    fn custom_operator_names_do_not_shadow_built_ins() {
        for def in CUSTOM_OPERATORS {
            assert!(Operator::from_str(def.name).is_err());
        }
    }
}
