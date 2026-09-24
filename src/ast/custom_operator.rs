//! Custom operators, defined in `custom_operators.toml` and loaded at compile time.

use super::Sort;

/// The declared type signature of a custom operator.
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct CustomOperatorDef {
    pub name: &'static str,
    pub arg_sorts: &'static [Sort],
    pub return_sort: Sort,
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
    use super::CustomOperator;
    use crate::ast::Operator;
    use std::str::FromStr;

    #[test]
    fn custom_operator_names_do_not_shadow_built_ins() {
        for op in CustomOperator::ALL {
            assert!(Operator::from_str(op.def().name).is_err());
        }
    }
}
