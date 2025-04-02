use crate::checker::error::CheckerError;

use super::{RuleArgs, RuleResult};

pub fn cp_addition(RuleArgs { .. }: RuleArgs) -> RuleResult {
    Err(CheckerError::Unspecified)
}

pub fn cp_multiplication(RuleArgs { .. }: RuleArgs) -> RuleResult {
    Err(CheckerError::Unspecified)
}

pub fn cp_division(RuleArgs { .. }: RuleArgs) -> RuleResult {
    Err(CheckerError::Unspecified)
}

pub fn cp_saturation(RuleArgs { .. }: RuleArgs) -> RuleResult {
    Err(CheckerError::Unspecified)
}

mod tests {
    #[test]
    fn cp_addition() {}

    #[test]
    fn cp_multiplication() {}

    #[test]
    fn cp_division() {}

    #[test]
    fn cp_saturation() {}
}
