use super::{RuleArgs, RuleResult};
use crate::checker::error::CheckerError;

/// Implements the equality rule
/// The expected shape is:
///    `(= (= x y) (= (- (+ sum_x) (+ sum_y)) 0))`
pub fn pbblast_bveq(RuleArgs { .. }: RuleArgs) -> RuleResult {
    Err(CheckerError::Unspecified)
}

/// Implements the unsigned-less-than rule.
/// The expected shape is:
///    `(= (bvult x y) (>= (- (+ sum_y) (+ sum_x)) 1))`
pub fn pbblast_bvult(RuleArgs { .. }: RuleArgs) -> RuleResult {
    Err(CheckerError::Unspecified)
}

/// Implements the unsigned-greater-than rule.
///
/// The expected shape is:
///    `(= (bvugt x y) (>= (- (+ sum_x) (+ sum_y)) 1))`
pub fn pbblast_bvugt(RuleArgs { .. }: RuleArgs) -> RuleResult {
    Err(CheckerError::Unspecified)
}

/// Implements the unsigned-greater-or-equal rule.
///
/// The expected shape is:
///    `(= (bvuge x y) (>= (- (+ sum_x) (+ sum_y)) 0))`
pub fn pbblast_bvuge(RuleArgs { .. }: RuleArgs) -> RuleResult {
    Err(CheckerError::Unspecified)
}

/// Implements the unsigned-less-or-equal rule.
///
/// The expected shape is:
///    `(= (bvule x y) (>= (- (+ sum_y) (+ sum_x)) 0))`
pub fn pbblast_bvule(RuleArgs { .. }: RuleArgs) -> RuleResult {
    Err(CheckerError::Unspecified)
}

/// Implements the signed-less-than rule.
///
/// The expected shape is:
///    `(= (bvslt x y) (>= (+ (- y_sum (* 2^(n-1) y_n-1))) (- (* 2^(n-1) x_n-1) x_sum)) 1))`
pub fn pbblast_bvslt(RuleArgs { .. }: RuleArgs) -> RuleResult {
    Err(CheckerError::Unspecified)
}

/// Implements the signed-greater-than rule.
///
/// The expected shape is:
///    `(= (bvsgt x y) (>= (+ (- x_sum (* 2^(n-1) x_n-1))) (- (* 2^(n-1) y_n-1) y_sum)) 1))`
pub fn pbblast_bvsgt(RuleArgs { .. }: RuleArgs) -> RuleResult {
    Err(CheckerError::Unspecified)
}

/// Implements the signed-greater-equal rule.
///
/// The expected shape is:
///    `(= (bvsge x y) (>= (+ (- x_sum (* 2^(n-1) x_n-1))) (- (* 2^(n-1) y_n-1) y_sum)) 0))`
pub fn pbblast_bvsge(RuleArgs { .. }: RuleArgs) -> RuleResult {
    Err(CheckerError::Unspecified)
}

/// Implements the signed-less-equal rule.
///
/// The expected shape is:
///    `(= (bvsle x y) (>= (+ (- y_sum (* 2^(n-1) y_n-1))) (- (* 2^(n-1) x_n-1) x_sum)) 0))`
pub fn pbblast_bvsle(RuleArgs { .. }: RuleArgs) -> RuleResult {
    Err(CheckerError::Unspecified)
}

/// Implements the blasting of a bitvector variable
pub fn pbblast_pbbvar(RuleArgs { .. }: RuleArgs) -> RuleResult {
    Err(CheckerError::Unspecified)
}

/// Implements the blasting of a constant
pub fn pbblast_pbbconst(RuleArgs { .. }: RuleArgs) -> RuleResult {
    Err(CheckerError::Unspecified)
}

/// Implements the bitwise exclusive or operation.
pub fn pbblast_bvxor(RuleArgs { .. }: RuleArgs) -> RuleResult {
    Err(CheckerError::Unspecified)
}

/// Implements the bitwise and operation.
pub fn pbblast_bvand(RuleArgs { .. }: RuleArgs) -> RuleResult {
    Err(CheckerError::Unspecified)
}

mod tests {
    #[test]
    fn pbblast_bveq_1() {}

    #[test]
    fn pbblast_bveq_2() {}

    #[test]
    fn pbblast_bveq_8() {}

    #[test]
    fn pbblast_bvult_1() {}

    #[test]
    fn pbblast_bvult_2() {}

    #[test]
    fn pbblast_bvult_8() {}

    #[test]
    fn pbblast_bvugt_1() {}

    #[test]
    fn pbblast_bvugt_2() {}

    #[test]
    fn pbblast_bvugt_8() {}

    #[test]
    fn pbblast_bvuge_1() {}

    #[test]
    fn pbblast_bvuge_2() {}

    #[test]
    fn pbblast_bvuge_8() {}

    #[test]
    fn pbblast_bvule_1() {}

    #[test]
    fn pbblast_bvule_2() {}

    #[test]
    fn pbblast_bvule_8() {}

    // TODO: What should happen to a signed operation on BitVec 1 ??

    #[test]
    fn pbblast_bvslt_2() {}

    #[test]
    fn pbblast_bvslt_4() {}

    #[test]
    fn pbblast_bvsgt_2() {}

    #[test]
    fn pbblast_bvsgt_4() {}

    #[test]
    fn pbblast_bvsge_2() {}

    #[test]
    fn pbblast_bvsge_4() {}

    #[test]
    fn pbblast_bvsle_2() {}

    #[test]
    fn pbblast_bvsle_4() {}

    #[test]
    fn pbblast_pbbvar_1() {}

    #[test]
    fn pbblast_pbbvar_2() {}

    #[test]
    fn pbblast_pbbvar_8() {}

    #[test]
    fn pbblast_pbbconst_1() {}

    #[test]
    fn pbblast_pbbconst_2() {}

    #[test]
    fn pbblast_pbbconst_4() {}

    #[test]
    fn pbblast_pbbconst_8() {}

    #[test]
    fn pbblast_bvxor_1() {}

    #[test]
    fn pbblast_bvxor_2() {}

    #[test]
    fn pbblast_bvxor_8() {}

    #[test]
    fn pbblast_bvand_1() {}

    #[test]
    fn pbblast_bvand_2() {}

    #[test]
    fn pbblast_bvand_8() {}
}
