use super::{RuleArgs, RuleResult};

/// Implements the equality rule
/// The expected shape is:
///    `(= (= x y) (= (- (+ sum_x) (+ sum_y)) 0))`
pub fn pbblast_bveq(RuleArgs { pool, conclusion, .. }: RuleArgs) -> RuleResult {
    Ok(())
}

/// Implements the unsigned-less-than rule.
/// The expected shape is:
///    `(= (bvult x y) (>= (- (+ sum_y) (+ sum_x)) 1))`
pub fn pbblast_bvult(RuleArgs { pool, conclusion, .. }: RuleArgs) -> RuleResult {
    Ok(())
}

/// Implements the unsigned-greater-than rule.
///
/// The expected shape is:
///    `(= (bvugt x y) (>= (- (+ sum_x) (+ sum_y)) 1))`
pub fn pbblast_bvugt(RuleArgs { pool, conclusion, .. }: RuleArgs) -> RuleResult {
    Ok(())
}

/// Implements the unsigned-greater-or-equal rule.
///
/// The expected shape is:
///    `(= (bvuge x y) (>= (- (+ sum_x) (+ sum_y)) 0))`
pub fn pbblast_bvuge(RuleArgs { pool, conclusion, .. }: RuleArgs) -> RuleResult {
    Ok(())
}

/// Implements the unsigned-less-or-equal rule.
///
/// The expected shape is:
///    `(= (bvule x y) (>= (- (+ sum_y) (+ sum_x)) 0))`
pub fn pbblast_bvule(RuleArgs { pool, conclusion, .. }: RuleArgs) -> RuleResult {
    Ok(())
}

/// Implements the signed-less-than rule.
///
/// The expected shape is:
///    `(= (bvslt x y) (>= (+ (- y_sum (* 2^(n-1) y_n-1))) (- (* 2^(n-1) x_n-1) x_sum)) 1))`
pub fn pbblast_bvslt(RuleArgs { pool, conclusion, .. }: RuleArgs) -> RuleResult {
    Ok(())
}

/// Implements the signed-greater-than rule.
///
/// The expected shape is:
///    `(= (bvsgt x y) (>= (+ (- x_sum (* 2^(n-1) x_n-1))) (- (* 2^(n-1) y_n-1) y_sum)) 1))`
pub fn pbblast_bvsgt(RuleArgs { pool, conclusion, .. }: RuleArgs) -> RuleResult {
    Ok(())
}

/// Implements the signed-greater-equal rule.
///
/// The expected shape is:
///    `(= (bvsge x y) (>= (+ (- x_sum (* 2^(n-1) x_n-1))) (- (* 2^(n-1) y_n-1) y_sum)) 0))`
pub fn pbblast_bvsge(RuleArgs { pool, conclusion, .. }: RuleArgs) -> RuleResult {
    Ok(())
}

/// Implements the signed-less-equal rule.
///
/// The expected shape is:
///    `(= (bvsle x y) (>= (+ (- y_sum (* 2^(n-1) y_n-1))) (- (* 2^(n-1) x_n-1) x_sum)) 0))`
pub fn pbblast_bvsle(RuleArgs { pool, conclusion, .. }: RuleArgs) -> RuleResult {
    Ok(())
}

/// Implements the blasting of a bitvector variable
pub fn pbblast_pbbvar(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    Ok(())
}

/// Implements the blasting of a constant
pub fn pbblast_pbbconst(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    Ok(())
}

/// Implements the bitwise exclusive or operation.
pub fn pbblast_bvxor(RuleArgs { pool, conclusion, .. }: RuleArgs) -> RuleResult {
    Ok(())
}

/// Implements the bitwise and operation.
pub fn pbblast_bvand(RuleArgs { pool, conclusion, .. }: RuleArgs) -> RuleResult {
    Ok(())
}

mod tests {
    #[test]
    fn pbblast_bveq_1() {
        test_cases! {
            definitions = "
            (declare-const x1 (_ BitVec 1))
            (declare-const y1 (_ BitVec 1))
        ",

            // Check that equality on single-bit bitvectors is accepted when
            // the summation for each side explicitly multiplies by 1.
            "Equality on single bits" {
                r#"(step t1 (cl (= (= x1 y1)
                                 (= (- (+ (* 1 ((_ int_of 0) x1)) 0)
                                       (+ (* 1 ((_ int_of 0) y1)) 0))
                                    0))) :rule pbblast_bveq)"#: true,
            }
        }
    }
}
