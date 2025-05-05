use super::{RuleArgs, RuleResult};
use crate::{
    ast::{Rc, Sort, Term, TermPool},
    checker::error::CheckerError,
};
use rug::Integer;

/// Helper to get the bit width of a bitvector looking into the pool
fn get_bit_width(x: &Rc<Term>, pool: &mut dyn TermPool) -> Result<usize, CheckerError> {
    // Get bit width of `x`
    let Sort::BitVec(n) = pool.sort(x).as_sort().cloned().unwrap() else {
        return Err(CheckerError::Explanation(
            "Was not able to get the bitvector sort".into(),
        ));
    };
    n.to_usize().ok_or(CheckerError::Explanation(format!(
        "Failed to convert value {n} to usize"
    )))
}

// Helper to unwrap a summation list
fn get_pbsum(pbsum: &Rc<Term>) -> &[Rc<Term>] {
    if let Some(pbsum) = match_term!((+ ...) = pbsum) {
        pbsum
    } else {
        std::slice::from_ref(pbsum)
    }
}

// Helper to check that a summation has the expected shape
fn check_pbblast_sum(
    pool: &mut dyn TermPool,
    bitvector: &Rc<Term>,
    sum: &[Rc<Term>],
) -> RuleResult {
    // Obtain the bitvector width from the pool.
    let width = get_bit_width(bitvector, pool)?;

    // The summation must have at most as many summands as the bitvector has bits.
    rassert!(
        width >= sum.len(),
        CheckerError::Explanation(format!(
            "Mismatched number of summands {} and bits {}",
            width,
            sum.len()
        ))
    );

    for (i, element) in sum.iter().enumerate() {
        // Try to match (* c ((_ @int_of idx) bv))
        let (c, idx, bv) = match match_term!((* c ((_ int_of idx) bv)) = element) {
            Some((c, (idx, bv))) => (c.as_integer_err()?, idx, bv),
            None => {
                if i == 0 {
                    // For i==0, allow the coefficient to be omitted (defaulting to 1)
                    match match_term!(((_ int_of idx) bitvector) = element) {
                        Some((idx, bv)) => (Integer::from(1), idx, bv),
                        None => {
                            return Err(CheckerError::Explanation(
                                "Summand does not match either pattern".into(),
                            ));
                        }
                    }
                } else {
                    return Err(CheckerError::Explanation(
                        "Coefficient was not found and i != 0".into(),
                    ));
                }
            }
        };

        // Convert the index term to an integer.
        let idx: Integer = idx.as_integer_err()?;
        // Check that the coefficient is 2^i.
        rassert!(
            c == (Integer::from(1) << i),
            CheckerError::Explanation(format!("Coefficient {} is not 2^{}", c, i))
        );
        // Check that the index is i.
        rassert!(
            idx == i,
            CheckerError::Explanation(format!("Index {} is not {}", idx, i))
        );
        // Finally, the bitvector in the summand must be the one we expect.
        rassert!(
            *bv == *bitvector,
            CheckerError::Explanation(format!("Wrong bitvector in blasting {} {}", bv, bitvector))
        );
    }
    Ok(())
}

/// A helper that checks the two summations that occur in a pseudo–Boolean constraint.
/// Here, `left_sum` and `right_sum` come from two bitvectors `left_bv` and `right_bv` respectively.
/// (The overall constraint is something like `(>= (- (+ left_sum) (+ right_sum)) constant)`.)
fn check_pbblast_constraint(
    pool: &mut dyn TermPool,
    left_bv: &Rc<Term>,
    right_bv: &Rc<Term>,
    left_sum: &[Rc<Term>],
    right_sum: &[Rc<Term>],
) -> RuleResult {
    check_pbblast_sum(pool, left_bv, left_sum)?;
    check_pbblast_sum(pool, right_bv, right_sum)
}

/// Implements the equality rule
/// The expected shape is:
///    `(= (= x y) (= (- (+ sum_x) (+ sum_y)) 0))`
pub fn pbblast_bveq(RuleArgs { pool, conclusion, .. }: RuleArgs) -> RuleResult {
    let ((x, y), ((sum_x, sum_y), constant)) =
        match_term_err!((= (= x y) (= (- sum_x sum_y) constant)) = &conclusion[0])?;

    // Get the summation lists
    let sum_x = get_pbsum(sum_x);
    let sum_y = get_pbsum(sum_y);

    // Check that the constant is 0
    let constant: Integer = constant.as_integer_err()?;
    rassert!(
        constant == 0,
        CheckerError::Explanation(format!("Non-zero constant {}", constant))
    );

    // Check that the summations have the correct structure.
    // (For equality the order is: sum_x for x and sum_y for y.)
    check_pbblast_constraint(pool, x, y, sum_x, sum_y)
}

/// Implements the unsigned-less-than rule.
/// The expected shape is:
///    `(= (bvult x y) (>= (- (+ sum_y) (+ sum_x)) 1))`
pub fn pbblast_bvult(RuleArgs { pool, conclusion, .. }: RuleArgs) -> RuleResult {
    let ((x, y), ((sum_y, sum_x), constant)) =
        match_term_err!((= (bvult x y) (>= (- sum_y sum_x) constant)) = &conclusion[0])?;

    // Get the summation lists
    let sum_x = get_pbsum(sum_x);
    let sum_y = get_pbsum(sum_y);

    // Check that the constant is 1
    let constant: Integer = constant.as_integer_err()?;
    rassert!(
        constant == 1,
        CheckerError::Explanation(format!("Constant not 1: {}", constant))
    );

    // For bvult the summations occur in reverse: the "left" sum comes from y and the "right" from x.
    check_pbblast_constraint(pool, y, x, sum_y, sum_x)
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
pub fn pbblast_bvule(RuleArgs { pool, conclusion, .. }: RuleArgs) -> RuleResult {
    let ((x, y), ((sum_y, sum_x), ())) =
        match_term_err!((= (bvule x y) (>= (- sum_y sum_x) 0)) = &conclusion[0])?;

    // Get the summation lists
    let sum_x = get_pbsum(sum_x);
    let sum_y = get_pbsum(sum_y);

    check_pbblast_constraint(pool, x, y, sum_x, sum_y)
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
pub fn pbblast_pbbvar(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    let (x, pbs) = match_term_err!((= x (pbbterm ...)) = &conclusion[0])?;

    for (i, pb) in pbs.iter().enumerate() {
        let (idx, bv) = match_term_err!(((_ int_of idx) bv) = pb)?;

        // Convert the index term to an integer.
        let idx: Integer = idx.as_integer_err()?;

        // Check that the index is `i`.
        rassert!(
            idx == i,
            CheckerError::Explanation(format!("Index {} is not {}", idx, i))
        );
        // Finally, the bitvector in the summand must be the one we expect.
        rassert!(
            *bv == *x,
            CheckerError::Explanation(format!("Mismatched bitvectors {} {}", bv, x))
        );
    }
    Ok(())
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
                                 (= (- (* 1 ((_ @int_of 0) x1))
                                       (* 1 ((_ @int_of 0) y1)))
                                    0))) :rule pbblast_bveq)"#: true,
            }

            // Check that equality on single-bit bitvectors is accepted even when
            // the multiplication by 1 is omitted (i.e. defaulting to 1).
            "Omit multiplication by 1" {
                r#"(step t1 (cl (= (= x1 y1)
                                 (= (- ((_ @int_of 0) x1)
                                       ((_ @int_of 0) y1))
                                    0))) :rule pbblast_bveq)"#: true,
            }

            // Check that a term which is not a subtraction of sums is rejected.
            "Not a subtraction of sums" {
                r#"(step t1 (cl (= (= x1 y1)
                                 (= (* 1 ((_ @int_of 0) x1))
                                    0))) :rule pbblast_bveq)"#: false,
            }

            // Check that malformed products are rejected:
            // Case 1: the first summand uses a zero coefficient.
            "Malformed products: coefficient 0 in first summand" {
                r#"(step t1 (cl (= (= x1 y1)
                                 (= (- (* 0 ((_ @int_of 0) x1))
                                       (* 1 ((_ @int_of 0) y1)))
                                    0))) :rule pbblast_bveq)"#: false,
            }

            // Check that malformed products are rejected:
            // Case 2: the second summand uses a zero coefficient.
            "Malformed products: coefficient 0 in second summand" {
                r#"(step t1 (cl (= (= x1 y1)
                                 (= (- (* 1 ((_ @int_of 0) x1))
                                       (* 0 ((_ @int_of 0) y1)))
                                    0))) :rule pbblast_bveq)"#: false,
            }

            // In the past a trailing zero was used. This checks that
            // only the current format is allowed by the checker
            "Trailing Zero" {
                r#"(step t1 (cl (= (= x1 y1)
                                 (= (- (+ (* 1 ((_ @int_of 0) x1)) 0)
                                       (+ (* 1 ((_ @int_of 0) y1)) 0))
                                    0))) :rule pbblast_bveq)"#: false,

                r#"(step t1 (cl (= (= x1 y1)
                                 (= (- (+ ((_ @int_of 0) x1) 0)
                                       (+ ((_ @int_of 0) y1) 0))
                                    0))) :rule pbblast_bveq)"#: false,
            }


        }
    }

    #[test]
    fn pbblast_bveq_2() {
        test_cases! {
            definitions = "
            (declare-const x2 (_ BitVec 2))
            (declare-const y2 (_ BitVec 2))
        ",
            // Check equality on two-bit bitvectors, ensuring that:
            // - The most significant bit (index 1) uses a coefficient of 1,
            // - The least significant bit (index 0) uses a coefficient of 2.
            "Equality on two bits" {
                r#"(step t1 (cl (= (= x2 y2)
                                 (= (- (+ (* 1 ((_ @int_of 0) x2))
                                          (* 2 ((_ @int_of 1) x2)))
                                       (+ (* 1 ((_ @int_of 0) y2))
                                          (* 2 ((_ @int_of 1) y2))))
                                    0))) :rule pbblast_bveq)"#: true,
            }
            "Trailing Zero" {
                r#"(step t1 (cl (= (= x2 y2)
                                 (= (- (+ (* 1 ((_ @int_of 0) x2))
                                          (* 2 ((_ @int_of 1) x2)) 0)
                                       (+ (* 1 ((_ @int_of 0) y2))
                                          (* 2 ((_ @int_of 1) y2)) 0))
                                    0))) :rule pbblast_bveq)"#: false,
            }

        }
    }

    #[test]
    fn pbblast_bveq_8() {
        test_cases! {
            definitions = "
            (declare-const x8 (_ BitVec 8))
            (declare-const y8 (_ BitVec 8))
        ",
            // Check equality on eight-bit bitvectors
            "Equality on 8-bit bitvectors" {
                r#"(step t1 (cl (= (= x8 y8)
                                 (= (- (+ (* 1   ((_ @int_of 0) x8))
                                          (* 2   ((_ @int_of 1) x8))
                                          (* 4   ((_ @int_of 2) x8))
                                          (* 8   ((_ @int_of 3) x8))
                                          (* 16  ((_ @int_of 4) x8))
                                          (* 32  ((_ @int_of 5) x8))
                                          (* 64  ((_ @int_of 6) x8))
                                          (* 128 ((_ @int_of 7) x8))
                                       )
                                       (+ (* 1   ((_ @int_of 0) y8))
                                          (* 2   ((_ @int_of 1) y8))
                                          (* 4   ((_ @int_of 2) y8))
                                          (* 8   ((_ @int_of 3) y8))
                                          (* 16  ((_ @int_of 4) y8))
                                          (* 32  ((_ @int_of 5) y8))
                                          (* 64  ((_ @int_of 6) y8))
                                          (* 128 ((_ @int_of 7) y8))
                                       ))
                                0))) :rule pbblast_bveq)"#: true,
            }

            // The correct encoding is:
            // (bveq x8 y8) -> (- (sum_x8) (sum_y8)) == 0
            // We introduce a wrong coefficient (63 instead of 64).
            "bveq wrong coefficient in x8" {
                r#"(step t1 (cl (= (= x8 y8)
                                 (= (- (+ (* 1   ((_ @int_of 0) x8))
                                          (* 2   ((_ @int_of 1) x8))
                                          (* 4   ((_ @int_of 2) x8))
                                          (* 8   ((_ @int_of 3) x8))
                                          (* 16  ((_ @int_of 4) x8))
                                          (* 32  ((_ @int_of 5) x8))
                                          (* 63  ((_ @int_of 6) x8))  ; WRONG: should be (* 64 ((_ @int_of 1) x8))
                                          (* 128 ((_ @int_of 7) x8))
                                       )
                                       (+ (* 1   ((_ @int_of 0) y8))
                                          (* 2   ((_ @int_of 1) y8))
                                          (* 4   ((_ @int_of 2) y8))
                                          (* 8   ((_ @int_of 3) y8))
                                          (* 16  ((_ @int_of 4) y8))
                                          (* 32  ((_ @int_of 5) y8))
                                          (* 64  ((_ @int_of 6) y8))
                                          (* 128 ((_ @int_of 7) y8))
                                       ))
                                 0))) :rule pbblast_bveq)"#: false,
            }

            // The correct encoding is:
            // (bveq x8 y8) -> (- (sum_x8) (sum_y8)) == 0
            // We introduce a wrong constant (1 instead of 0).
            "bveq wrong constant in equality" {
                r#"(step t1 (cl (= (= x8 y8)
                                 (= (- (+ (* 1   ((_ @int_of 0) x8))
                                          (* 2   ((_ @int_of 1) x8))
                                          (* 4   ((_ @int_of 2) x8))
                                          (* 8   ((_ @int_of 3) x8))
                                          (* 16  ((_ @int_of 4) x8))
                                          (* 32  ((_ @int_of 5) x8))
                                          (* 64  ((_ @int_of 6) x8))
                                          (* 128 ((_ @int_of 7) x8))
                                       )
                                       (+ (* 1   ((_ @int_of 0) y8))
                                          (* 2   ((_ @int_of 1) y8))
                                          (* 4   ((_ @int_of 2) y8))
                                          (* 8   ((_ @int_of 3) y8))
                                          (* 16  ((_ @int_of 4) y8))
                                          (* 32  ((_ @int_of 5) y8))
                                          (* 64  ((_ @int_of 6) y8))
                                          (* 128 ((_ @int_of 7) y8))
                                       ))
                                 1) ; WRONG: should be 0
                                 )) :rule pbblast_bveq)"#: false,
            }
            "Trailing Zero" {
                r#"(step t1 (cl (= (= x8 y8)
                                 (= (- (+ (* 1   ((_ @int_of 0) x8))
                                          (* 2   ((_ @int_of 1) x8))
                                          (* 4   ((_ @int_of 2) x8))
                                          (* 8   ((_ @int_of 3) x8))
                                          (* 16  ((_ @int_of 4) x8))
                                          (* 32  ((_ @int_of 5) x8))
                                          (* 64  ((_ @int_of 6) x8))
                                          (* 128 ((_ @int_of 7) x8))
                                          0
                                       )
                                       (+ (* 1   ((_ @int_of 0) y8))
                                          (* 2   ((_ @int_of 1) y8))
                                          (* 4   ((_ @int_of 2) y8))
                                          (* 8   ((_ @int_of 3) y8))
                                          (* 16  ((_ @int_of 4) y8))
                                          (* 32  ((_ @int_of 5) y8))
                                          (* 64  ((_ @int_of 6) y8))
                                          (* 128 ((_ @int_of 7) y8))
                                          0
                                       ))
                                0))) :rule pbblast_bveq)"#: false,
            }
        }
    }

    #[test]
    fn pbblast_bvult_1() {
        test_cases! {
            definitions = "
            (declare-const x1 (_ BitVec 1))
            (declare-const y1 (_ BitVec 1))
        ",
            // A simple test on one-bit bitvectors using explicit multiplication.
            "bvult on single bits" {
                r#"(step t1 (cl (= (bvult x1 y1)
                                 (>= (- (* 1 ((_ @int_of 0) y1))
                                        (* 1 ((_ @int_of 0) x1)))
                                     1))) :rule pbblast_bvult)"#: true,
            }

            // Test where the multiplication by 1 is omitted for the only summand.
            "Omit multiplication by 1" {
                r#"(step t1 (cl (= (bvult x1 y1)
                                 (>= (- ((_ @int_of 0) y1)
                                        ((_ @int_of 0) x1))
                                     1))) :rule pbblast_bvult)"#: true,
            }

            // Test a malformed pseudo-Boolean constraint (e.g. not a subtraction of two sums).
            "Not a subtraction of sums" {
                r#"(step t1 (cl (= (bvult x1 y1)
                                 (>= (* 1 ((_ @int_of 0) y1))
                                     1))) :rule pbblast_bvult)"#: false,
            }

            // Test with malformed products: coefficient 0 is not allowed.
            "Malformed products" {
                r#"(step t1 (cl (= (bvult x1 y1)
                                 (>= (- (* 0 ((_ @int_of 0) y1))
                                        (* 1 ((_ @int_of 0) x1)))
                                     1))) :rule pbblast_bvult)"#: false,
                r#"(step t1 (cl (= (bvult x1 y1)
                                 (>= (- (* 1 ((_ @int_of 0) y1))
                                        (* 0 ((_ @int_of 0) x1)))
                                     1))) :rule pbblast_bvult)"#: false,
            }

            "Trailing Zero" {
                r#"(step t1 (cl (= (bvult x1 y1)
                                 (>= (- (+ (* 1 ((_ @int_of 0) y1)) 0)
                                        (+ (* 1 ((_ @int_of 0) x1)) 0))
                                     1))) :rule pbblast_bvult)"#: false,

                r#"(step t1 (cl (= (bvult x1 y1)
                                 (>= (- (+ ((_ @int_of 0) y1) 0)
                                        (+ ((_ @int_of 0) x1) 0))
                                     1))) :rule pbblast_bvult)"#: false,
            }


        }
    }

    #[test]
    fn pbblast_bvult_2() {
        test_cases! {
            definitions = "
            (declare-const x2 (_ BitVec 2))
            (declare-const y2 (_ BitVec 2))
        ",
            // Test on two-bit bitvectors.
            "bvult on two bits" {
                r#"(step t1 (cl (= (bvult x2 y2)
                                 (>= (- (+ (* 1 ((_ @int_of 0) y2)) (* 2 ((_ @int_of 1) y2)))
                                        (+ (* 1 ((_ @int_of 0) x2)) (* 2 ((_ @int_of 1) x2))))
                                     1))) :rule pbblast_bvult)"#: true,
            }
            "bvult mismatched index on two bits" {
                r#"(step t1 (cl (= (bvult x2 y2)
                                 (>= (- (+ (* 1 ((_ @int_of 1) y2)) (* 2 ((_ @int_of 0) y2)))
                                        (+ (* 1 ((_ @int_of 1) x2)) (* 2 ((_ @int_of 0) x2))))
                                     1))) :rule pbblast_bvult)"#: false,
            }
            "Trailing Zero" {
                r#"(step t1 (cl (= (bvult x2 y2)
                                 (>= (- (+ (* 1 ((_ @int_of 0) y2)) (* 2 ((_ @int_of 1) y2)) 0)
                                        (+ (* 1 ((_ @int_of 0) x2)) (* 2 ((_ @int_of 1) x2)) 0))
                                     1))) :rule pbblast_bvult)"#: false,
            }

        }
    }

    #[test]
    fn pbblast_bvult_8() {
        test_cases! {
            definitions = "
            (declare-const x8 (_ BitVec 8))
            (declare-const y8 (_ BitVec 8))
        ",
            // Check unsigned-less-than on eight-bit bitvectors
            "bvult on 8-bit bitvectors" {
                r#"(step t1 (cl (= (bvult x8 y8)
                                 (>= (- (+ (* 1 ((_ @int_of 0) y8))
                                           (* 2   ((_ @int_of 1) y8))
                                           (* 4   ((_ @int_of 2) y8))
                                           (* 8   ((_ @int_of 3) y8))
                                           (* 16  ((_ @int_of 4) y8))
                                           (* 32  ((_ @int_of 5) y8))
                                           (* 64  ((_ @int_of 6) y8))
                                           (* 128 ((_ @int_of 7) y8))
                                        )
                                        (+ (* 1   ((_ @int_of 0) x8))
                                           (* 2   ((_ @int_of 1) x8))
                                           (* 4   ((_ @int_of 2) x8))
                                           (* 8   ((_ @int_of 3) x8))
                                           (* 16  ((_ @int_of 4) x8))
                                           (* 32  ((_ @int_of 5) x8))
                                           (* 64  ((_ @int_of 6) x8))
                                           (* 128 ((_ @int_of 7) x8))
                                        ))
                                 1))) :rule pbblast_bvult)"#: true,
            }

            // Incorrect constant: should be 1, but here 0 is used.
            "bvult on 8-bit bitvectors (incorrect constant)" {
                r#"(step t1 (cl (= (bvult x8 y8)
                                 (>= (- (+ (* 1 ((_ @int_of 0) y8))
                                           (* 2   ((_ @int_of 1) y8))
                                           (* 4   ((_ @int_of 2) y8))
                                           (* 8   ((_ @int_of 3) y8))
                                           (* 16  ((_ @int_of 4) y8))
                                           (* 32  ((_ @int_of 5) y8))
                                           (* 64  ((_ @int_of 6) y8))
                                           (* 128 ((_ @int_of 7) y8))
                                        )
                                        (+ (* 1   ((_ @int_of 0) x8))
                                           (* 2   ((_ @int_of 1) x8))
                                           (* 4   ((_ @int_of 2) x8))
                                           (* 8   ((_ @int_of 3) x8))
                                           (* 16  ((_ @int_of 4) x8))
                                           (* 32  ((_ @int_of 5) x8))
                                           (* 64  ((_ @int_of 6) x8))
                                           (* 128 ((_ @int_of 7) x8))
                                        ))
                                 0) ; WRONG: Should be 1
                                 )) :rule pbblast_bvult)"#: false,
            }

            // For bvult the correct encoding is:
            //   (- (sum_y8) (sum_x8)) >= 1
            // Here we deliberately use 63 instead of 64 for the summand corresponding to index 1 (bit position 6).
            "bvult wrong coefficient" {
                r#"(step t1 (cl (= (bvult x8 y8)
                                 (>= (- (+ (* 1 ((_ @int_of 0) y8))
                                           (* 2   ((_ @int_of 1) y8))
                                           (* 4   ((_ @int_of 2) y8))
                                           (* 8   ((_ @int_of 3) y8))
                                           (* 16  ((_ @int_of 4) y8))
                                           (* 32  ((_ @int_of 5) y8))
                                           (* 63  ((_ @int_of 6) y8)); WRONG: should be (* 64 ((_ @int_of 1) y8))
                                           (* 128 ((_ @int_of 7) y8))
                                        )
                                        (+ (* 1   ((_ @int_of 0) x8))
                                           (* 2   ((_ @int_of 1) x8))
                                           (* 4   ((_ @int_of 2) x8))
                                           (* 8   ((_ @int_of 3) x8))
                                           (* 16  ((_ @int_of 4) x8))
                                           (* 32  ((_ @int_of 5) x8))
                                           (* 64  ((_ @int_of 6) x8))
                                           (* 128 ((_ @int_of 7) x8))
                                        ))
                                 1))) :rule pbblast_bvult)"#: false,
            }

            "Trailing Zero" {
                r#"(step t1 (cl (= (bvult x8 y8)
                                 (>= (- (+ (* 1 ((_ @int_of 0) y8))
                                           (* 2   ((_ @int_of 1) y8))
                                           (* 4   ((_ @int_of 2) y8))
                                           (* 8   ((_ @int_of 3) y8))
                                           (* 16  ((_ @int_of 4) y8))
                                           (* 32  ((_ @int_of 5) y8))
                                           (* 64  ((_ @int_of 6) y8))
                                           (* 128 ((_ @int_of 7) y8))
                                         0)
                                        (+ (* 1   ((_ @int_of 0) x8))
                                           (* 2   ((_ @int_of 1) x8))
                                           (* 4   ((_ @int_of 2) x8))
                                           (* 8   ((_ @int_of 3) x8))
                                           (* 16  ((_ @int_of 4) x8))
                                           (* 32  ((_ @int_of 5) x8))
                                           (* 64  ((_ @int_of 6) x8))
                                           (* 128 ((_ @int_of 7) x8))
                                         0))
                                 1))) :rule pbblast_bvult)"#: false,
            }


        }
    }

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
    fn pbblast_bvule_1() {
        test_cases! {
            definitions = "
            (declare-const x1 (_ BitVec 1))
            (declare-const y1 (_ BitVec 1))
        ",
            // Correct pseudo–Boolean formulation for unsigned less-or-equal on single-bit bitvectors.
            // Note the summation order is reversed compared to bvugt: the summation over y appears first.
            // Expected: (bvule x1 y1) ≈ (>= (- (+ (* 1 ((_ @int_of 0) y1)) 0)
            //                                  (+ (* 1 ((_ @int_of 0) x1)) 0))
            //                           0)
            "bvule on single bits" {
                r#"(step t1 (cl (= (bvule x1 y1)
                                 (>= (- (* 1 ((_ @int_of 0) y1))
                                        (* 1 ((_ @int_of 0) x1)))
                                     0))) :rule pbblast_bvule)"#: true,
            }

            // Accept omission of multiplication by 1.
            "Omit multiplication by 1" {
                r#"(step t1 (cl (= (bvule x1 y1)
                                 (>= (- ((_ @int_of 0) y1)
                                        ((_ @int_of 0) x1))
                                     0))) :rule pbblast_bvule)"#: true,
            }

            // Reject when the term is not a subtraction of two summations.
            "Not a subtraction of sums" {
                r#"(step t1 (cl (= (bvule x1 y1)
                                 (>= (* 1 ((_ @int_of 0) y1))
                                     0))) :rule pbblast_bvule)"#: false,
            }

            // Reject malformed product in the first summand.
            "Malformed products: coefficient 0 in first summand" {
                r#"(step t1 (cl (= (bvule x1 y1)
                                 (>= (- (* 0 ((_ @int_of 0) y1))
                                        (* 1 ((_ @int_of 0) x1)))
                                     0))) :rule pbblast_bvule)"#: false,
            }

            // Reject malformed product in the second summand.
            "Malformed products: coefficient 0 in second summand" {
                r#"(step t1 (cl (= (bvule x1 y1)
                                 (>= (- (* 1 ((_ @int_of 0) y1))
                                        (* 0 ((_ @int_of 0) x1)))
                                     0))) :rule pbblast_bvule)"#: false,
            }

            "Trailing Zero" {
                r#"(step t1 (cl (= (bvule x1 y1)
                                 (>= (- (+ (* 1 ((_ @int_of 0) y1)) 0)
                                        (+ (* 1 ((_ @int_of 0) x1)) 0))
                                     0))) :rule pbblast_bvule)"#: false,

                r#"(step t1 (cl (= (bvule x1 y1)
                                 (>= (- (+ ((_ @int_of 0) y1) 0)
                                        (+ ((_ @int_of 0) x1) 0))
                                     0))) :rule pbblast_bvule)"#: false,
            }


        }
    }

    #[test]
    fn pbblast_bvule_2() {
        test_cases! {
            definitions = "
            (declare-const x2 (_ BitVec 2))
            (declare-const y2 (_ BitVec 2))
        ",
            // Correct formulation for two-bit bitvectors.
            "bvule on two bits" {
                r#"(step t1 (cl (= (bvule x2 y2)
                                 (>= (- (+ (* 1 ((_ @int_of 0) y2)) (* 2 ((_ @int_of 1) y2)))
                                        (+ (* 1 ((_ @int_of 0) x2)) (* 2 ((_ @int_of 1) x2))))
                                     0))) :rule pbblast_bvule)"#: true,
            }
            "bvule mismatched indices on two bits" {
                r#"(step t1 (cl (= (bvule x2 y2)
                                 (>= (- (+ (* 1 ((_ @int_of 1) y2)) (* 2 ((_ @int_of 0) y2)))
                                        (+ (* 1 ((_ @int_of 1) x2)) (* 2 ((_ @int_of 0) x2))))
                                     0))) :rule pbblast_bvule)"#: false,
            }
            "Trailing Zero" {
                r#"(step t1 (cl (= (bvule x2 y2)
                                 (>= (- (+ (* 1 ((_ @int_of 0) y2)) (* 2 ((_ @int_of 1) y2)) 0)
                                        (+ (* 1 ((_ @int_of 0) x2)) (* 2 ((_ @int_of 1) x2)) 0))
                                     0))) :rule pbblast_bvule)"#: false,
            }

        }
    }

    #[test]
    fn pbblast_bvule_8() {
        test_cases! {
            definitions = "
            (declare-const x8 (_ BitVec 8))
            (declare-const y8 (_ BitVec 8))
        ",
            // Check unsigned-less-equal on eight-bit bitvectors
            "bvule on 8-bit bitvectors" {
                r#"(step t1 (cl (= (bvule x8 y8)
                                 (>= (- (+ (* 1   ((_ @int_of 0) y8))
                                           (* 2   ((_ @int_of 1) y8))
                                           (* 4   ((_ @int_of 2) y8))
                                           (* 8   ((_ @int_of 3) y8))
                                           (* 16  ((_ @int_of 4) y8))
                                           (* 32  ((_ @int_of 5) y8))
                                           (* 64  ((_ @int_of 6) y8))
                                           (* 128 ((_ @int_of 7) y8)))
                                        (+ (* 1   ((_ @int_of 0) x8))
                                           (* 2   ((_ @int_of 1) x8))
                                           (* 4   ((_ @int_of 2) x8))
                                           (* 8   ((_ @int_of 3) x8))
                                           (* 16  ((_ @int_of 4) x8))
                                           (* 32  ((_ @int_of 5) x8))
                                           (* 64  ((_ @int_of 6) x8))
                                           (* 128 ((_ @int_of 7) x8))))
                                 0))) :rule pbblast_bvule)"#: true,
            }

            // Incorrect constant: should be 0, but here 1 is used.
            "bvule on 8-bit bitvectors (incorrect constant)" {
                r#"(step t1 (cl (= (bvule x8 y8)
                                 (>= (- (+ (* 1   ((_ @int_of 0) y8))
                                           (* 2   ((_ @int_of 1) y8))
                                           (* 4   ((_ @int_of 2) y8))
                                           (* 8   ((_ @int_of 3) y8))
                                           (* 16  ((_ @int_of 4) y8))
                                           (* 32  ((_ @int_of 5) y8))
                                           (* 64  ((_ @int_of 6) y8))
                                           (* 128 ((_ @int_of 7) y8)))
                                        (+ (* 1   ((_ @int_of 0) x8))
                                           (* 2   ((_ @int_of 1) x8))
                                           (* 4   ((_ @int_of 2) x8))
                                           (* 8   ((_ @int_of 3) x8))
                                           (* 16  ((_ @int_of 4) x8))
                                           (* 32  ((_ @int_of 5) x8))
                                           (* 64  ((_ @int_of 6) x8))
                                           (* 128 ((_ @int_of 7) x8))))
                                 1) ; WRONG: Should be 0
                                )) :rule pbblast_bvule)"#: false,
            }

            // For bvule the correct encoding is:
            //   (- (sum_y8) (sum_x8)) >= 0
            // Here we deliberately use 63 instead of 64 for one of the summands in y8.
            "bvule wrong coefficient" {
                r#"(step t1 (cl (= (bvule x8 y8)
                                 (>= (- (+ (* 1   ((_ @int_of 0) y8))
                                           (* 2   ((_ @int_of 1) y8))
                                           (* 4   ((_ @int_of 2) y8))
                                           (* 8   ((_ @int_of 3) y8))
                                           (* 16  ((_ @int_of 4) y8))
                                           (* 32  ((_ @int_of 5) y8))
                                           (* 63  ((_ @int_of 6) y8))    ; WRONG: should be (* 64 ((_ @int_of 1) y8))
                                           (* 128 ((_ @int_of 7) y8)))
                                        (+ (* 1   ((_ @int_of 0) x8))
                                           (* 2   ((_ @int_of 1) x8))
                                           (* 4   ((_ @int_of 2) x8))
                                           (* 8   ((_ @int_of 3) x8))
                                           (* 16  ((_ @int_of 4) x8))
                                           (* 32  ((_ @int_of 5) x8))
                                           (* 64  ((_ @int_of 6) x8))
                                           (* 128 ((_ @int_of 7) x8))))
                                 0))) :rule pbblast_bvule)"#: false,
            }

            "Trailing Zero" {
                r#"(step t1 (cl (= (bvule x8 y8)
                                 (>= (- (+ (* 1   ((_ @int_of 0) y8))
                                           (* 2   ((_ @int_of 1) y8))
                                           (* 4   ((_ @int_of 2) y8))
                                           (* 8   ((_ @int_of 3) y8))
                                           (* 16  ((_ @int_of 4) y8))
                                           (* 32  ((_ @int_of 5) y8))
                                           (* 64  ((_ @int_of 6) y8))
                                           (* 128 ((_ @int_of 7) y8))
                                         0)
                                        (+ (* 1   ((_ @int_of 0) x8))
                                           (* 2   ((_ @int_of 1) x8))
                                           (* 4   ((_ @int_of 2) x8))
                                           (* 8   ((_ @int_of 3) x8))
                                           (* 16  ((_ @int_of 4) x8))
                                           (* 32  ((_ @int_of 5) x8))
                                           (* 64  ((_ @int_of 6) x8))
                                           (* 128 ((_ @int_of 7) x8))
                                         0))
                                 0))) :rule pbblast_bvule)"#: false,
            }
        }
    }

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
    fn pbblast_pbbvar_1() {
        test_cases! {
           definitions = "
                (declare-const x (_ BitVec 1))
                (declare-const y (_ BitVec 1))
                ",
            // No restriction, only create a vector of pseudo-boolean variables that are free
            "pbbvar on single bits" {
                r#"(step t1 (cl (= x (@pbbterm ((_ @int_of 0) x)))) :rule pbblast_pbbvar)"#: true,
                r#"(step t1 (cl (= x (@pbbterm ((_ @int_of 1) x)))) :rule pbblast_pbbvar)"#: false, // Wrong index
                r#"(step t1 (cl (= x (@pbbterm ((_ @int_of 0) y)))) :rule pbblast_pbbvar)"#: false, // Mismatched vectors
                r#"(step t1 (cl (= y (@pbbterm ((_ @int_of 0) x)))) :rule pbblast_pbbvar)"#: false, // Mismatched vectors
            }
        }
    }

    #[test]
    fn pbblast_pbbvar_2() {
        test_cases! {
            definitions = "
            (declare-const x2 (_ BitVec 2))
            (declare-const y2 (_ BitVec 2))
        ",
            "Valid 2-bit pbbvar" {
                r#"(step t1 (cl (= x2 (@pbbterm ((_ @int_of 0) x2) ((_ @int_of 1) x2)))) :rule pbblast_pbbvar)"#: true,
            }
            "Mixed variables" {
                r#"(step t1 (cl (= x2 (@pbbterm ((_ @int_of 0) x2) ((_ @int_of 1) y2)))) :rule pbblast_pbbvar)"#: false,
            }
        }
    }

    #[test]
    fn pbblast_pbbvar_8() {
        test_cases! {
            definitions = "
            (declare-const x8 (_ BitVec 8))
        ",
            "Valid 8-bit pbbvar" {
                r#"(step t1 (cl (= x8 (@pbbterm
                    ((_ @int_of 0) x8) ((_ @int_of 1) x8)
                    ((_ @int_of 2) x8) ((_ @int_of 3) x8)
                    ((_ @int_of 4) x8) ((_ @int_of 5) x8)
                    ((_ @int_of 6) x8) ((_ @int_of 7) x8)
                ))) :rule pbblast_pbbvar)"#: true,
            }

            "Invalid 8-bit (missing term)" {
                r#"(step t1 (cl (= x8 (@pbbterm
                    ((_ @int_of 0) x8) ((_ @int_of 1) x8)
                    ((_ @int_of 2) x8) ((_ @int_of 3) x8)
                    ((_ @int_of 4) x8) ((_ @int_of 5) x8)
                    ((_ @int_of 6) x8) ((_ @int_of 6) x8) ;; index 6 twice
                ))) :rule pbblast_pbbvar)"#: false,
            }
        }
    }

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
