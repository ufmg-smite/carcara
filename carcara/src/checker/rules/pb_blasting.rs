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
    let ((x, y), ((sum_x, sum_y), _)) =
        match_term_err!((= (= x y) (= (- sum_x sum_y) 0)) = &conclusion[0])?;

    // Get the summation lists
    let sum_x = get_pbsum(sum_x);
    let sum_y = get_pbsum(sum_y);

    // Check that the summations have the correct structure.
    // (For equality the order is: sum_x for x and sum_y for y.)
    check_pbblast_constraint(pool, x, y, sum_x, sum_y)
}

/// Implements the unsigned-less-than rule.
/// The expected shape is:
///    `(= (bvult x y) (>= (- (+ sum_y) (+ sum_x)) 1))`
pub fn pbblast_bvult(RuleArgs { pool, conclusion, .. }: RuleArgs) -> RuleResult {
    let ((x, y), ((sum_y, sum_x), _)) =
        match_term_err!((= (bvult x y) (>= (- sum_y sum_x) 1)) = &conclusion[0])?;

    // Get the summation lists
    let sum_x = get_pbsum(sum_x);
    let sum_y = get_pbsum(sum_y);

    // For bvult the summations occur in reverse: the "left" sum comes from y and the "right" from x.
    check_pbblast_constraint(pool, y, x, sum_y, sum_x)
}

/// Implements the unsigned-greater-than rule.
///
/// The expected shape is:
///    `(= (bvugt x y) (>= (- (+ sum_x) (+ sum_y)) 1))`
pub fn pbblast_bvugt(RuleArgs { pool, conclusion, .. }: RuleArgs) -> RuleResult {
    let ((x, y), ((sum_x, sum_y), _)) =
        match_term_err!((= (bvugt x y) (>= (- sum_x sum_y) 1)) = &conclusion[0])?;

    // Get the summation lists
    let sum_x = get_pbsum(sum_x);
    let sum_y = get_pbsum(sum_y);

    // For bvugt the summations appear in the same order as in equality.
    check_pbblast_constraint(pool, x, y, sum_x, sum_y)
}

/// Implements the unsigned-greater-or-equal rule.
///
/// The expected shape is:
///    `(= (bvuge x y) (>= (- (+ sum_x) (+ sum_y)) 0))`
pub fn pbblast_bvuge(RuleArgs { pool, conclusion, .. }: RuleArgs) -> RuleResult {
    let ((x, y), ((sum_x, sum_y), ())) =
        match_term_err!((= (bvuge x y) (>= (- sum_x sum_y) 0)) = &conclusion[0])?;

    // Get the summation lists
    let sum_x = get_pbsum(sum_x);
    let sum_y = get_pbsum(sum_y);

    check_pbblast_constraint(pool, x, y, sum_x, sum_y)
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

/// Helper that checks the the `sign` term has the format -(2<sup>n-1</sup>) x<sub>n-1</sub>
fn check_pbblast_signed_relation(n: usize, sign: &Rc<Term>, bitvector: &Rc<Term>) -> RuleResult {
    // Check the signs
    let (coeff, (idx, bv)) = match_term_err!((* coeff ((_ int_of idx) bv)) = sign)?;
    let coeff = coeff.as_integer_err()?;
    let idx = idx.as_integer_err()?;

    // Check that the coefficient is 2^(n-1)
    rassert!(
        coeff == (Integer::from(1) << (n - 1)), // 2^(n-1)
        CheckerError::Explanation(format!("Expected coefficient 2^{} got {coeff}", (n - 1)))
    );

    // Check that the index is n-1.
    rassert!(
        idx == n - 1,
        CheckerError::Explanation(format!("Index {} is not {}", idx, n - 1))
    );

    // Finally, the bitvector in the term must be the one we expect.
    rassert!(
        *bv == *bitvector,
        CheckerError::Explanation(format!("Wrong bitvector in sign bit {} {}", bv, bitvector))
    );

    Ok(())
}

/// Implements the signed-less-than rule.
///
/// The expected shape is:
///    `(= (bvslt x y) (>= (+ (- y_sum (* 2^(n-1) y_n-1))) (- (* 2^(n-1) x_n-1) x_sum)) 1))`
pub fn pbblast_bvslt(RuleArgs { pool, conclusion, .. }: RuleArgs) -> RuleResult {
    let ((x, y), (((sum_y, sign_y), (sign_x, sum_x)), _)) = match_term_err!((= (bvslt x y) (>= (+ (- sum_y sign_y) (- sign_x sum_x)) 1)) = &conclusion[0])?;

    // Get the summation lists
    let sum_x = get_pbsum(sum_x);
    let sum_y = get_pbsum(sum_y);

    let n = get_bit_width(x, pool)?;

    // Check the sign terms
    check_pbblast_signed_relation(n, sign_y, y)?;
    check_pbblast_signed_relation(n, sign_x, x)?;

    // For bvult the summations occur in reverse: the "left" sum comes from y and the "right" from x.
    check_pbblast_constraint(pool, y, x, sum_y, sum_x)
}

/// Implements the signed-greater-than rule.
///
/// The expected shape is:
///    `(= (bvsgt x y) (>= (+ (- x_sum (* 2^(n-1) x_n-1))) (- (* 2^(n-1) y_n-1) y_sum)) 1))`
pub fn pbblast_bvsgt(RuleArgs { pool, conclusion, .. }: RuleArgs) -> RuleResult {
    let ((x, y), (((sum_x, sign_x), (sign_y, sum_y)), _)) = match_term_err!((= (bvsgt x y) (>= (+ (- sum_x sign_x) (- sign_y sum_y)) 1)) = &conclusion[0])?;

    // Get the summation lists
    let sum_x = get_pbsum(sum_x);
    let sum_y = get_pbsum(sum_y);

    // Get bit width of `x`
    let n = get_bit_width(x, pool)?;

    // Check the sign terms
    check_pbblast_signed_relation(n, sign_x, x)?;
    check_pbblast_signed_relation(n, sign_y, y)?;

    check_pbblast_constraint(pool, x, y, sum_x, sum_y)
}

/// Implements the signed-greater-equal rule.
///
/// The expected shape is:
///    `(= (bvsge x y) (>= (+ (- x_sum (* 2^(n-1) x_n-1))) (- (* 2^(n-1) y_n-1) y_sum)) 0))`
pub fn pbblast_bvsge(RuleArgs { pool, conclusion, .. }: RuleArgs) -> RuleResult {
    let ((x, y), (((sum_x, sign_x), (sign_y, sum_y)), _)) = match_term_err!((= (bvsge x y) (>= (+ (- sum_x sign_x) (- sign_y sum_y)) 0)) = &conclusion[0])?;

    // Get the summation lists
    let sum_x = get_pbsum(sum_x);
    let sum_y = get_pbsum(sum_y);

    // Get bit width of `x`
    let n = get_bit_width(x, pool)?;

    // Check the sign terms
    check_pbblast_signed_relation(n, sign_x, x)?;
    check_pbblast_signed_relation(n, sign_y, y)?;

    check_pbblast_constraint(pool, x, y, sum_x, sum_y)
}

/// Implements the signed-less-equal rule.
///
/// The expected shape is:
///    `(= (bvsle x y) (>= (+ (- y_sum (* 2^(n-1) y_n-1))) (- (* 2^(n-1) x_n-1) x_sum)) 0))`
pub fn pbblast_bvsle(RuleArgs { pool, conclusion, .. }: RuleArgs) -> RuleResult {
    let ((x, y), (((sum_y, sign_y), (sign_x, sum_x)), _)) = match_term_err!((= (bvsle x y) (>= (+ (- sum_y sign_y) (- sign_x sum_x)) 0)) = &conclusion[0])?;

    // Get the summation lists
    let sum_x = get_pbsum(sum_x);
    let sum_y = get_pbsum(sum_y);

    // Get bit width of `x`
    let n = get_bit_width(x, pool)?;

    // Check the sign terms
    check_pbblast_signed_relation(n, sign_y, y)?;
    check_pbblast_signed_relation(n, sign_x, x)?;

    // For bvsle the summations occur in reverse: the "left" sum comes from y and the "right" from x.
    check_pbblast_constraint(pool, y, x, sum_y, sum_x)
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
pub fn pbblast_pbbconst(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    let (bv, pbs) = match_term_err!((= bv (pbbterm ...)) = &conclusion[0])
        .map_err(|_| CheckerError::Explanation("Malformed @pbbterm equality".into()))?;

    let (m, w) = bv.as_bitvector().ok_or(CheckerError::Explanation(
        "Expected bitvector constant".into(),
    ))?;

    let size = w
        .to_usize()
        .ok_or(CheckerError::Explanation("Invalid bitvector width".into()))?;

    if pbs.len() != size {
        return Err(CheckerError::Explanation(format!(
            "Expected {} @pbbterms, got {}",
            size,
            pbs.len()
        )));
    }

    let computed_value = pbs
        .iter()
        .enumerate()
        .try_fold(Integer::new(), |acc, (i, term)| {
            let pb = term
                .as_integer()
                .ok_or(CheckerError::Explanation(format!(
                    "Non-integer term at position {}",
                    i
                )))?
                .to_i32_wrapping();

            match pb {
                0 => Ok(acc),
                1 => {
                    let exponent = i.try_into().unwrap();
                    let increment = Integer::i_pow_u(2, exponent);
                    Ok(&acc + Integer::from(increment))
                }
                _ => Err(CheckerError::Explanation(format!(
                    "Invalid value {} at position {}",
                    pb, i
                ))),
            }
        })?;

    if computed_value != m {
        return Err(CheckerError::Explanation(format!(
            "Computed value {} != declared value {}",
            computed_value, m
        )));
    }

    Ok(())
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
    fn pbblast_bvugt_1() {
        test_cases! {
            definitions = "
            (declare-const x1 (_ BitVec 1))
            (declare-const y1 (_ BitVec 1))
        ",

            // Correct pseudo–Boolean formulation for unsigned greater-than on single-bit bitvectors.
            // Expected: (bvugt x1 y1) ≈ (>= (- (+ (* 1 ((_ @int_of 0) x1)) 0)
            //                                  (+ (* 1 ((_ @int_of 0) y1)) 0))
            //                           1)
            "bvugt on single bits" {
                r#"(step t1 (cl (= (bvugt x1 y1)
                                 (>= (- (* 1 ((_ @int_of 0) x1))
                                        (* 1 ((_ @int_of 0) y1)))
                                     1))) :rule pbblast_bvugt)"#: true,
            }

            // Accept omission of multiplication by 1 for the only summand.
            "Omit multiplication by 1" {
                r#"(step t1 (cl (= (bvugt x1 y1)
                                 (>= (- ((_ @int_of 0) x1)
                                        ((_ @int_of 0) y1))
                                     1))) :rule pbblast_bvugt)"#: true,
            }

            // Reject when the term is not a subtraction of two summations.
            "Not a subtraction of sums" {
                r#"(step t1 (cl (= (bvugt x1 y1)
                                 (>= (* 1 ((_ @int_of 0) x1))
                                     1))) :rule pbblast_bvugt)"#: false,
            }

            // Reject malformed product in the first summand (coefficient 0 instead of 1).
            "Malformed products: coefficient 0 in first summand" {
                r#"(step t1 (cl (= (bvugt x1 y1)
                                 (>= (- (* 0 ((_ @int_of 0) x1))
                                        (* 1 ((_ @int_of 0) y1)))
                                     1))) :rule pbblast_bvugt)"#: false,
            }

            // Reject malformed product in the second summand (coefficient 0 instead of 1).
            "Malformed products: coefficient 0 in second summand" {
                r#"(step t1 (cl (= (bvugt x1 y1)
                                 (>= (- (* 1 ((_ @int_of 0) x1))
                                        (* 0 ((_ @int_of 0) y1)))
                                     1))) :rule pbblast_bvugt)"#: false,
            }

            "Trailing Zero" {
                r#"(step t1 (cl (= (bvugt x1 y1)
                                 (>= (- (+ (* 1 ((_ @int_of 0) x1)) 0)
                                        (+ (* 1 ((_ @int_of 0) y1)) 0))
                                     1))) :rule pbblast_bvugt)"#: false,
                r#"(step t1 (cl (= (bvugt x1 y1)
                                 (>= (- (+ ((_ @int_of 0) x1) 0)
                                        (+ ((_ @int_of 0) y1) 0))
                                     1))) :rule pbblast_bvugt)"#: false,
            }


        }
    }

    #[test]
    fn pbblast_bvugt_2() {
        test_cases! {
            definitions = "
            (declare-const x2 (_ BitVec 2))
            (declare-const y2 (_ BitVec 2))
        ",
            // Correct formulation for two-bit bitvectors.
            // Expected summands for x2: most-significant bit uses coefficient 1, least-significant uses coefficient 2.
            "bvugt on two bits" {
                r#"(step t1 (cl (= (bvugt x2 y2)
                                 (>= (- (+ (* 1 ((_ @int_of 0) x2)) (* 2 ((_ @int_of 1) x2)))
                                        (+ (* 1 ((_ @int_of 0) y2)) (* 2 ((_ @int_of 1) y2))))
                                     1))) :rule pbblast_bvugt)"#: true,
            }
            "bvugt mismatched indices on two bits" {
                r#"(step t1 (cl (= (bvugt x2 y2)
                                 (>= (- (+ (* 1 ((_ @int_of 1) x2)) (* 2 ((_ @int_of 0) x2)))
                                        (+ (* 1 ((_ @int_of 1) y2)) (* 2 ((_ @int_of 0) y2))))
                                     1))) :rule pbblast_bvugt)"#: false,
            }
            "Trailing Zero" {
                r#"(step t1 (cl (= (bvugt x2 y2)
                                 (>= (- (+ (* 1 ((_ @int_of 0) x2)) (* 2 ((_ @int_of 1) x2)) 0)
                                        (+ (* 1 ((_ @int_of 0) y2)) (* 2 ((_ @int_of 1) y2)) 0))
                                     1))) :rule pbblast_bvugt)"#: false,
            }

        }
    }

    #[test]
    fn pbblast_bvugt_8() {
        test_cases! {
            definitions = "
            (declare-const x8 (_ BitVec 8))
            (declare-const y8 (_ BitVec 8))
        ",
            // Check unsigned-greater-than on eight-bit bitvectors
            "bvugt on 8-bit bitvectors" {
                r#"(step t1 (cl (= (bvugt x8 y8)
                                 (>= (- (+ (* 1   ((_ @int_of 0) x8))
                                           (* 2   ((_ @int_of 1) x8))
                                           (* 4   ((_ @int_of 2) x8))
                                           (* 8   ((_ @int_of 3) x8))
                                           (* 16  ((_ @int_of 4) x8))
                                           (* 32  ((_ @int_of 5) x8))
                                           (* 64  ((_ @int_of 6) x8))
                                           (* 128 ((_ @int_of 7) x8)))
                                        (+ (* 1   ((_ @int_of 0) y8))
                                           (* 2   ((_ @int_of 1) y8))
                                           (* 4   ((_ @int_of 2) y8))
                                           (* 8   ((_ @int_of 3) y8))
                                           (* 16  ((_ @int_of 4) y8))
                                           (* 32  ((_ @int_of 5) y8))
                                           (* 64  ((_ @int_of 6) y8))
                                           (* 128 ((_ @int_of 7) y8))))
                                 1))) :rule pbblast_bvugt)"#: true,
            }

            // Incorrect constant: should be 1, but here 0 is used.
            "bvugt on 8-bit bitvectors (incorrect constant)" {
                r#"(step t1 (cl (= (bvugt x8 y8)
                                 (>= (- (+ (* 1   ((_ @int_of 0) x8))
                                           (* 2   ((_ @int_of 1) x8))
                                           (* 4   ((_ @int_of 2) x8))
                                           (* 8   ((_ @int_of 3) x8))
                                           (* 16  ((_ @int_of 4) x8))
                                           (* 32  ((_ @int_of 5) x8))
                                           (* 64  ((_ @int_of 6) x8))
                                           (* 128 ((_ @int_of 7) x8)))
                                        (+ (* 1   ((_ @int_of 0) y8))
                                           (* 2   ((_ @int_of 1) y8))
                                           (* 4   ((_ @int_of 2) y8))
                                           (* 8   ((_ @int_of 3) y8))
                                           (* 16  ((_ @int_of 4) y8))
                                           (* 32  ((_ @int_of 5) y8))
                                           (* 64  ((_ @int_of 6) y8))
                                           (* 128 ((_ @int_of 7) y8))))
                                 0) ; WRONG: Should be 1
                                )) :rule pbblast_bvugt)"#: false,
            }

            // For bvugt the correct encoding is:
            //   (- (sum_x8) (sum_y8)) >= 1
            // Here we deliberately use 63 instead of 64 for the summand corresponding to index 1 in x8.
            "bvugt on 8-bit bitvectors wrong coefficient" {
                r#"(step t1 (cl (= (bvugt x8 y8)
                                 (>= (- (+ (* 1   ((_ @int_of 0) x8))
                                           (* 2   ((_ @int_of 1) x8))
                                           (* 4   ((_ @int_of 2) x8))
                                           (* 8   ((_ @int_of 3) x8))
                                           (* 16  ((_ @int_of 4) x8))
                                           (* 32  ((_ @int_of 5) x8))
                                           (* 63  ((_ @int_of 6) x8))    ; WRONG: should be (* 64 ((_ @int_of 1) x8))
                                           (* 128 ((_ @int_of 7) x8)))
                                        (+ (* 1   ((_ @int_of 0) y8))
                                           (* 2   ((_ @int_of 1) y8))
                                           (* 4   ((_ @int_of 2) y8))
                                           (* 8   ((_ @int_of 3) y8))
                                           (* 16  ((_ @int_of 4) y8))
                                           (* 32  ((_ @int_of 5) y8))
                                           (* 64  ((_ @int_of 6) y8))
                                           (* 128 ((_ @int_of 7) y8))))
                                 1))) :rule pbblast_bvugt)"#: false,
            }

            "Trailing Zero" {
                r#"(step t1 (cl (= (bvugt x8 y8)
                                 (>= (- (+ (* 1   ((_ @int_of 0) x8))
                                           (* 2   ((_ @int_of 1) x8))
                                           (* 4   ((_ @int_of 2) x8))
                                           (* 8   ((_ @int_of 3) x8))
                                           (* 16  ((_ @int_of 4) x8))
                                           (* 32  ((_ @int_of 5) x8))
                                           (* 64  ((_ @int_of 6) x8))
                                           (* 128 ((_ @int_of 7) x8))
                                         0)
                                        (+ (* 1   ((_ @int_of 0) y8))
                                           (* 2   ((_ @int_of 1) y8))
                                           (* 4   ((_ @int_of 2) y8))
                                           (* 8   ((_ @int_of 3) y8))
                                           (* 16  ((_ @int_of 4) y8))
                                           (* 32  ((_ @int_of 5) y8))
                                           (* 64  ((_ @int_of 6) y8))
                                           (* 128 ((_ @int_of 7) y8))
                                         0))
                                 1))) :rule pbblast_bvugt)"#: false,
            }

        }
    }

    #[test]
    fn pbblast_bvuge_1() {
        test_cases! {
            definitions = "
            (declare-const x1 (_ BitVec 1))
            (declare-const y1 (_ BitVec 1))
        ",

            // Correct pseudo–Boolean formulation for unsigned greater-or-equal on single-bit bitvectors.
            // Expected: (bvuge x1 y1) ≈ (>= (- (+ (* 1 ((_ @int_of 0) x1)) 0)
            //                                  (+ (* 1 ((_ @int_of 0) y1)) 0))
            //                           0)
            "bvuge on single bits" {
                r#"(step t1 (cl (= (bvuge x1 y1)
                                 (>= (- (* 1 ((_ @int_of 0) x1))
                                        (* 1 ((_ @int_of 0) y1)))
                                     0))) :rule pbblast_bvuge)"#: true,
            }

            // Accept omission of multiplication by 1.
            "Omit multiplication by 1" {
                r#"(step t1 (cl (= (bvuge x1 y1)
                                 (>= (- ((_ @int_of 0) x1)
                                        ((_ @int_of 0) y1))
                                     0))) :rule pbblast_bvuge)"#: true,
            }

            // Reject when the expression is not a subtraction of two summations.
            "Not a subtraction of sums" {
                r#"(step t1 (cl (= (bvuge x1 y1)
                                 (>= (* 1 ((_ @int_of 0) x1))
                                     0))) :rule pbblast_bvuge)"#: false,
            }

            // Reject malformed product in the first summand.
            "Malformed products: coefficient 0 in first summand" {
                r#"(step t1 (cl (= (bvuge x1 y1)
                                 (>= (- (* 0 ((_ @int_of 0) x1))
                                        (* 1 ((_ @int_of 0) y1)))
                                     0))) :rule pbblast_bvuge)"#: false,
            }

            // Reject malformed product in the second summand.
            "Malformed products: coefficient 0 in second summand" {
                r#"(step t1 (cl (= (bvuge x1 y1)
                                 (>= (- (* 1 ((_ @int_of 0) x1))
                                        (* 0 ((_ @int_of 0) y1)))
                                     0))) :rule pbblast_bvuge)"#: false,
            }
            "Trailing Zero" {
                r#"(step t1 (cl (= (bvuge x1 y1)
                                 (>= (- (+ (* 1 ((_ @int_of 0) x1)) 0)
                                        (+ (* 1 ((_ @int_of 0) y1)) 0))
                                     0))) :rule pbblast_bvuge)"#: false,
                r#"(step t1 (cl (= (bvuge x1 y1)
                                 (>= (- (+ ((_ @int_of 0) x1) 0)
                                        (+ ((_ @int_of 0) y1) 0))
                                     0))) :rule pbblast_bvuge)"#: false,
            }


        }
    }

    #[test]
    fn pbblast_bvuge_2() {
        test_cases! {
            definitions = "
            (declare-const x2 (_ BitVec 2))
            (declare-const y2 (_ BitVec 2))
        ",
            // Correct formulation for two-bit bitvectors.
            "bvuge on two bits" {
                r#"(step t1 (cl (= (bvuge x2 y2)
                                 (>= (- (+ (* 1 ((_ @int_of 0) x2)) (* 2 ((_ @int_of 1) x2)))
                                        (+ (* 1 ((_ @int_of 0) y2)) (* 2 ((_ @int_of 1) y2))))
                                     0))) :rule pbblast_bvuge)"#: true,
            }
            "bvuge mismatched indices on two bits" {
                r#"(step t1 (cl (= (bvuge x2 y2)
                                 (>= (- (+ (* 1 ((_ @int_of 1) x2)) (* 2 ((_ @int_of 0) x2)))
                                        (+ (* 1 ((_ @int_of 1) y2)) (* 2 ((_ @int_of 0) y2))))
                                     0))) :rule pbblast_bvuge)"#: false,
            }
            "Trailing Zero" {
                r#"(step t1 (cl (= (bvuge x2 y2)
                                 (>= (- (+ (* 1 ((_ @int_of 0) x2)) (* 2 ((_ @int_of 1) x2)) 0)
                                        (+ (* 1 ((_ @int_of 0) y2)) (* 2 ((_ @int_of 1) y2)) 0))
                                     0))) :rule pbblast_bvuge)"#: false,
            }
        }
    }

    #[test]
    fn pbblast_bvuge_8() {
        test_cases! {
            definitions = "
            (declare-const x8 (_ BitVec 8))
            (declare-const y8 (_ BitVec 8))
        ",
            // Check unsigned-greater-equal on eight-bit bitvectors
            "bvuge on 8-bit bitvectors" {
                r#"(step t1 (cl (= (bvuge x8 y8)
                                 (>= (- (+ (* 1   ((_ @int_of 0) x8))
                                           (* 2   ((_ @int_of 1) x8))
                                           (* 4   ((_ @int_of 2) x8))
                                           (* 8   ((_ @int_of 3) x8))
                                           (* 16  ((_ @int_of 4) x8))
                                           (* 32  ((_ @int_of 5) x8))
                                           (* 64  ((_ @int_of 6) x8))
                                           (* 128 ((_ @int_of 7) x8)))
                                        (+ (* 1   ((_ @int_of 0) y8))
                                           (* 2   ((_ @int_of 1) y8))
                                           (* 4   ((_ @int_of 2) y8))
                                           (* 8   ((_ @int_of 3) y8))
                                           (* 16  ((_ @int_of 4) y8))
                                           (* 32  ((_ @int_of 5) y8))
                                           (* 64  ((_ @int_of 6) y8))
                                           (* 128 ((_ @int_of 7) y8))))
                                 0))) :rule pbblast_bvuge)"#: true,
            }

            // Incorrect constant: should be 0, but here 1 is used.
            "bvuge on 8-bit bitvectors (incorrect constant)" {
                r#"(step t1 (cl (= (bvuge x8 y8)
                                 (>= (- (+ (* 1   ((_ @int_of 0) x8))
                                           (* 2   ((_ @int_of 1) x8))
                                           (* 4   ((_ @int_of 2) x8))
                                           (* 8   ((_ @int_of 3) x8))
                                           (* 16  ((_ @int_of 4) x8))
                                           (* 32  ((_ @int_of 5) x8))
                                           (* 64  ((_ @int_of 6) x8))
                                           (* 128 ((_ @int_of 7) x8)))
                                        (+ (* 1   ((_ @int_of 0) y8))
                                           (* 2   ((_ @int_of 1) y8))
                                           (* 4   ((_ @int_of 2) y8))
                                           (* 8   ((_ @int_of 3) y8))
                                           (* 16  ((_ @int_of 4) y8))
                                           (* 32  ((_ @int_of 5) y8))
                                           (* 64  ((_ @int_of 6) y8))
                                           (* 128 ((_ @int_of 7) y8))))
                                 1) ; WRONG: Should be 0 instead
                                )) :rule pbblast_bvuge)"#: false,
            }

            // For bvuge the correct encoding is:
            //   (- (sum_x8) (sum_y8)) >= 0
            // Here we deliberately use 63 instead of 64 for one of the summands in x8.
            "bvuge wrong coefficient" {
                r#"(step t1 (cl (= (bvuge x8 y8)
                                 (>= (- (+ (* 1   ((_ @int_of 0) x8))
                                           (* 2   ((_ @int_of 1) x8))
                                           (* 4   ((_ @int_of 2) x8))
                                           (* 8   ((_ @int_of 3) x8))
                                           (* 16  ((_ @int_of 4) x8))
                                           (* 32  ((_ @int_of 5) x8))
                                           (* 63  ((_ @int_of 6) x8))    ; WRONG: should be (* 64 ((_ @int_of 1) x8))
                                           (* 128 ((_ @int_of 7) x8)))
                                        (+ (* 1   ((_ @int_of 0) y8))
                                           (* 2   ((_ @int_of 1) y8))
                                           (* 4   ((_ @int_of 2) y8))
                                           (* 8   ((_ @int_of 3) y8))
                                           (* 16  ((_ @int_of 4) y8))
                                           (* 32  ((_ @int_of 5) y8))
                                           (* 64  ((_ @int_of 6) y8))
                                           (* 128 ((_ @int_of 7) y8))))
                                 0))) :rule pbblast_bvuge)"#: false,
            }

            "Trailing Zero" {
                r#"(step t1 (cl (= (bvuge x8 y8)
                                 (>= (- (+ (* 1   ((_ @int_of 0) x8))
                                           (* 2   ((_ @int_of 1) x8))
                                           (* 4   ((_ @int_of 2) x8))
                                           (* 8   ((_ @int_of 3) x8))
                                           (* 16  ((_ @int_of 4) x8))
                                           (* 32  ((_ @int_of 5) x8))
                                           (* 64  ((_ @int_of 6) x8))
                                           (* 128 ((_ @int_of 7) x8))
                                         0)
                                        (+ (* 1   ((_ @int_of 0) y8))
                                           (* 2   ((_ @int_of 1) y8))
                                           (* 4   ((_ @int_of 2) y8))
                                           (* 8   ((_ @int_of 3) y8))
                                           (* 16  ((_ @int_of 4) y8))
                                           (* 32  ((_ @int_of 5) y8))
                                           (* 64  ((_ @int_of 6) y8))
                                           (* 128 ((_ @int_of 7) y8))
                                         0))
                                 0))) :rule pbblast_bvuge)"#: false,
            }


        }
    }

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
    fn pbblast_bvslt_2() {
        test_cases! {
            definitions = "
            (declare-const x2 (_ BitVec 2))
            (declare-const y2 (_ BitVec 2))
        ",

            // Using explicit multiplication everywhere.
            "bvslt on two bits with explicit multiplication" {
                r#"(step t1 (cl (= (bvslt x2 y2)
                                (>= (+
                                        (-
                                            (* 1 ((_ @int_of 0) y2))         ; y sum
                                            (* 2 ((_ @int_of 1) y2))         ; y sign
                                        )
                                        (-
                                            (* 2 ((_ @int_of 1) x2))         ; x sign
                                            (* 1 ((_ @int_of 0) x2))         ; x sum
                                        )
                                    ) 1))) :rule pbblast_bvslt)"#: true,
            }

            // Omitting the explicit multiplication by 1 in the sum parts.
            "bvslt on two bits omitting multiplication by 1 in sum parts" {
                r#"(step t1 (cl (= (bvslt x2 y2)
                                (>= (+
                                        (-
                                            ((_ @int_of 0) y2)               ; y sum omitted "* 1"
                                            (* 2 ((_ @int_of 1) y2)) 
                                        )
                                        (-
                                            (* 2 ((_ @int_of 1) x2))         
                                            ((_ @int_of 0) x2)               ; x sum omitted "* 1"
                                        )
                                    ) 1))) :rule pbblast_bvslt)"#: true,
            }

            // Wrong scalar of the sign bit
            "bvslt on two bits wrong scalar of the sign bit of y" {
                r#"(step t1 (cl (= (bvslt x2 y2)
                                (>= (+
                                        (-
                                            (* 1 ((_ @int_of 0) y2))
                                            (* 1 ((_ @int_of 1) y2))         ; should be * 2
                                        )
                                        (-
                                            (* 2 ((_ @int_of 1) x2))
                                            (* 1 ((_ @int_of 0) x2))
                                        )
                                    ) 1))) :rule pbblast_bvslt)"#: false,
            }

            "bvslt on two bits wrong scalar of the sign bit of x" {
                r#"(step t1 (cl (= (bvslt x2 y2)
                                (>= (+
                                        (-
                                            (* 1 ((_ @int_of 0) y2))
                                            (* 2 ((_ @int_of 1) y2))    
                                        )
                                        (-
                                            (* 1 ((_ @int_of 1) x2))         ; should be * 2
                                            (* 1 ((_ @int_of 0) x2))
                                        )
                                    ) 1))) :rule pbblast_bvslt)"#: false,
            }

            // Wrong indexing of the sign bit
            "bvslt on two bits wrong indexing of the sign bit of y" {
                r#"(step t1 (cl (= (bvslt x2 y2)
                                (>= (+
                                        (-
                                            (* 1 ((_ @int_of 0) y2))
                                            (* 2 ((_ @int_of 0) y2))         ; should be (_ @int_of 1)
                                        )
                                        (-
                                            (* 2 ((_ @int_of 1) x2))
                                            (* 1 ((_ @int_of 0) x2))
                                        )
                                    ) 1))) :rule pbblast_bvslt)"#: false,
            }

            "bvslt on two bits wrong indexing of the sign bit of x" {
                r#"(step t1 (cl (= (bvslt x2 y2)
                                (>= (+
                                        (-
                                            (* 1 ((_ @int_of 0) y2))
                                            (* 2 ((_ @int_of 1) y2))    
                                        )
                                        (-
                                            (* 2 ((_ @int_of 0) x2))         ; should be (_ @int_of 1)
                                            (* 1 ((_ @int_of 0) x2))
                                        )
                                    ) 1))) :rule pbblast_bvslt)"#: false,
            }

            "bvslt on two bits wrong bitvector of the sign bit of x" {
                r#"(step t1 (cl (= (bvslt x2 y2)
                                (>= (+
                                        (-
                                            (* 1 ((_ @int_of 0) y2))
                                            (* 2 ((_ @int_of 1) y2))    
                                        )
                                        (-
                                            (* 2 ((_ @int_of 1) y2))         ; should be x2
                                            (* 1 ((_ @int_of 0) x2))
                                        )
                                    ) 1))) :rule pbblast_bvslt)"#: false,
            }

            "bvslt on two bits wrong bitvector of the sign bit of y" {
                r#"(step t1 (cl (= (bvslt x2 y2)
                                (>= (+
                                        (-
                                            (* 1 ((_ @int_of 0) y2))
                                            (* 2 ((_ @int_of 1) x2))         ; should be y2
                                        )
                                        (-
                                            (* 2 ((_ @int_of 1) x2))         
                                            (* 1 ((_ @int_of 0) x2))
                                        )
                                    ) 1))) :rule pbblast_bvslt)"#: false,
            }

            // Wrong indexing of the summation term
            "bvslt on two bits with wrong indexing of the summation term" {
                r#"(step t1 (cl (= (bvslt x2 y2)
                                (>= (+
                                        (-
                                            (* 1 ((_ @int_of 1) y2))         ; should be "@int_of 0"
                                            (* 2 ((_ @int_of 1) y2))
                                        )
                                        (-
                                            (* 2 ((_ @int_of 1) x2))
                                            (* 1 ((_ @int_of 0) x2))
                                        )
                                    ) 1))) :rule pbblast_bvslt)"#: false,
            }

            "Trailing Zero" {
                r#"(step t1 (cl (= (bvslt x2 y2)
                                (>= (+
                                        (-
                                            (+ (* 1 ((_ @int_of 0) y2)) 0)   ; y sum
                                            (* 2 ((_ @int_of 1) y2))         ; y sign
                                        )
                                        (-
                                            (* 2 ((_ @int_of 1) x2))         ; x sign
                                            (+ (* 1 ((_ @int_of 0) x2)) 0)   ; x sum
                                        )
                                    ) 1))) :rule pbblast_bvslt)"#: false,

                r#"(step t1 (cl (= (bvslt x2 y2)
                                (>= (+
                                        (-
                                            (+ ((_ @int_of 0) y2) 0)         ; y sum omitted "* 1"
                                            (* 2 ((_ @int_of 1) y2)) 
                                        )
                                        (-
                                            (* 2 ((_ @int_of 1) x2))         
                                            (+ ((_ @int_of 0) x2) 0)         ; x sum omitted "* 1"
                                        )
                                    ) 1))) :rule pbblast_bvslt)"#: false,
            }
        }
    }

    #[test]
    fn pbblast_bvslt_4() {
        test_cases! {
            definitions = "
            (declare-const x4 (_ BitVec 4))
            (declare-const y4 (_ BitVec 4))
        ",
            // Using explicit multiplication everywhere.
            "bvslt on 4 bits with explicit multiplication" {
                r#"(step t1 (cl (= (bvslt x4 y4)
                                (>= (+
                                        (-
                                            (+ (* 1 ((_ @int_of 0) y4))
                                               (* 2 ((_ @int_of 1) y4))
                                               (* 4 ((_ @int_of 2) y4)))
                                            (* 8 ((_ @int_of 3) y4)))
                                        (-
                                            (* 8 ((_ @int_of 3) x4))
                                            (+ (* 1 ((_ @int_of 0) x4))
                                               (* 2 ((_ @int_of 1) x4))
                                               (* 4 ((_ @int_of 2) x4)))
                                        )
                                    ) 1))) :rule pbblast_bvslt)"#: true,
            }

            // Omitting explicit multiplication by 1 in the sum parts.
            "bvslt on 4 bits omitting multiplication by 1 in sum parts" {
                r#"(step t1 (cl (= (bvslt x4 y4)
                                (>= (+
                                        (-
                                            (+ ((_ @int_of 0) y4)            ; omit "* 1"
                                               (* 2 ((_ @int_of 1) y4))
                                               (* 4 ((_ @int_of 2) y4)))
                                            (* 8 ((_ @int_of 3) y4)))
                                        (-
                                            (* 8 ((_ @int_of 3) x4))
                                            (+ ((_ @int_of 0) x4)            ; omit "* 1"
                                               (* 2 ((_ @int_of 1) x4))
                                               (* 4 ((_ @int_of 2) x4)))
                                        )
                                    ) 1))) :rule pbblast_bvslt)"#: true,
            }

            "wrong indexed bvslt on 4 bits with explicit multiplication" {
                r#"(step t1 (cl (= (bvslt x4 y4)
                                (>= (+
                                        (-
                                            (+ (* 8 ((_ @int_of 0) y4)) ; wrong coefficients
                                               (* 4 ((_ @int_of 1) y4))
                                               (* 2 ((_ @int_of 2) y4)))
                                            (* 1 ((_ @int_of 3) y4)))
                                        (-
                                            (* 8 ((_ @int_of 3) x4))
                                            (+ (* 1 ((_ @int_of 0) x4))
                                               (* 2 ((_ @int_of 1) x4))
                                               (* 4 ((_ @int_of 2) x4)))
                                        )
                                    ) 1))) :rule pbblast_bvslt)"#: false,
            }

            "bvslt on four bits wrong scalar of the sign bit" {
                            r#"(step t1 (cl (= (bvslt x4 y4)
                                (>= (+
                                        (-
                                            (+ (* 1 ((_ @int_of 0) y4))
                                               (* 2 ((_ @int_of 1) y4))
                                               (* 4 ((_ @int_of 2) y4)))
                                            (* 4 ((_ @int_of 3) y4)))    ; should be * 8
                                        (-
                                            (* 8 ((_ @int_of 3) x4))
                                            (+ (* 1 ((_ @int_of 0) x4))
                                               (* 2 ((_ @int_of 1) x4))
                                               (* 4 ((_ @int_of 2) x4)))
                                        )
                                    ) 1))) :rule pbblast_bvslt)"#: false,
            }

            "Trailing Zero" {
                r#"(step t1 (cl (= (bvslt x4 y4)
                                (>= (+
                                        (-
                                            (+ (* 1 ((_ @int_of 0) y4))
                                               (* 2 ((_ @int_of 1) y4))
                                               (* 4 ((_ @int_of 2) y4))
                                               0)
                                            (* 8 ((_ @int_of 3) y4)))
                                        (-
                                            (* 8 ((_ @int_of 3) x4))
                                            (+ (* 1 ((_ @int_of 0) x4))
                                               (* 2 ((_ @int_of 1) x4))
                                               (* 4 ((_ @int_of 2) x4))
                                               0)
                                        )
                                    ) 1))) :rule pbblast_bvslt)"#: false,

                r#"(step t1 (cl (= (bvslt x4 y4)
                                (>= (+
                                        (-
                                            (+ ((_ @int_of 0) y4)            ; omit "* 1"
                                               (* 2 ((_ @int_of 1) y4))
                                               (* 4 ((_ @int_of 2) y4))
                                               0)
                                            (* 8 ((_ @int_of 3) y4)))
                                        (-
                                            (* 8 ((_ @int_of 3) x4))
                                            (+ ((_ @int_of 0) x4)            ; omit "* 1"
                                               (* 2 ((_ @int_of 1) x4))
                                               (* 4 ((_ @int_of 2) x4))
                                               0)
                                        )
                                    ) 1))) :rule pbblast_bvslt)"#: false,
            }


        }
    }

    #[test]
    fn pbblast_bvsgt_2() {
        test_cases! {
            definitions = "
            (declare-const x2 (_ BitVec 2))
            (declare-const y2 (_ BitVec 2))
        ",

            // Using explicit multiplication everywhere.
            "bvsgt on two bits with explicit multiplication" {
                r#"(step t1 (cl (= (bvsgt x2 y2)
                                (>= (+ (-
                                            (* 1 ((_ @int_of 0) x2))   ; x sum
                                            (* 2 ((_ @int_of 1) x2))         ; x sign
                                        )
                                        (-
                                            (* 2 ((_ @int_of 1) y2))         ; y sign
                                            (* 1 ((_ @int_of 0) y2))   ; y sum
                                        )
                                    ) 1))) :rule pbblast_bvsgt)"#: true,
            }

            // Omitting the explicit multiplication by 1 in the sum parts.
            "bvsgt on two bits omitting multiplication by 1 in sum parts" {
                r#"(step t1 (cl (= (bvsgt x2 y2)
                                (>= (+
                                        (-
                                            ((_ @int_of 0) x2)         ; x sum omitted "* 1"
                                            (* 2 ((_ @int_of 1) x2)) 
                                        )
                                        (-
                                            (* 2 ((_ @int_of 1) y2))         
                                            ((_ @int_of 0) y2)         ; y sum omitted "* 1"
                                        )
                                    ) 1))) :rule pbblast_bvsgt)"#: true,
            }

            // Wrong scalar of the sign bit
            "bvsgt on two bits wrong scalar of the sign bit of y" {
                r#"(step t1 (cl (= (bvsgt x2 y2)
                                (>= (+
                                        (-
                                            (* 1 ((_ @int_of 0) x2))
                                            (* 1 ((_ @int_of 1) x2))         ; should be * 2
                                        )
                                        (-
                                            (* 2 ((_ @int_of 1) y2))
                                            (* 1 ((_ @int_of 0) y2))
                                        )
                                    ) 1))) :rule pbblast_bvsgt)"#: false,
            }

            "bvsgt on two bits wrong scalar of the sign bit of y" {
                r#"(step t1 (cl (= (bvsgt x2 y2)
                                (>= (+
                                        (-
                                            (* 1 ((_ @int_of 0) x2))
                                            (* 2 ((_ @int_of 1) x2))    
                                        )
                                        (-
                                            (* 1 ((_ @int_of 1) y2))         ; should be * 2
                                            (* 1 ((_ @int_of 0) y2))
                                        )
                                    ) 1))) :rule pbblast_bvsgt)"#: false,
            }

            // Wrong indexing of the sign bit
            "bvsgt on two bits wrong indexing of the sign bit of x" {
                r#"(step t1 (cl (= (bvsgt x2 y2)
                                (>= (+
                                        (-
                                            (* 1 ((_ @int_of 0) x2))
                                            (* 2 ((_ @int_of 0) x2))         ; should be (_ @int_of 1)
                                        )
                                        (-
                                            (* 2 ((_ @int_of 1) y2))
                                            (* 1 ((_ @int_of 0) y2))
                                        )
                                    ) 1))) :rule pbblast_bvsgt)"#: false,
            }

            "bvsgt on two bits wrong indexing of the sign bit of y" {
                r#"(step t1 (cl (= (bvsgt x2 y2)
                                (>= (+
                                        (-
                                            (* 1 ((_ @int_of 0) x2))
                                            (* 2 ((_ @int_of 1) x2))    
                                        )
                                        (-
                                            (* 2 ((_ @int_of 0) y2))         ; should be (_ @int_of 1)
                                            (* 1 ((_ @int_of 0) y2))
                                        )
                                    ) 1))) :rule pbblast_bvsgt)"#: false,
            }

            "bvsgt on two bits wrong bitvector of the sign bit of y" {
                r#"(step t1 (cl (= (bvsgt x2 y2)
                                (>= (+
                                        (-
                                            (* 1 ((_ @int_of 0) x2))
                                            (* 2 ((_ @int_of 1) x2))    
                                        )
                                        (-
                                            (* 2 ((_ @int_of 1) x2))         ; should be y2
                                            (* 1 ((_ @int_of 0) y2))
                                        )
                                    ) 1))) :rule pbblast_bvsgt)"#: false,
            }

            "bvsgt on two bits wrong bitvector of the sign bit of x" {
                r#"(step t1 (cl (= (bvsgt x2 y2)
                                (>= (+
                                        (-
                                            (* 1 ((_ @int_of 0) x2))
                                            (* 2 ((_ @int_of 1) y2))         ; should be x2
                                        )
                                        (-
                                            (* 2 ((_ @int_of 1) y2))         
                                            (* 1 ((_ @int_of 0) y2))
                                        )
                                    ) 1))) :rule pbblast_bvsgt)"#: false,
            }

            // Wrong indexing of the summation term
            "bvsgt on two bits with wrong indexing of the summation term" {
                r#"(step t1 (cl (= (bvsgt x2 y2)
                                (>= (+
                                        (-
                                            (* 1 ((_ @int_of 1) x2))   ; should be "@int_of 0"
                                            (* 2 ((_ @int_of 1) x2))
                                        )
                                        (-
                                            (* 2 ((_ @int_of 1) y2))
                                            (* 1 ((_ @int_of 0) y2))
                                        )
                                    ) 1))) :rule pbblast_bvsgt)"#: false,
            }

            "Trailing Zero" {
                r#"(step t1 (cl (= (bvsgt x2 y2)
                                (>= (+ (-
                                            (+ (* 1 ((_ @int_of 0) x2)) 0)   ; x sum
                                            (* 2 ((_ @int_of 1) x2))         ; x sign
                                        )
                                        (-
                                            (* 2 ((_ @int_of 1) y2))         ; y sign
                                            (+ (* 1 ((_ @int_of 0) y2)) 0)   ; y sum
                                        )
                                    ) 1))) :rule pbblast_bvsgt)"#: false,

                r#"(step t1 (cl (= (bvsgt x2 y2)
                                (>= (+
                                        (-
                                            (+ ((_ @int_of 0) x2) 0)         ; x sum omitted "* 1"
                                            (* 2 ((_ @int_of 1) x2)) 
                                        )
                                        (-
                                            (* 2 ((_ @int_of 1) y2))         
                                            (+ ((_ @int_of 0) y2) 0)         ; y sum omitted "* 1"
                                        )
                                    ) 1))) :rule pbblast_bvsgt)"#: false,
            }
        }
    }

    #[test]
    fn pbblast_bvsgt_4() {
        test_cases! {
            definitions = "
            (declare-const x4 (_ BitVec 4))
            (declare-const y4 (_ BitVec 4))
        ",
            // Using explicit multiplication everywhere.
            "bvsgt on 4 bits with explicit multiplication" {
                r#"(step t1 (cl (= (bvsgt x4 y4)
                                (>= (+
                                        (-
                                            (+ (* 1 ((_ @int_of 0) x4))
                                               (* 2 ((_ @int_of 1) x4))
                                               (* 4 ((_ @int_of 2) x4)))
                                            (* 8 ((_ @int_of 3) x4)))
                                        (-
                                            (* 8 ((_ @int_of 3) y4))
                                            (+ (* 1 ((_ @int_of 0) y4))
                                               (* 2 ((_ @int_of 1) y4))
                                               (* 4 ((_ @int_of 2) y4)))
                                        )
                                    ) 1))) :rule pbblast_bvsgt)"#: true,
            }

            // Omitting explicit multiplication by 1 in the sum parts.
            "bvsgt on 4 bits omitting multiplication by 1 in sum parts" {
                r#"(step t1 (cl (= (bvsgt x4 y4)
                                (>= (+
                                        (-
                                            (+ ((_ @int_of 0) x4)            ; omit "* 1"
                                               (* 2 ((_ @int_of 1) x4))
                                               (* 4 ((_ @int_of 2) x4)))
                                            (* 8 ((_ @int_of 3) x4)))
                                        (-
                                            (* 8 ((_ @int_of 3) y4))
                                            (+ ((_ @int_of 0) y4)            ; omit "* 1"
                                               (* 2 ((_ @int_of 1) y4))
                                               (* 4 ((_ @int_of 2) y4)))
                                        )
                                    ) 1))) :rule pbblast_bvsgt)"#: true,
            }

            "wrong indexed bvsgt on 4 bits with explicit multiplication" {
                r#"(step t1 (cl (= (bvsgt x4 y4)
                                (>= (+
                                        (-
                                            (+ (* 8 ((_ @int_of 0) x4)) ; wrong coefficients
                                               (* 4 ((_ @int_of 1) x4))
                                               (* 2 ((_ @int_of 2) x4)))
                                            (* 1 ((_ @int_of 3) x4)))
                                        (-
                                            (* 8 ((_ @int_of 3) y4))
                                            (+ (* 1 ((_ @int_of 0) y4))
                                               (* 2 ((_ @int_of 1) y4))
                                               (* 4 ((_ @int_of 2) y4)))
                                        )
                                    ) 1))) :rule pbblast_bvsgt)"#: false,
            }

            "bvsgt on four bits wrong scalar of the sign bit" {
                            r#"(step t1 (cl (= (bvsgt x4 y4)
                                (>= (+
                                        (-
                                            (+ (* 1 ((_ @int_of 0) x4))
                                               (* 2 ((_ @int_of 1) x4))
                                               (* 4 ((_ @int_of 2) x4)))
                                            (* 4 ((_ @int_of 3) x4)))    ; should be * 8
                                        (-
                                            (* 8 ((_ @int_of 3) y4))
                                            (+ (* 1 ((_ @int_of 0) y4))
                                               (* 2 ((_ @int_of 1) y4))
                                               (* 4 ((_ @int_of 2) y4)))
                                        )
                                    ) 1))) :rule pbblast_bvsgt)"#: false,
            }

            "Trailing Zero" {
                r#"(step t1 (cl (= (bvsgt x4 y4)
                                (>= (+
                                        (-
                                            (+ (* 1 ((_ @int_of 0) x4))
                                               (* 2 ((_ @int_of 1) x4))
                                               (* 4 ((_ @int_of 2) x4))
                                               0)
                                            (* 8 ((_ @int_of 3) x4)))
                                        (-
                                            (* 8 ((_ @int_of 3) y4))
                                            (+ (* 1 ((_ @int_of 0) y4))
                                               (* 2 ((_ @int_of 1) y4))
                                               (* 4 ((_ @int_of 2) y4))
                                               0)
                                        )
                                    ) 1))) :rule pbblast_bvsgt)"#: false,

                r#"(step t1 (cl (= (bvsgt x4 y4)
                                (>= (+
                                        (-
                                            (+ ((_ @int_of 0) x4)            ; omit "* 1"
                                               (* 2 ((_ @int_of 1) x4))
                                               (* 4 ((_ @int_of 2) x4))
                                               0)
                                            (* 8 ((_ @int_of 3) x4)))
                                        (-
                                            (* 8 ((_ @int_of 3) y4))
                                            (+ ((_ @int_of 0) y4)            ; omit "* 1"
                                               (* 2 ((_ @int_of 1) y4))
                                               (* 4 ((_ @int_of 2) y4))
                                               0)
                                        )
                                    ) 1))) :rule pbblast_bvsgt)"#: false,
            }
        }
    }

    #[test]
    fn pbblast_bvsge_2() {
        test_cases! {
            definitions = "
            (declare-const x2 (_ BitVec 2))
            (declare-const y2 (_ BitVec 2))
        ",

            // Using explicit multiplication everywhere.
            "bvsge on two bits with explicit multiplication" {
                r#"(step t1 (cl (= (bvsge x2 y2)
                                (>= (+
                                        (-
                                            (* 1 ((_ @int_of 0) x2))   ; x sum
                                            (* 2 ((_ @int_of 1) x2))   ; x sign
                                        )
                                        (-
                                            (* 2 ((_ @int_of 1) y2))   ; y sign
                                            (* 1 ((_ @int_of 0) y2))   ; y sum
                                        )
                                    ) 0))) :rule pbblast_bvsge)"#: true,
            }

            // Omitting the explicit multiplication by 1 in the sum parts.
            "bvsge on two bits omitting multiplication by 1 in sum parts" {
                r#"(step t1 (cl (= (bvsge x2 y2)
                                (>= (+
                                        (-
                                            ((_ @int_of 0) x2)         ; x sum omitted "* 1"
                                            (* 2 ((_ @int_of 1) x2)) 
                                        )
                                        (-
                                            (* 2 ((_ @int_of 1) y2))         
                                            ((_ @int_of 0) y2)         ; y sum omitted "* 1"
                                        )
                                    ) 0))) :rule pbblast_bvsge)"#: true,
            }

            // Wrong scalar of the sign bit
            "bvsge on two bits wrong scalar of the sign bit of y" {
                r#"(step t1 (cl (= (bvsge x2 y2)
                                (>= (+
                                        (-
                                            (* 1 ((_ @int_of 0) x2))
                                            (* 1 ((_ @int_of 1) x2))   ; should be * 2
                                        )
                                        (-
                                            (* 2 ((_ @int_of 1) y2))
                                            (* 1 ((_ @int_of 0) y2))
                                        )
                                    ) 0))) :rule pbblast_bvsge)"#: false,
            }

            "bvsge on two bits wrong scalar of the sign bit of y" {
                r#"(step t1 (cl (= (bvsge x2 y2)
                                (>= (+
                                        (-
                                            (* 1 ((_ @int_of 0) x2))
                                            (* 2 ((_ @int_of 1) x2))    
                                        )
                                        (-
                                            (* 1 ((_ @int_of 1) y2))   ; should be * 2
                                            (* 1 ((_ @int_of 0) y2))
                                        )
                                    ) 0))) :rule pbblast_bvsge)"#: false,
            }

            // Wrong indexing of the sign bit
            "bvsge on two bits wrong indexing of the sign bit of x" {
                r#"(step t1 (cl (= (bvsge x2 y2)
                                (>= (+
                                        (-
                                            (* 1 ((_ @int_of 0) x2))
                                            (* 2 ((_ @int_of 0) x2))   ; should be (_ @int_of 1)
                                        )
                                        (-
                                            (* 2 ((_ @int_of 1) y2))
                                            (* 1 ((_ @int_of 0) y2))
                                        )
                                    ) 0))) :rule pbblast_bvsge)"#: false,
            }

            "bvsge on two bits wrong indexing of the sign bit of y" {
                r#"(step t1 (cl (= (bvsge x2 y2)
                                (>= (+
                                        (-
                                            (* 1 ((_ @int_of 0) x2))
                                            (* 2 ((_ @int_of 1) x2))    
                                        )
                                        (-
                                            (* 2 ((_ @int_of 0) y2))   ; should be (_ @int_of 1)
                                            (* 1 ((_ @int_of 0) y2))
                                        )
                                    ) 0))) :rule pbblast_bvsge)"#: false,
            }

            "bvsge on two bits wrong bitvector of the sign bit of y" {
                r#"(step t1 (cl (= (bvsge x2 y2)
                                (>= (+
                                        (-
                                            (* 1 ((_ @int_of 0) x2))
                                            (* 2 ((_ @int_of 1) x2))    
                                        )
                                        (-
                                            (* 2 ((_ @int_of 1) x2))   ; should be y2
                                            (* 1 ((_ @int_of 0) y2))
                                        )
                                    ) 0))) :rule pbblast_bvsge)"#: false,
            }

            "bvsge on two bits wrong bitvector of the sign bit of x" {
                r#"(step t1 (cl (= (bvsge x2 y2)
                                (>= (+
                                        (-
                                            (* 1 ((_ @int_of 0) x2))
                                            (* 2 ((_ @int_of 1) y2))   ; should be x2
                                        )
                                        (-
                                            (* 2 ((_ @int_of 1) y2))         
                                            (* 1 ((_ @int_of 0) y2))
                                        )
                                    ) 0))) :rule pbblast_bvsge)"#: false,
            }

            // Wrong indexing of the summation term
            "bvsge on two bits with wrong indexing of the summation term" {
                r#"(step t1 (cl (= (bvsge x2 y2)
                                (>= (+
                                        (-
                                            (* 1 ((_ @int_of 1) x2))   ; should be "@int_of 0"
                                            (* 2 ((_ @int_of 1) x2))
                                        )
                                        (-
                                            (* 2 ((_ @int_of 1) y2))
                                            (* 1 ((_ @int_of 0) y2))
                                        )
                                    ) 0))) :rule pbblast_bvsge)"#: false,
            }

            "Trailing Zero" {
                r#"(step t1 (cl (= (bvsge x2 y2)
                                (>= (+
                                        (-
                                            (+ (* 1 ((_ @int_of 0) x2)) 0)   ; x sum
                                            (* 2 ((_ @int_of 1) x2))         ; x sign
                                        )
                                        (-
                                            (* 2 ((_ @int_of 1) y2))         ; y sign
                                            (+ (* 1 ((_ @int_of 0) y2)) 0)   ; y sum
                                        )
                                    ) 0))) :rule pbblast_bvsge)"#: false,

                r#"(step t1 (cl (= (bvsge x2 y2)
                                (>= (+
                                        (-
                                            (+ ((_ @int_of 0) x2) 0)         ; x sum omitted "* 1"
                                            (* 2 ((_ @int_of 1) x2)) 
                                        )
                                        (-
                                            (* 2 ((_ @int_of 1) y2))         
                                            (+ ((_ @int_of 0) y2) 0)         ; y sum omitted "* 1"
                                        )
                                    ) 0))) :rule pbblast_bvsge)"#: false,
            }
        }
    }

    #[test]
    fn pbblast_bvsge_4() {
        test_cases! {
            definitions = "
            (declare-const x4 (_ BitVec 4))
            (declare-const y4 (_ BitVec 4))
        ",
            // Using explicit multiplication everywhere.
            "bvsge on 4 bits with explicit multiplication" {
                r#"(step t1 (cl (= (bvsge x4 y4)
                                (>= (+
                                        (-
                                            (+ (* 1 ((_ @int_of 0) x4))
                                               (* 2 ((_ @int_of 1) x4))
                                               (* 4 ((_ @int_of 2) x4)))
                                            (* 8 ((_ @int_of 3) x4)))
                                        (-
                                            (* 8 ((_ @int_of 3) y4))
                                            (+ (* 1 ((_ @int_of 0) y4))
                                               (* 2 ((_ @int_of 1) y4))
                                               (* 4 ((_ @int_of 2) y4)))
                                        )
                                    ) 0))) :rule pbblast_bvsge)"#: true,
            }

            // Omitting explicit multiplication by 1 in the sum parts.
            "bvsge on 4 bits omitting multiplication by 1 in sum parts" {
                r#"(step t1 (cl (= (bvsge x4 y4)
                                (>= (+
                                        (-
                                            (+ ((_ @int_of 0) x4)            ; omit "* 1"
                                               (* 2 ((_ @int_of 1) x4))
                                               (* 4 ((_ @int_of 2) x4)))
                                            (* 8 ((_ @int_of 3) x4)))
                                        (-
                                            (* 8 ((_ @int_of 3) y4))
                                            (+ ((_ @int_of 0) y4)            ; omit "* 1"
                                               (* 2 ((_ @int_of 1) y4))
                                               (* 4 ((_ @int_of 2) y4)))
                                        )
                                    ) 0))) :rule pbblast_bvsge)"#: true,
            }

            "wrong indexed bvsge on 4 bits with explicit multiplication" {
                r#"(step t1 (cl (= (bvsge x4 y4)
                                (>= (+
                                        (-
                                            (+ (* 8 ((_ @int_of 0) x4)) ; wrong coefficients
                                               (* 4 ((_ @int_of 1) x4))
                                               (* 2 ((_ @int_of 2) x4)))
                                            (* 1 ((_ @int_of 3) x4)))
                                        (-
                                            (* 8 ((_ @int_of 3) y4))
                                            (+ (* 1 ((_ @int_of 0) y4))
                                               (* 2 ((_ @int_of 1) y4))
                                               (* 4 ((_ @int_of 2) y4)))
                                        )
                                    ) 0))) :rule pbblast_bvsge)"#: false,
            }

            "bvsge on four bits wrong scalar of the sign bit" {
                            r#"(step t1 (cl (= (bvsge x4 y4)
                                (>= (+
                                        (-
                                            (+ (* 1 ((_ @int_of 0) x4))
                                               (* 2 ((_ @int_of 1) x4))
                                               (* 4 ((_ @int_of 2) x4)))
                                            (* 4 ((_ @int_of 3) x4)))    ; should be * 8
                                        (-
                                            (* 8 ((_ @int_of 3) y4))
                                            (+ (* 1 ((_ @int_of 0) y4))
                                               (* 2 ((_ @int_of 1) y4))
                                               (* 4 ((_ @int_of 2) y4)))
                                        )
                                    ) 0))) :rule pbblast_bvsge)"#: false,
            }

            "Trailing Zero" {
                r#"(step t1 (cl (= (bvsge x4 y4)
                                (>= (+
                                        (-
                                            (+ (* 1 ((_ @int_of 0) x4))
                                               (* 2 ((_ @int_of 1) x4))
                                               (* 4 ((_ @int_of 2) x4))
                                               0)
                                            (* 8 ((_ @int_of 3) x4)))
                                        (-
                                            (* 8 ((_ @int_of 3) y4))
                                            (+ (* 1 ((_ @int_of 0) y4))
                                               (* 2 ((_ @int_of 1) y4))
                                               (* 4 ((_ @int_of 2) y4))
                                               0)
                                        )
                                    ) 0))) :rule pbblast_bvsge)"#: false,

                r#"(step t1 (cl (= (bvsge x4 y4)
                                (>= (+
                                        (-
                                            (+ ((_ @int_of 0) x4)            ; omit "* 1"
                                               (* 2 ((_ @int_of 1) x4))
                                               (* 4 ((_ @int_of 2) x4))
                                               0)
                                            (* 8 ((_ @int_of 3) x4)))
                                        (-
                                            (* 8 ((_ @int_of 3) y4))
                                            (+ ((_ @int_of 0) y4)            ; omit "* 1"
                                               (* 2 ((_ @int_of 1) y4))
                                               (* 4 ((_ @int_of 2) y4))
                                               0)
                                        )
                                    ) 0))) :rule pbblast_bvsge)"#: false,
            }
        }
    }

    #[test]
    fn pbblast_bvsle_2() {
        test_cases! {
            definitions = "
            (declare-const x2 (_ BitVec 2))
            (declare-const y2 (_ BitVec 2))
        ",

            // Using explicit multiplication everywhere.
            "bvsle on two bits with explicit multiplication" {
                r#"(step t1 (cl (= (bvsle x2 y2)
                                (>= (+
                                        (-
                                            (* 1 ((_ @int_of 0) y2))   ; y sum
                                            (* 2 ((_ @int_of 1) y2))   ; y sign
                                        )
                                        (-
                                            (* 2 ((_ @int_of 1) x2))   ; x sign
                                            (* 1 ((_ @int_of 0) x2))   ; x sum
                                        )
                                    ) 0))) :rule pbblast_bvsle)"#: true,
            }

            // Omitting the explicit multiplication by 1 in the sum parts.
            "bvsle on two bits omitting multiplication by 1 in sum parts" {
                r#"(step t1 (cl (= (bvsle x2 y2)
                                (>= (+
                                        (-
                                            ((_ @int_of 0) y2)         ; y sum omitted "* 1"
                                            (* 2 ((_ @int_of 1) y2)) 
                                        )
                                        (-
                                            (* 2 ((_ @int_of 1) x2))         
                                            ((_ @int_of 0) x2)         ; x sum omitted "* 1"
                                        )
                                    ) 0))) :rule pbblast_bvsle)"#: true,
            }

            // Wrong scalar of the sign bit
            "bvsle on two bits wrong scalar of the sign bit of y" {
                r#"(step t1 (cl (= (bvsle x2 y2)
                                (>= (+
                                        (-
                                            (* 1 ((_ @int_of 0) y2))
                                            (* 1 ((_ @int_of 1) y2))   ; should be * 2
                                        )
                                        (-
                                            (* 2 ((_ @int_of 1) x2))
                                            (* 1 ((_ @int_of 0) x2))
                                        )
                                    ) 0))) :rule pbblast_bvsle)"#: false,
            }

            "bvsle on two bits wrong scalar of the sign bit of x" {
                r#"(step t1 (cl (= (bvsle x2 y2)
                                (>= (+
                                        (-
                                            (* 1 ((_ @int_of 0) y2))
                                            (* 2 ((_ @int_of 1) y2))    
                                        )
                                        (-
                                            (* 1 ((_ @int_of 1) x2))   ; should be * 2
                                            (* 1 ((_ @int_of 0) x2))
                                        )
                                    ) 0))) :rule pbblast_bvsle)"#: false,
            }

            // Wrong indexing of the sign bit
            "bvsle on two bits wrong indexing of the sign bit of y" {
                r#"(step t1 (cl (= (bvsle x2 y2)
                                (>= (+
                                        (-
                                            (* 1 ((_ @int_of 0) y2))
                                            (* 2 ((_ @int_of 0) y2))   ; should be (_ @int_of 1)
                                        )
                                        (-
                                            (* 2 ((_ @int_of 1) x2))
                                            (* 1 ((_ @int_of 0) x2))
                                        )
                                    ) 0))) :rule pbblast_bvsle)"#: false,
            }

            "bvsle on two bits wrong indexing of the sign bit of x" {
                r#"(step t1 (cl (= (bvsle x2 y2)
                                (>= (+
                                        (-
                                            (* 1 ((_ @int_of 0) y2))
                                            (* 2 ((_ @int_of 1) y2))    
                                        )
                                        (-
                                            (* 2 ((_ @int_of 0) x2))   ; should be (_ @int_of 1)
                                            (* 1 ((_ @int_of 0) x2))
                                        )
                                    ) 0))) :rule pbblast_bvsle)"#: false,
            }

            "bvsle on two bits wrong bitvector of the sign bit of x" {
                r#"(step t1 (cl (= (bvsle x2 y2)
                                (>= (+
                                        (-
                                            (* 1 ((_ @int_of 0) y2))
                                            (* 2 ((_ @int_of 1) y2))    
                                        )
                                        (-
                                            (* 2 ((_ @int_of 1) y2))   ; should be x2
                                            (* 1 ((_ @int_of 0) x2))
                                        )
                                    ) 0))) :rule pbblast_bvsle)"#: false,
            }

            "bvsle on two bits wrong bitvector of the sign bit of y" {
                r#"(step t1 (cl (= (bvsle x2 y2)
                                (>= (+
                                        (-
                                            (* 1 ((_ @int_of 0) y2))
                                            (* 2 ((_ @int_of 1) x2))   ; should be y2
                                        )
                                        (-
                                            (* 2 ((_ @int_of 1) x2))         
                                            (* 1 ((_ @int_of 0) x2))
                                        )
                                    ) 0))) :rule pbblast_bvsle)"#: false,
            }

            // Wrong indexing of the summation term
            "bvsle on two bits with wrong indexing of the summation term" {
                r#"(step t1 (cl (= (bvsle x2 y2)
                                (>= (+
                                        (-
                                            (* 1 ((_ @int_of 1) y2))   ; should be "@int_of 0"
                                            (* 2 ((_ @int_of 1) y2))
                                        )
                                        (-
                                            (* 2 ((_ @int_of 1) x2))
                                            (* 1 ((_ @int_of 0) x2))
                                        )
                                    ) 0))) :rule pbblast_bvsle)"#: false,
            }

            "Trailing Zero" {
                r#"(step t1 (cl (= (bvsle x2 y2)
                                (>= (+
                                        (-
                                            (+ (* 1 ((_ @int_of 0) y2)) 0)   ; y sum
                                            (* 2 ((_ @int_of 1) y2))         ; y sign
                                        )
                                        (-
                                            (* 2 ((_ @int_of 1) x2))         ; x sign
                                            (+ (* 1 ((_ @int_of 0) x2)) 0)   ; x sum
                                        )
                                    ) 0))) :rule pbblast_bvsle)"#: false,

                r#"(step t1 (cl (= (bvsle x2 y2)
                                (>= (+
                                        (-
                                            (+ ((_ @int_of 0) y2) 0)         ; y sum omitted "* 1"
                                            (* 2 ((_ @int_of 1) y2)) 
                                        )
                                        (-
                                            (* 2 ((_ @int_of 1) x2))         
                                            (+ ((_ @int_of 0) x2) 0)         ; x sum omitted "* 1"
                                        )
                                    ) 0))) :rule pbblast_bvsle)"#: false,
            }
        }
    }

    #[test]
    fn pbblast_bvsle_4() {
        test_cases! {
            definitions = "
            (declare-const x4 (_ BitVec 4))
            (declare-const y4 (_ BitVec 4))
        ",
            // Using explicit multiplication everywhere.
            "bvsle on 4 bits with explicit multiplication" {
                r#"(step t1 (cl (= (bvsle x4 y4)
                                (>= (+
                                        (-
                                            (+ (* 1 ((_ @int_of 0) y4))
                                               (* 2 ((_ @int_of 1) y4))
                                               (* 4 ((_ @int_of 2) y4)))
                                            (* 8 ((_ @int_of 3) y4)))
                                        (-
                                            (* 8 ((_ @int_of 3) x4))
                                            (+ (* 1 ((_ @int_of 0) x4))
                                               (* 2 ((_ @int_of 1) x4))
                                               (* 4 ((_ @int_of 2) x4)))
                                        )
                                    ) 0))) :rule pbblast_bvsle)"#: true,
            }

            // Omitting explicit multiplication by 1 in the sum parts.
            "bvsle on 4 bits omitting multiplication by 1 in sum parts" {
                r#"(step t1 (cl (= (bvsle x4 y4)
                                (>= (+
                                        (-
                                            (+ ((_ @int_of 0) y4)            ; omit "* 1"
                                               (* 2 ((_ @int_of 1) y4))
                                               (* 4 ((_ @int_of 2) y4)))
                                            (* 8 ((_ @int_of 3) y4)))
                                        (-
                                            (* 8 ((_ @int_of 3) x4))
                                            (+ ((_ @int_of 0) x4)            ; omit "* 1"
                                               (* 2 ((_ @int_of 1) x4))
                                               (* 4 ((_ @int_of 2) x4)))
                                        )
                                    ) 0))) :rule pbblast_bvsle)"#: true,
            }

            "wrong indexed bvsle on 4 bits with explicit multiplication" {
                r#"(step t1 (cl (= (bvsle x4 y4)
                                (>= (+
                                        (-
                                            (+ (* 8 ((_ @int_of 0) y4)) ; wrong coefficients
                                               (* 4 ((_ @int_of 1) y4))
                                               (* 2 ((_ @int_of 2) y4)))
                                            (* 1 ((_ @int_of 3) y4)))
                                        (-
                                            (* 8 ((_ @int_of 3) x4))
                                            (+ (* 1 ((_ @int_of 0) x4))
                                               (* 2 ((_ @int_of 1) x4))
                                               (* 4 ((_ @int_of 2) x4)))
                                        )
                                    ) 0))) :rule pbblast_bvsle)"#: false,
            }

            "bvsle on four bits wrong scalar of the sign bit" {
                            r#"(step t1 (cl (= (bvsle x4 y4)
                                (>= (+
                                        (-
                                            (+ (* 1 ((_ @int_of 0) y4))
                                               (* 2 ((_ @int_of 1) y4))
                                               (* 4 ((_ @int_of 2) y4)))
                                            (* 4 ((_ @int_of 3) y4)))    ; should be * 8
                                        (-
                                            (* 8 ((_ @int_of 3) x4))
                                            (+ (* 1 ((_ @int_of 0) x4))
                                               (* 2 ((_ @int_of 1) x4))
                                               (* 4 ((_ @int_of 2) x4)))
                                        )
                                    ) 0))) :rule pbblast_bvsle)"#: false,
            }

            "Trailing Zero" {
                r#"(step t1 (cl (= (bvsle x4 y4)
                                (>= (+
                                        (-
                                            (+ (* 1 ((_ @int_of 0) y4))
                                               (* 2 ((_ @int_of 1) y4))
                                               (* 4 ((_ @int_of 2) y4))
                                               0)
                                            (* 8 ((_ @int_of 3) y4)))
                                        (-
                                            (* 8 ((_ @int_of 3) x4))
                                            (+ (* 1 ((_ @int_of 0) x4))
                                               (* 2 ((_ @int_of 1) x4))
                                               (* 4 ((_ @int_of 2) x4))
                                               0)
                                        )
                                    ) 0))) :rule pbblast_bvsle)"#: false,

                r#"(step t1 (cl (= (bvsle x4 y4)
                                (>= (+
                                        (-
                                            (+ ((_ @int_of 0) y4)            ; omit "* 1"
                                               (* 2 ((_ @int_of 1) y4))
                                               (* 4 ((_ @int_of 2) y4))
                                               0)
                                            (* 8 ((_ @int_of 3) y4)))
                                        (-
                                            (* 8 ((_ @int_of 3) x4))
                                            (+ ((_ @int_of 0) x4)            ; omit "* 1"
                                               (* 2 ((_ @int_of 1) x4))
                                               (* 4 ((_ @int_of 2) x4))
                                               0)
                                        )
                                    ) 0))) :rule pbblast_bvsle)"#: false,
            }
        }
    }

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
    fn pbblast_pbbconst_1() {
        test_cases! {
            definitions = "
            (declare-const r (_ BitVec 1))
        ",
            "Valid 1-bit constant" {
                r#"(step t1 (cl (= #b1 (@pbbterm 1))) :rule pbblast_pbbconst)"#: true,
                r#"(step t1 (cl (= #b0 (@pbbterm 0))) :rule pbblast_pbbconst)"#: true,
            }
            "Invalid 1-bit value" {
                r#"(step t1 (cl (= #b1 (@pbbterm 0))) :rule pbblast_pbbconst)"#: false,
                r#"(step t1 (cl (= #b0 (@pbbterm 1))) :rule pbblast_pbbconst)"#: false,
            }
        }
    }

    #[test]
    fn pbblast_pbbconst_2() {
        test_cases! {
            definitions = "
            (declare-const r (_ BitVec 2))
        ",
            "Valid 2-bit constant" {
                r#"(step t1 (cl (= #b00 (@pbbterm 0 0))) :rule pbblast_pbbconst)"#: true,
                r#"(step t1 (cl (= #b10 (@pbbterm 0 1))) :rule pbblast_pbbconst)"#: true,
                r#"(step t1 (cl (= #b01 (@pbbterm 1 0))) :rule pbblast_pbbconst)"#: true,
                r#"(step t1 (cl (= #b11 (@pbbterm 1 1))) :rule pbblast_pbbconst)"#: true,
            }
            "Invalid bit pattern" {
                r#"(step t1 (cl (= #b10 (@pbbterm 1 0))) :rule pbblast_pbbconst)"#: false,
                r#"(step t1 (cl (= #b10 (@pbbterm 1 1))) :rule pbblast_pbbconst)"#: false,
                r#"(step t1 (cl (= #b01 (@pbbterm 0 1))) :rule pbblast_pbbconst)"#: false,
                r#"(step t1 (cl (= #b01 (@pbbterm 0 0))) :rule pbblast_pbbconst)"#: false,
                r#"(step t1 (cl (= #b11 (@pbbterm 0 0))) :rule pbblast_pbbconst)"#: false,
                r#"(step t1 (cl (= #b00 (@pbbterm 1 1))) :rule pbblast_pbbconst)"#: false,
            }
        }
    }

    #[test]
    fn pbblast_pbbconst_4() {
        test_cases! {
            definitions = "
            (declare-const r (_ BitVec 4))
        ",
            "Valid 4-bit constant" {
                // #b0111 = LSB-first: [1,1,1,0]
                r#"(step t1 (cl (= #b0111 (@pbbterm 1 1 1 0))) :rule pbblast_pbbconst)"#: true,
            }
            "Wrong term" {
                r#"(step t1 (cl (= #b0111 (@pbbterm 1 1 1 1))) :rule pbblast_pbbconst)"#: false,
            }
        }
    }

    #[test]
    fn pbblast_pbbconst_8() {
        test_cases! {
            definitions = "
            (declare-const r (_ BitVec 8))
        ",
            "Valid 8-bit constant" {
                // #b11110000 = LSB-first: [0,0,0,0,1,1,1,1]
                r#"(step t1 (cl (= #b11110000 (@pbbterm 0 0 0 0 1 1 1 1))) :rule pbblast_pbbconst)"#: true,
            }
            "Wrong bit value" {
                r#"(step t1 (cl (= #b11110000 (@pbbterm 0 0 0 0 1 1 0 1))) :rule pbblast_pbbconst)"#: false,
            }
        }
    }

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
