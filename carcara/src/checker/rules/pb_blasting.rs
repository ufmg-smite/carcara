use super::{RuleArgs, RuleResult};
use crate::{
    ast::{pool::TermPool, Rc, Sort, Term},
    checker::error::CheckerError,
};
use rug::Integer;

// Helper to check that a summation has the expected shape
fn check_pbblast_sum(
    pool: &mut dyn TermPool,
    bitvector: &Rc<Term>,
    sum: &[Rc<Term>],
) -> RuleResult {
    // Obtain the bitvector width from the pool.
    let Sort::BitVec(width) = pool.sort(bitvector).as_sort().cloned().unwrap() else {
        unreachable!();
    };
    let width = width.to_usize().unwrap();

    // Drop the last element, which is the constant zero
    let sum = &sum[..sum.len() - 1];

    // The summation must have as many summands as the bitvector has bits.
    rassert!(width == sum.len(), CheckerError::Unspecified);

    for (i, element) in sum.iter().enumerate() {
        // Try to match (* c ((_ int_of idx) bv))
        let (c, idx, bv) = match match_term!((* c ((_ int_of idx) bv)) = element) {
            Some((c, (idx, bv))) => (c.as_integer_err()?, idx, bv),
            None => {
                if i == 0 {
                    // For i==0, allow the coefficient to be omitted (defaulting to 1)
                    match match_term!(((_ int_of idx) bitvector) = element) {
                        Some((idx, bv)) => (Integer::from(1), idx, bv),
                        None => panic!("Summand does not match either pattern"),
                    }
                } else {
                    panic!("Coefficient was not found and i != 0");
                }
            }
        };

        // Convert the index term to an integer.
        let idx: Integer = idx.as_integer_err()?;
        // Check that the coefficient is 2^i.
        rassert!(c == (Integer::from(1) << i), CheckerError::Unspecified);
        // Check that the index is width - i - 1.
        rassert!(idx == width - i - 1, CheckerError::Unspecified);
        // Finally, the bitvector in the summand must be the one we expect.
        rassert!(*bv == *bitvector, CheckerError::Unspecified);
    }
    Ok(())
}

// A helper that checks the two summations that occur in a pseudo–Boolean constraint.
// Here, left_sum and right_sum come from two bitvectors left_bv and right_bv respectively.
// (The overall constraint is something like `(>= (- (+ left_sum) (+ right_sum)) constant)`.)
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
        match_term_err!((= (= x y) (= (- (+ ...) (+ ...)) constant)) = &conclusion[0])?;

    // Check that the constant is 0
    let constant: Integer = constant.as_integer_err()?;
    rassert!(constant == 0, CheckerError::Unspecified);

    // Check that the summations have the correct structure.
    // (For equality the order is: sum_x for x and sum_y for y.)
    check_pbblast_constraint(pool, x, y, sum_x, sum_y)
}

/// Implements the unsigned-less-than rule.
/// The expected shape is:
///    `(= (bvult x y) (>= (- (+ sum_y) (+ sum_x)) 1))`
pub fn pbblast_bvult(RuleArgs { pool, conclusion, .. }: RuleArgs) -> RuleResult {
    let ((x, y), ((sum_y, sum_x), constant)) =
        match_term_err!((= (bvult x y) (>= (- (+ ...) (+ ...)) constant)) = &conclusion[0])?;

    // Check that the constant is 1
    let constant: Integer = constant.as_integer_err()?;
    rassert!(constant == 1, CheckerError::Unspecified);

    // For bvult the summations occur in reverse: the "left" sum comes from y and the "right" from x.
    check_pbblast_constraint(pool, y, x, sum_y, sum_x)
}

/// Implements the unsigned-greater-than rule.
///
/// The expected shape is:
///    `(= (bvugt x y) (>= (- (+ sum_x) (+ sum_y)) 1))`
pub fn pbblast_bvugt(RuleArgs { pool, conclusion, .. }: RuleArgs) -> RuleResult {
    let ((x, y), ((sum_x, sum_y), constant)) =
        match_term_err!((= (bvugt x y) (>= (- (+ ...) (+ ...)) constant)) = &conclusion[0])?;

    // Check that the constant is 1
    let constant: Integer = constant.as_integer_err()?;
    rassert!(constant == 1, CheckerError::Unspecified);

    // For bvugt the summations appear in the same order as in equality.
    check_pbblast_constraint(pool, x, y, sum_x, sum_y)
}

/// Implements the unsigned-greater-or-equal rule.
///
/// The expected shape is:
///    `(= (bvuge x y) (>= (- (+ sum_x) (+ sum_y)) 0))`
pub fn pbblast_bvuge(RuleArgs { pool, conclusion, .. }: RuleArgs) -> RuleResult {
    let ((x, y), ((sum_x, sum_y), constant)) =
        match_term_err!((= (bvuge x y) (>= (- (+ ...) (+ ...)) constant)) = &conclusion[0])?;

    // Check that the constant is 0
    let constant: Integer = constant.as_integer_err()?;
    rassert!(constant == 0, CheckerError::Unspecified);

    check_pbblast_constraint(pool, x, y, sum_x, sum_y)
}

/// Implements the unsigned-less-or-equal rule.
///
/// The expected shape is:
///    `(= (bvule x y) (>= (- (+ sum_y) (+ sum_x)) 0))`
pub fn pbblast_bvule(RuleArgs { pool, conclusion, .. }: RuleArgs) -> RuleResult {
    let ((x, y), ((sum_y, sum_x), constant)) =
        match_term_err!((= (bvule x y) (>= (- (+ ...) (+ ...)) constant)) = &conclusion[0])?;

    // Check that the constant is 0
    let constant: Integer = constant.as_integer_err()?;
    rassert!(constant == 0, CheckerError::Unspecified);

    check_pbblast_constraint(pool, x, y, sum_x, sum_y)
}

pub fn pbblast_bvslt(RuleArgs { premises, args, conclusion, .. }: RuleArgs) -> RuleResult {
    println!("{} {} {}", premises.len(), args.len(), conclusion.len());
    Err(CheckerError::Unspecified)
}

pub fn pbblast_bvsgt(RuleArgs { premises, args, conclusion, .. }: RuleArgs) -> RuleResult {
    println!("{} {} {}", premises.len(), args.len(), conclusion.len());
    Err(CheckerError::Unspecified)
}

pub fn pbblast_bvsge(RuleArgs { premises, args, conclusion, .. }: RuleArgs) -> RuleResult {
    println!("{} {} {}", premises.len(), args.len(), conclusion.len());
    Err(CheckerError::Unspecified)
}

pub fn pbblast_bvsle(RuleArgs { premises, args, conclusion, .. }: RuleArgs) -> RuleResult {
    println!("{} {} {}", premises.len(), args.len(), conclusion.len());
    Err(CheckerError::Unspecified)
}

pub fn pbblast_pbbvar(RuleArgs { premises, args, conclusion, .. }: RuleArgs) -> RuleResult {
    println!("{} {} {}", premises.len(), args.len(), conclusion.len());
    Err(CheckerError::Unspecified)
}

pub fn pbblast_pbbconst(RuleArgs { premises, args, conclusion, .. }: RuleArgs) -> RuleResult {
    println!("{} {} {}", premises.len(), args.len(), conclusion.len());
    Err(CheckerError::Unspecified)
}

pub fn pbblast_bvxor(RuleArgs { premises, args, conclusion, .. }: RuleArgs) -> RuleResult {
    println!("{} {} {}", premises.len(), args.len(), conclusion.len());
    Err(CheckerError::Unspecified)
}

pub fn pbblast_bvand(RuleArgs { premises, args, conclusion, .. }: RuleArgs) -> RuleResult {
    println!("{} {} {}", premises.len(), args.len(), conclusion.len());
    Err(CheckerError::Unspecified)
}

mod tests {
    #[test]
    fn pbblast_bveq() {
        test_cases! {
            definitions = "
            (declare-const x1 (_ BitVec 1))
            (declare-const y1 (_ BitVec 1))
            (declare-const x2 (_ BitVec 2))
            (declare-const y2 (_ BitVec 2))
        ",

            // Check that equality on single-bit bitvectors is accepted when
            // the summation for each side explicitly multiplies by 1.
            "Equality on single bits" {
                r#"(step t1 (cl (= (= x1 y1)
                                 (= (- (+ (* 1 ((_ int_of 0) x1)) 0)
                                       (+ (* 1 ((_ int_of 0) y1)) 0))
                                    0))) :rule pbblast_bveq)"#: true,
            }

            // Check that equality on single-bit bitvectors is accepted even when
            // the multiplication by 1 is omitted (i.e. defaulting to 1).
            "Omit multiplication by 1" {
                r#"(step t1 (cl (= (= x1 y1)
                                 (= (- (+ ((_ int_of 0) x1) 0)
                                       (+ ((_ int_of 0) y1) 0))
                                    0))) :rule pbblast_bveq)"#: true,
            }

            // Check that a term which is not a subtraction of sums is rejected.
            "Not a subtraction of sums" {
                r#"(step t1 (cl (= (= x1 y1)
                                 (= (+ (* 1 ((_ int_of 0) x1)) 0)
                                    0))) :rule pbblast_bveq)"#: false,
            }

            // Check that malformed products are rejected:
            // Case 1: the first summand uses a zero coefficient.
            "Malformed products: coefficient 0 in first summand" {
                r#"(step t1 (cl (= (= x1 y1)
                                 (= (- (+ (* 0 ((_ int_of 0) x1)) 0)
                                       (+ (* 1 ((_ int_of 0) y1)) 0))
                                    0))) :rule pbblast_bveq)"#: false,
            }

            // Check that malformed products are rejected:
            // Case 2: the second summand uses a zero coefficient.
            "Malformed products: coefficient 0 in second summand" {
                r#"(step t1 (cl (= (= x1 y1)
                                 (= (- (+ (* 1 ((_ int_of 0) x1)) 0)
                                       (+ (* 0 ((_ int_of 0) y1)) 0))
                                    0))) :rule pbblast_bveq)"#: false,
            }

            // Check equality on two-bit bitvectors, ensuring that:
            // - The most significant bit (index 1) uses a coefficient of 1,
            // - The least significant bit (index 0) uses a coefficient of 2.
            "Equality on two bits" {
                r#"(step t1 (cl (= (= x2 y2)
                                 (= (- (+ (* 1 ((_ int_of 1) x2))
                                         (* 2 ((_ int_of 0) x2)) 0)
                                       (+ (* 1 ((_ int_of 1) y2))
                                          (* 2 ((_ int_of 0) y2)) 0))
                                    0))) :rule pbblast_bveq)"#: true,
            }
        }
    }

    #[test]
    fn pbblast_bvult() {
        test_cases! {
            definitions = "
            (declare-const x1 (_ BitVec 1))
            (declare-const y1 (_ BitVec 1))
            (declare-const x2 (_ BitVec 2))
            (declare-const y2 (_ BitVec 2))
        ",

            // A simple test on one-bit bitvectors using explicit multiplication.
            "bvult on single bits" {
                r#"(step t1 (cl (= (bvult x1 y1)
                                 (>= (- (+ (* 1 ((_ int_of 0) y1)) 0)
                                        (+ (* 1 ((_ int_of 0) x1)) 0))
                                     1))) :rule pbblast_bvult)"#: true,
            }

            // Test where the multiplication by 1 is omitted for the only summand.
            "Omit multiplication by 1" {
                r#"(step t1 (cl (= (bvult x1 y1)
                                 (>= (- (+ ((_ int_of 0) y1) 0)
                                        (+ ((_ int_of 0) x1) 0))
                                     1))) :rule pbblast_bvult)"#: true,
            }

            // Test a malformed pseudo-Boolean constraint (e.g. not a subtraction of two sums).
            "Not a subtraction of sums" {
                r#"(step t1 (cl (= (bvult x1 y1)
                                 (>= (+ (* 1 ((_ int_of 0) y1)) 0)
                                     1))) :rule pbblast_bvult)"#: false,
            }

            // Test with malformed products: coefficient 0 is not allowed.
            "Malformed products" {
                r#"(step t1 (cl (= (bvult x1 y1)
                                 (>= (- (+ (* 0 ((_ int_of 0) y1)) 0)
                                        (+ (* 1 ((_ int_of 0) x1)) 0))
                                     1))) :rule pbblast_bvult)"#: false,
                r#"(step t1 (cl (= (bvult x1 y1)
                                 (>= (- (+ (* 1 ((_ int_of 0) y1)) 0)
                                        (+ (* 0 ((_ int_of 0) x1)) 0))
                                     1))) :rule pbblast_bvult)"#: false,
            }

            // Test on two-bit bitvectors.
            "bvult on two bits" {
                r#"(step t1 (cl (= (bvult x2 y2)
                                 (>= (- (+ (* 1 ((_ int_of 1) y2)) (* 2 ((_ int_of 0) y2)) 0)
                                        (+ (* 1 ((_ int_of 1) x2)) (* 2 ((_ int_of 0) x2)) 0))
                                     1))) :rule pbblast_bvult)"#: true,
            }
        }
    }

    #[test]
    fn pbblast_bvugt() {
        test_cases! {
            definitions = "
            (declare-const x1 (_ BitVec 1))
            (declare-const y1 (_ BitVec 1))
            (declare-const x2 (_ BitVec 2))
            (declare-const y2 (_ BitVec 2))
        ",

            // Correct pseudo–Boolean formulation for unsigned greater-than on single-bit bitvectors.
            // Expected: (bvugt x1 y1) ≈ (>= (- (+ (* 1 ((_ int_of 0) x1)) 0)
            //                                  (+ (* 1 ((_ int_of 0) y1)) 0))
            //                           1)
            "bvugt on single bits" {
                r#"(step t1 (cl (= (bvugt x1 y1)
                                 (>= (- (+ (* 1 ((_ int_of 0) x1)) 0)
                                        (+ (* 1 ((_ int_of 0) y1)) 0))
                                     1))) :rule pbblast_bvugt)"#: true,
            }

            // Accept omission of multiplication by 1 for the only summand.
            "Omit multiplication by 1" {
                r#"(step t1 (cl (= (bvugt x1 y1)
                                 (>= (- (+ ((_ int_of 0) x1) 0)
                                        (+ ((_ int_of 0) y1) 0))
                                     1))) :rule pbblast_bvugt)"#: true,
            }

            // Reject when the term is not a subtraction of two summations.
            "Not a subtraction of sums" {
                r#"(step t1 (cl (= (bvugt x1 y1)
                                 (>= (+ (* 1 ((_ int_of 0) x1)) 0)
                                     1))) :rule pbblast_bvugt)"#: false,
            }

            // Reject malformed product in the first summand (coefficient 0 instead of 1).
            "Malformed products: coefficient 0 in first summand" {
                r#"(step t1 (cl (= (bvugt x1 y1)
                                 (>= (- (+ (* 0 ((_ int_of 0) x1)) 0)
                                        (+ (* 1 ((_ int_of 0) y1)) 0))
                                     1))) :rule pbblast_bvugt)"#: false,
            }

            // Reject malformed product in the second summand (coefficient 0 instead of 1).
            "Malformed products: coefficient 0 in second summand" {
                r#"(step t1 (cl (= (bvugt x1 y1)
                                 (>= (- (+ (* 1 ((_ int_of 0) x1)) 0)
                                        (+ (* 0 ((_ int_of 0) y1)) 0))
                                     1))) :rule pbblast_bvugt)"#: false,
            }

            // Correct formulation for two-bit bitvectors.
            // Expected summands for x2: most-significant bit uses coefficient 1, least-significant uses coefficient 2.
            "bvugt on two bits" {
                r#"(step t1 (cl (= (bvugt x2 y2)
                                 (>= (- (+ (* 1 ((_ int_of 1) x2)) (* 2 ((_ int_of 0) x2)) 0)
                                        (+ (* 1 ((_ int_of 1) y2)) (* 2 ((_ int_of 0) y2)) 0))
                                     1))) :rule pbblast_bvugt)"#: true,
            }
        }
    }

    #[test]
    fn pbblast_bvuge() {
        test_cases! {
            definitions = "
            (declare-const x1 (_ BitVec 1))
            (declare-const y1 (_ BitVec 1))
            (declare-const x2 (_ BitVec 2))
            (declare-const y2 (_ BitVec 2))
        ",

            // Correct pseudo–Boolean formulation for unsigned greater-or-equal on single-bit bitvectors.
            // Expected: (bvuge x1 y1) ≈ (>= (- (+ (* 1 ((_ int_of 0) x1)) 0)
            //                                  (+ (* 1 ((_ int_of 0) y1)) 0))
            //                           0)
            "bvuge on single bits" {
                r#"(step t1 (cl (= (bvuge x1 y1)
                                 (>= (- (+ (* 1 ((_ int_of 0) x1)) 0)
                                        (+ (* 1 ((_ int_of 0) y1)) 0))
                                     0))) :rule pbblast_bvuge)"#: true,
            }

            // Accept omission of multiplication by 1.
            "Omit multiplication by 1" {
                r#"(step t1 (cl (= (bvuge x1 y1)
                                 (>= (- (+ ((_ int_of 0) x1) 0)
                                        (+ ((_ int_of 0) y1) 0))
                                     0))) :rule pbblast_bvuge)"#: true,
            }

            // Reject when the expression is not a subtraction of two summations.
            "Not a subtraction of sums" {
                r#"(step t1 (cl (= (bvuge x1 y1)
                                 (>= (+ (* 1 ((_ int_of 0) x1)) 0)
                                     0))) :rule pbblast_bvuge)"#: false,
            }

            // Reject malformed product in the first summand.
            "Malformed products: coefficient 0 in first summand" {
                r#"(step t1 (cl (= (bvuge x1 y1)
                                 (>= (- (+ (* 0 ((_ int_of 0) x1)) 0)
                                        (+ (* 1 ((_ int_of 0) y1)) 0))
                                     0))) :rule pbblast_bvuge)"#: false,
            }

            // Reject malformed product in the second summand.
            "Malformed products: coefficient 0 in second summand" {
                r#"(step t1 (cl (= (bvuge x1 y1)
                                 (>= (- (+ (* 1 ((_ int_of 0) x1)) 0)
                                        (+ (* 0 ((_ int_of 0) y1)) 0))
                                     0))) :rule pbblast_bvuge)"#: false,
            }

            // Correct formulation for two-bit bitvectors.
            "bvuge on two bits" {
                r#"(step t1 (cl (= (bvuge x2 y2)
                                 (>= (- (+ (* 1 ((_ int_of 1) x2)) (* 2 ((_ int_of 0) x2)) 0)
                                        (+ (* 1 ((_ int_of 1) y2)) (* 2 ((_ int_of 0) y2)) 0))
                                     0))) :rule pbblast_bvuge)"#: true,
            }
        }
    }

    #[test]
    fn pbblast_bvule() {
        test_cases! {
            definitions = "
            (declare-const x1 (_ BitVec 1))
            (declare-const y1 (_ BitVec 1))
            (declare-const x2 (_ BitVec 2))
            (declare-const y2 (_ BitVec 2))
        ",

            // Correct pseudo–Boolean formulation for unsigned less-or-equal on single-bit bitvectors.
            // Note the summation order is reversed compared to bvugt: the summation over y appears first.
            // Expected: (bvule x1 y1) ≈ (>= (- (+ (* 1 ((_ int_of 0) y1)) 0)
            //                                  (+ (* 1 ((_ int_of 0) x1)) 0))
            //                           0)
            "bvule on single bits" {
                r#"(step t1 (cl (= (bvule x1 y1)
                                 (>= (- (+ (* 1 ((_ int_of 0) y1)) 0)
                                        (+ (* 1 ((_ int_of 0) x1)) 0))
                                     0))) :rule pbblast_bvule)"#: true,
            }

            // Accept omission of multiplication by 1.
            "Omit multiplication by 1" {
                r#"(step t1 (cl (= (bvule x1 y1)
                                 (>= (- (+ ((_ int_of 0) y1) 0)
                                        (+ ((_ int_of 0) x1) 0))
                                     0))) :rule pbblast_bvule)"#: true,
            }

            // Reject when the term is not a subtraction of two summations.
            "Not a subtraction of sums" {
                r#"(step t1 (cl (= (bvule x1 y1)
                                 (>= (+ (* 1 ((_ int_of 0) y1)) 0)
                                     0))) :rule pbblast_bvule)"#: false,
            }

            // Reject malformed product in the first summand.
            "Malformed products: coefficient 0 in first summand" {
                r#"(step t1 (cl (= (bvule x1 y1)
                                 (>= (- (+ (* 0 ((_ int_of 0) y1)) 0)
                                        (+ (* 1 ((_ int_of 0) x1)) 0))
                                     0))) :rule pbblast_bvule)"#: false,
            }

            // Reject malformed product in the second summand.
            "Malformed products: coefficient 0 in second summand" {
                r#"(step t1 (cl (= (bvule x1 y1)
                                 (>= (- (+ (* 1 ((_ int_of 0) y1)) 0)
                                        (+ (* 0 ((_ int_of 0) x1)) 0))
                                     0))) :rule pbblast_bvule)"#: false,
            }

            // Correct formulation for two-bit bitvectors.
            "bvule on two bits" {
                r#"(step t1 (cl (= (bvule x2 y2)
                                 (>= (- (+ (* 1 ((_ int_of 1) y2)) (* 2 ((_ int_of 0) y2)) 0)
                                        (+ (* 1 ((_ int_of 1) x2)) (* 2 ((_ int_of 0) x2)) 0))
                                     0))) :rule pbblast_bvule)"#: true,
            }
        }
    }

    #[test]
    fn pbblast_bvslt() {
        test_cases! {
           definitions = "
                (declare-const x (_ BitVec 1))
                (declare-const y (_ BitVec 1))
                ",
            "Equality on single bits" {
                r#"(step t1 (cl (= (= x y) (= (- (+ ((_ int_of 0) x) 0) (+ ((_ int_of 0) y) 0)) 0))) :rule pbblast_bvslt :args (x y))"#: true,
            }
        }
    }
    #[test]
    fn pbblast_bvsgt() {
        test_cases! {
           definitions = "
                (declare-const x (_ BitVec 1))
                (declare-const y (_ BitVec 1))
                ",
            "Equality on single bits" {
                r#"(step t1 (cl (= (= x y) (= (- (+ ((_ int_of 0) x) 0) (+ ((_ int_of 0) y) 0)) 0))) :rule pbblast_bvsgt :args (x y))"#: true,
            }
        }
    }
    #[test]
    fn pbblast_bvsge() {
        test_cases! {
           definitions = "
                (declare-const x (_ BitVec 1))
                (declare-const y (_ BitVec 1))
                ",
            "Equality on single bits" {
                r#"(step t1 (cl (= (= x y) (= (- (+ ((_ int_of 0) x) 0) (+ ((_ int_of 0) y) 0)) 0))) :rule pbblast_bvsge :args (x y))"#: true,
            }
        }
    }
    #[test]
    fn pbblast_bvsle() {
        test_cases! {
           definitions = "
                (declare-const x (_ BitVec 1))
                (declare-const y (_ BitVec 1))
                ",
            "Equality on single bits" {
                r#"(step t1 (cl (= (= x y) (= (- (+ ((_ int_of 0) x) 0) (+ ((_ int_of 0) y) 0)) 0))) :rule pbblast_bvsle :args (x y))"#: true,
            }
        }
    }
    #[test]
    fn pbblast_pbbvar() {
        test_cases! {
           definitions = "
                (declare-const x (_ BitVec 1))
                (declare-const y (_ BitVec 1))
                ",
            "Equality on single bits" {
                r#"(step t1 (cl (= (= x y) (= (- (+ ((_ int_of 0) x) 0) (+ ((_ int_of 0) y) 0)) 0))) :rule pbblast_pbbvar :args (x y))"#: true,
            }
        }
    }
    #[test]
    fn pbblast_pbbconst() {
        test_cases! {
           definitions = "
                (declare-const x (_ BitVec 1))
                (declare-const y (_ BitVec 1))
                ",
            "Equality on single bits" {
                r#"(step t1 (cl (= (= x y) (= (- (+ ((_ int_of 0) x) 0) (+ ((_ int_of 0) y) 0)) 0))) :rule pbblast_pbbconst :args (x y))"#: true,
            }
        }
    }
    #[test]
    fn pbblast_bvxor() {
        test_cases! {
           definitions = "
                (declare-const x (_ BitVec 1))
                (declare-const y (_ BitVec 1))
                ",
            "Equality on single bits" {
                r#"(step t1 (cl (= (= x y) (= (- (+ ((_ int_of 0) x) 0) (+ ((_ int_of 0) y) 0)) 0))) :rule pbblast_bvxor :args (x y))"#: true,
            }
        }
    }
    #[test]
    fn pbblast_bvand() {
        test_cases! {
           definitions = "
                (declare-const x (_ BitVec 1))
                (declare-const y (_ BitVec 1))
                ",
            "Equality on single bits" {
                r#"(step t1 (cl (= (= x y) (= (- (+ ((_ int_of 0) x) 0) (+ ((_ int_of 0) y) 0)) 0))) :rule pbblast_bvand :args (x y))"#: true,
            }
        }
    }
}
