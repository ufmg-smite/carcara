use std::ops::Range;

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
    range: &Range<usize>,
) -> RuleResult {
    // Obtain the bitvector width from the pool.
    let Sort::BitVec(width) = pool.sort(bitvector).as_sort().cloned().unwrap() else {
        unreachable!();
    };

    // The `range` must be the same length as the `sum`, but may be less than `width`
    let width = width.to_usize().unwrap();

    // Drop the last element, which is the constant zero
    let sum = &sum[..sum.len() - 1];

    // The summation must have at most as many summands as the bitvector has bits.
    rassert!(width >= sum.len(), CheckerError::Unspecified);

    // The summation must have as many summands as the range has element.
    rassert!(range.len() == sum.len(), CheckerError::Unspecified);

    for (i, element) in range.clone().zip(sum.iter()) {
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
    range: Option<Range<usize>>,
) -> RuleResult {
    let range = range.unwrap_or(0..(left_sum.len() - 1));
    check_pbblast_sum(pool, left_bv, left_sum, &range)?;
    check_pbblast_sum(pool, right_bv, right_sum, &range)
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
    check_pbblast_constraint(pool, x, y, sum_x, sum_y, None)
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
    check_pbblast_constraint(pool, y, x, sum_y, sum_x, None)
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
    check_pbblast_constraint(pool, x, y, sum_x, sum_y, None)
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

    check_pbblast_constraint(pool, x, y, sum_x, sum_y, None)
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

    check_pbblast_constraint(pool, x, y, sum_x, sum_y, None)
}

pub fn pbblast_bvslt(RuleArgs { pool, conclusion, .. }: RuleArgs) -> RuleResult {
    let ((x, y), (((sum_y, sign_y), (sign_x, sum_x)), constant)) = match_term_err!((= (bvslt x y) (>= (+ (- (+ ...) sign_y) (- sign_x (+ ...))) constant)) = &conclusion[0])?;

    // Range from 0 to n-2
    let the_range = 0..(sum_y.len() - 1);

    // Check that the constant is 1
    let constant: Integer = constant.as_integer_err()?;
    rassert!(constant == 1, CheckerError::Unspecified);

    // TODO: Check the signs
    // sign_y=(* 2 ((_ int_of 0) y2)) sign_x=(* 2 ((_ int_of 0) x2))
    println!("sign_y={sign_y} sign_x={sign_x}");

    // TODO: Pass `tail y` and `tail x` to the function
    // For bvult the summations occur in reverse: the "left" sum comes from y and the "right" from x.
    check_pbblast_constraint(pool, y, x, sum_y, sum_x, Some(the_range))
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

pub fn pbblast_pbbvar(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    let (x, pbs) = match_term_err!((= x (pbbterm ...)) = &conclusion[0])?;

    for (i, pb) in pbs.iter().enumerate() {
        let (idx, bv) = match_term_err!(((_ int_of idx) bv) = pb)?;

        // Convert the index term to an integer.
        let idx: Integer = idx.as_integer_err()?;

        // Check that the index is `i`.
        rassert!(idx == i, CheckerError::Unspecified);
        // Finally, the bitvector in the summand must be the one we expect.
        rassert!(*bv == *x, CheckerError::Unspecified);
    }
    Ok(())
}

pub fn pbblast_pbbconst(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    let ((r, bv_const), pbs) = match_term_err!((= (= r bv_const) (and ...)) = &conclusion[0])?;

    // Drop the last element of conjunctions, which is the constant `true`
    let pbs = &pbs[..pbs.len() - 1];

    // Iterate on bits of bv, check and list
    // ? let bv = match_term_err!((_ bv1 bv) = bv)?;
    println!("r={r}");
    println!("bv_const={bv_const}");
    println!("pbs:");
    for (i, pb) in pbs.iter().enumerate() {
        print!("{i}:{pb} ");
        let ((idx, bv), bit) = match_term_err!((= ((_ int_of idx) bv) bit) = pb)?;
        // Convert the index term to an integer.
        let idx: Integer = idx.as_integer_err()?;

        // TODO get ith bit from bv_const e.g. "(_ bv1 1)"
        println!("=> {bv}[{idx}] = {bit}, check that {bit} is {bv_const}[{idx}]...");
    }
    println!();

    Ok(())
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
                                 (= (- (+ (* 1 ((_ int_of 1) x2))
                                         (* 2 ((_ int_of 0) x2)) 0)
                                       (+ (* 1 ((_ int_of 1) y2))
                                          (* 2 ((_ int_of 0) y2)) 0))
                                    0))) :rule pbblast_bveq)"#: true,
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
                                 (= (- (+ (* 1  ((_ int_of 7) x8))
                                         (* 2   ((_ int_of 6) x8))
                                         (* 4   ((_ int_of 5) x8))
                                         (* 8   ((_ int_of 4) x8))
                                         (* 16  ((_ int_of 3) x8))
                                         (* 32  ((_ int_of 2) x8))
                                         (* 64  ((_ int_of 1) x8))
                                         (* 128 ((_ int_of 0) x8))
                                         0)
                                     (+ (* 1   ((_ int_of 7) y8))
                                        (* 2   ((_ int_of 6) y8))
                                        (* 4   ((_ int_of 5) y8))
                                        (* 8   ((_ int_of 4) y8))
                                        (* 16  ((_ int_of 3) y8))
                                        (* 32  ((_ int_of 2) y8))
                                        (* 64  ((_ int_of 1) y8))
                                        (* 128 ((_ int_of 0) y8))
                                        0))
                                0))) :rule pbblast_bveq)"#: true,
            }

            // The correct encoding is:
            // (bveq x8 y8) -> (- (sum_x8) (sum_y8)) == 0
            // We introduce a wrong coefficient (63 instead of 64).
            "bveq wrong coefficient in x8" {
                r#"(step t1 (cl (= (= x8 y8)
                                 (= (- (+ (* 1  ((_ int_of 7) x8))
                                         (* 2   ((_ int_of 6) x8))
                                         (* 4   ((_ int_of 5) x8))
                                         (* 8   ((_ int_of 4) x8))
                                         (* 16  ((_ int_of 3) x8))
                                         (* 32  ((_ int_of 2) x8))
                                         (* 63  ((_ int_of 1) x8))  ; WRONG: should be (* 64 ((_ int_of 1) x8))
                                         (* 128 ((_ int_of 0) x8))
                                         0)
                                      (+ (* 1   ((_ int_of 7) y8))
                                         (* 2   ((_ int_of 6) y8))
                                         (* 4   ((_ int_of 5) y8))
                                         (* 8   ((_ int_of 4) y8))
                                         (* 16  ((_ int_of 3) y8))
                                         (* 32  ((_ int_of 2) y8))
                                         (* 64  ((_ int_of 1) y8))
                                         (* 128 ((_ int_of 0) y8))
                                         0))
                                 0))) :rule pbblast_bveq)"#: false,
            }

            // The correct encoding is:
            // (bveq x8 y8) -> (- (sum_x8) (sum_y8)) == 0
            // We introduce a wrong constant (1 instead of 0).
            "bveq wrong constant in equality" {
                r#"(step t1 (cl (= (= x8 y8)
                                 (= (- (+ (* 1  ((_ int_of 7) x8))
                                         (* 2   ((_ int_of 6) x8))
                                         (* 4   ((_ int_of 5) x8))
                                         (* 8   ((_ int_of 4) x8))
                                         (* 16  ((_ int_of 3) x8))
                                         (* 32  ((_ int_of 2) x8))
                                         (* 64  ((_ int_of 1) x8))
                                         (* 128 ((_ int_of 0) x8))
                                         0)
                                      (+ (* 1   ((_ int_of 7) y8))
                                         (* 2   ((_ int_of 6) y8))
                                         (* 4   ((_ int_of 5) y8))
                                         (* 8   ((_ int_of 4) y8))
                                         (* 16  ((_ int_of 3) y8))
                                         (* 32  ((_ int_of 2) y8))
                                         (* 64  ((_ int_of 1) y8))
                                         (* 128 ((_ int_of 0) y8))
                                         0))
                                 1))) :rule pbblast_bveq)"#: false,
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
                                 (>= (- (+ (* 1 ((_ int_of 1) y2)) (* 2 ((_ int_of 0) y2)) 0)
                                        (+ (* 1 ((_ int_of 1) x2)) (* 2 ((_ int_of 0) x2)) 0))
                                     1))) :rule pbblast_bvult)"#: true,
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
                                 (>= (- (+ (* 1 ((_ int_of 7) y8))
                                         (* 2   ((_ int_of 6) y8))
                                         (* 4   ((_ int_of 5) y8))
                                         (* 8   ((_ int_of 4) y8))
                                         (* 16  ((_ int_of 3) y8))
                                         (* 32  ((_ int_of 2) y8))
                                         (* 64  ((_ int_of 1) y8))
                                         (* 128 ((_ int_of 0) y8))
                                         0)
                                      (+ (* 1   ((_ int_of 7) x8))
                                         (* 2   ((_ int_of 6) x8))
                                         (* 4   ((_ int_of 5) x8))
                                         (* 8   ((_ int_of 4) x8))
                                         (* 16  ((_ int_of 3) x8))
                                         (* 32  ((_ int_of 2) x8))
                                         (* 64  ((_ int_of 1) x8))
                                         (* 128 ((_ int_of 0) x8))
                                         0))
                                 1))) :rule pbblast_bvult)"#: true,
            }

            // Incorrect constant: should be 1, but here 0 is used.
            "bvult on 8-bit bitvectors (incorrect constant)" {
                r#"(step t1 (cl (= (bvult x8 y8)
                                 (>= (- (+ (* 1 ((_ int_of 7) y8))
                                         (* 2   ((_ int_of 6) y8))
                                         (* 4   ((_ int_of 5) y8))
                                         (* 8   ((_ int_of 4) y8))
                                         (* 16  ((_ int_of 3) y8))
                                         (* 32  ((_ int_of 2) y8))
                                         (* 64  ((_ int_of 1) y8))
                                         (* 128 ((_ int_of 0) y8))
                                         0)
                                      (+ (* 1   ((_ int_of 7) x8))
                                         (* 2   ((_ int_of 6) x8))
                                         (* 4   ((_ int_of 5) x8))
                                         (* 8   ((_ int_of 4) x8))
                                         (* 16  ((_ int_of 3) x8))
                                         (* 32  ((_ int_of 2) x8))
                                         (* 64  ((_ int_of 1) x8))
                                         (* 128 ((_ int_of 0) x8))
                                         0))
                                 0))) :rule pbblast_bvult)"#: false,
            }

            // For bvult the correct encoding is:
            //   (- (sum_y8) (sum_x8)) >= 1
            // Here we deliberately use 63 instead of 64 for the summand corresponding to index 1 (bit position 6).
            "bvult wrong coefficient" {
                r#"(step t1 (cl (= (bvult x8 y8)
                                 (>= (- (+ (* 1 ((_ int_of 7) y8))
                                         (* 2   ((_ int_of 6) y8))
                                         (* 4   ((_ int_of 5) y8))
                                         (* 8   ((_ int_of 4) y8))
                                         (* 16  ((_ int_of 3) y8))
                                         (* 32  ((_ int_of 2) y8))
                                         (* 63  ((_ int_of 1) y8))  ; WRONG: should be (* 64 ((_ int_of 1) y8))
                                         (* 128 ((_ int_of 0) y8))
                                         0)
                                      (+ (* 1   ((_ int_of 7) x8))
                                         (* 2   ((_ int_of 6) x8))
                                         (* 4   ((_ int_of 5) x8))
                                         (* 8   ((_ int_of 4) x8))
                                         (* 16  ((_ int_of 3) x8))
                                         (* 32  ((_ int_of 2) x8))
                                         (* 64  ((_ int_of 1) x8))
                                         (* 128 ((_ int_of 0) x8))
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
                                 (>= (- (+ (* 1 ((_ int_of 1) x2)) (* 2 ((_ int_of 0) x2)) 0)
                                        (+ (* 1 ((_ int_of 1) y2)) (* 2 ((_ int_of 0) y2)) 0))
                                     1))) :rule pbblast_bvugt)"#: true,
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
                                 (>= (- (+ (* 1 ((_ int_of 7) x8))
                                         (* 2   ((_ int_of 6) x8))
                                         (* 4   ((_ int_of 5) x8))
                                         (* 8   ((_ int_of 4) x8))
                                         (* 16  ((_ int_of 3) x8))
                                         (* 32  ((_ int_of 2) x8))
                                         (* 64  ((_ int_of 1) x8))
                                         (* 128 ((_ int_of 0) x8))
                                         0)
                                      (+ (* 1   ((_ int_of 7) y8))
                                         (* 2   ((_ int_of 6) y8))
                                         (* 4   ((_ int_of 5) y8))
                                         (* 8   ((_ int_of 4) y8))
                                         (* 16  ((_ int_of 3) y8))
                                         (* 32  ((_ int_of 2) y8))
                                         (* 64  ((_ int_of 1) y8))
                                         (* 128 ((_ int_of 0) y8))
                                         0))
                                 1))) :rule pbblast_bvugt)"#: true,
            }

            // Incorrect constant: should be 1, but here 0 is used.
            "bvugt on 8-bit bitvectors (incorrect constant)" {
                r#"(step t1 (cl (= (bvugt x8 y8)
                                 (>= (- (+ (* 1 ((_ int_of 7) x8))
                                         (* 2   ((_ int_of 6) x8))
                                         (* 4   ((_ int_of 5) x8))
                                         (* 8   ((_ int_of 4) x8))
                                         (* 16  ((_ int_of 3) x8))
                                         (* 32  ((_ int_of 2) x8))
                                         (* 64  ((_ int_of 1) x8))
                                         (* 128 ((_ int_of 0) x8))
                                         0)
                                      (+ (* 1   ((_ int_of 7) y8))
                                         (* 2   ((_ int_of 6) y8))
                                         (* 4   ((_ int_of 5) y8))
                                         (* 8   ((_ int_of 4) y8))
                                         (* 16  ((_ int_of 3) y8))
                                         (* 32  ((_ int_of 2) y8))
                                         (* 64  ((_ int_of 1) y8))
                                         (* 128 ((_ int_of 0) y8))
                                         0))
                                 0))) :rule pbblast_bvugt)"#: false,
            }

            // For bvugt the correct encoding is:
            //   (- (sum_x8) (sum_y8)) >= 1
            // Here we deliberately use 63 instead of 64 for the summand corresponding to index 1 in x8.
            "bvugt wrong coefficient" {
                r#"(step t1 (cl (= (bvugt x8 y8)
                                 (>= (- (+ (* 1 ((_ int_of 7) x8))
                                         (* 2   ((_ int_of 6) x8))
                                         (* 4   ((_ int_of 5) x8))
                                         (* 8   ((_ int_of 4) x8))
                                         (* 16  ((_ int_of 3) x8))
                                         (* 32  ((_ int_of 2) x8))
                                         (* 63  ((_ int_of 1) x8))  ; WRONG: should be (* 64 ((_ int_of 1) x8))
                                         (* 128 ((_ int_of 0) x8))
                                         0)
                                      (+ (* 1   ((_ int_of 7) y8))
                                         (* 2   ((_ int_of 6) y8))
                                         (* 4   ((_ int_of 5) y8))
                                         (* 8   ((_ int_of 4) y8))
                                         (* 16  ((_ int_of 3) y8))
                                         (* 32  ((_ int_of 2) y8))
                                         (* 64  ((_ int_of 1) y8))
                                         (* 128 ((_ int_of 0) y8))
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
                                 (>= (- (+ (* 1 ((_ int_of 1) x2)) (* 2 ((_ int_of 0) x2)) 0)
                                        (+ (* 1 ((_ int_of 1) y2)) (* 2 ((_ int_of 0) y2)) 0))
                                     0))) :rule pbblast_bvuge)"#: true,
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
                                 (>= (- (+ (* 1 ((_ int_of 7) x8))
                                         (* 2   ((_ int_of 6) x8))
                                         (* 4   ((_ int_of 5) x8))
                                         (* 8   ((_ int_of 4) x8))
                                         (* 16  ((_ int_of 3) x8))
                                         (* 32  ((_ int_of 2) x8))
                                         (* 64  ((_ int_of 1) x8))
                                         (* 128 ((_ int_of 0) x8))
                                         0)
                                      (+ (* 1   ((_ int_of 7) y8))
                                         (* 2   ((_ int_of 6) y8))
                                         (* 4   ((_ int_of 5) y8))
                                         (* 8   ((_ int_of 4) y8))
                                         (* 16  ((_ int_of 3) y8))
                                         (* 32  ((_ int_of 2) y8))
                                         (* 64  ((_ int_of 1) y8))
                                         (* 128 ((_ int_of 0) y8))
                                         0))
                                 0))) :rule pbblast_bvuge)"#: true,
            }

            // Incorrect constant: should be 0, but here 1 is used.
            "bvuge on 8-bit bitvectors (incorrect constant)" {
                r#"(step t1 (cl (= (bvuge x8 y8)
                                 (>= (- (+ (* 1 ((_ int_of 7) x8))
                                         (* 2   ((_ int_of 6) x8))
                                         (* 4   ((_ int_of 5) x8))
                                         (* 8   ((_ int_of 4) x8))
                                         (* 16  ((_ int_of 3) x8))
                                         (* 32  ((_ int_of 2) x8))
                                         (* 64  ((_ int_of 1) x8))
                                         (* 128 ((_ int_of 0) x8))
                                         0)
                                      (+ (* 1   ((_ int_of 7) y8))
                                         (* 2   ((_ int_of 6) y8))
                                         (* 4   ((_ int_of 5) y8))
                                         (* 8   ((_ int_of 4) y8))
                                         (* 16  ((_ int_of 3) y8))
                                         (* 32  ((_ int_of 2) y8))
                                         (* 64  ((_ int_of 1) y8))
                                         (* 128 ((_ int_of 0) y8))
                                         0))
                                 1))) :rule pbblast_bvuge)"#: false,
            }

            // For bvuge the correct encoding is:
            //   (- (sum_x8) (sum_y8)) >= 0
            // Here we deliberately use 63 instead of 64 for one of the summands in x8.
            "bvuge wrong coefficient" {
                r#"(step t1 (cl (= (bvuge x8 y8)
                                 (>= (- (+ (* 1 ((_ int_of 7) x8))
                                         (* 2   ((_ int_of 6) x8))
                                         (* 4   ((_ int_of 5) x8))
                                         (* 8   ((_ int_of 4) x8))
                                         (* 16  ((_ int_of 3) x8))
                                         (* 32  ((_ int_of 2) x8))
                                         (* 63  ((_ int_of 1) x8))  ; WRONG: should be (* 64 ((_ int_of 1) x8))
                                         (* 128 ((_ int_of 0) x8))
                                         0)
                                      (+ (* 1   ((_ int_of 7) y8))
                                         (* 2   ((_ int_of 6) y8))
                                         (* 4   ((_ int_of 5) y8))
                                         (* 8   ((_ int_of 4) y8))
                                         (* 16  ((_ int_of 3) y8))
                                         (* 32  ((_ int_of 2) y8))
                                         (* 64  ((_ int_of 1) y8))
                                         (* 128 ((_ int_of 0) y8))
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
                                 (>= (- (+ (* 1 ((_ int_of 1) y2)) (* 2 ((_ int_of 0) y2)) 0)
                                        (+ (* 1 ((_ int_of 1) x2)) (* 2 ((_ int_of 0) x2)) 0))
                                     0))) :rule pbblast_bvule)"#: true,
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
                                 (>= (- (+ (* 1 ((_ int_of 7) y8))
                                         (* 2   ((_ int_of 6) y8))
                                         (* 4   ((_ int_of 5) y8))
                                         (* 8   ((_ int_of 4) y8))
                                         (* 16  ((_ int_of 3) y8))
                                         (* 32  ((_ int_of 2) y8))
                                         (* 64  ((_ int_of 1) y8))
                                         (* 128 ((_ int_of 0) y8))
                                         0)
                                      (+ (* 1   ((_ int_of 7) x8))
                                         (* 2   ((_ int_of 6) x8))
                                         (* 4   ((_ int_of 5) x8))
                                         (* 8   ((_ int_of 4) x8))
                                         (* 16  ((_ int_of 3) x8))
                                         (* 32  ((_ int_of 2) x8))
                                         (* 64  ((_ int_of 1) x8))
                                         (* 128 ((_ int_of 0) x8))
                                         0))
                                 0))) :rule pbblast_bvule)"#: true,
            }

            // Incorrect constant: should be 0, but here 1 is used.
            "bvule on 8-bit bitvectors (incorrect constant)" {
                r#"(step t1 (cl (= (bvule x8 y8)
                                 (>= (- (+ (* 1 ((_ int_of 7) y8))
                                         (* 2   ((_ int_of 6) y8))
                                         (* 4   ((_ int_of 5) y8))
                                         (* 8   ((_ int_of 4) y8))
                                         (* 16  ((_ int_of 3) y8))
                                         (* 32  ((_ int_of 2) y8))
                                         (* 64  ((_ int_of 1) y8))
                                         (* 128 ((_ int_of 0) y8))
                                         0)
                                      (+ (* 1   ((_ int_of 7) x8))
                                         (* 2   ((_ int_of 6) x8))
                                         (* 4   ((_ int_of 5) x8))
                                         (* 8   ((_ int_of 4) x8))
                                         (* 16  ((_ int_of 3) x8))
                                         (* 32  ((_ int_of 2) x8))
                                         (* 64  ((_ int_of 1) x8))
                                         (* 128 ((_ int_of 0) x8))
                                         0))
                                 1))) :rule pbblast_bvule)"#: false,
            }

            // For bvule the correct encoding is:
            //   (- (sum_y8) (sum_x8)) >= 0
            // Here we deliberately use 63 instead of 64 for one of the summands in y8.
            "bvule wrong coefficient" {
                r#"(step t1 (cl (= (bvule x8 y8)
                                 (>= (- (+ (* 1 ((_ int_of 7) y8))
                                         (* 2   ((_ int_of 6) y8))
                                         (* 4   ((_ int_of 5) y8))
                                         (* 8   ((_ int_of 4) y8))
                                         (* 16  ((_ int_of 3) y8))
                                         (* 32  ((_ int_of 2) y8))
                                         (* 63  ((_ int_of 1) y8))  ; WRONG: should be (* 64 ((_ int_of 1) y8))
                                         (* 128 ((_ int_of 0) y8))
                                         0)
                                      (+ (* 1   ((_ int_of 7) x8))
                                         (* 2   ((_ int_of 6) x8))
                                         (* 4   ((_ int_of 5) x8))
                                         (* 8   ((_ int_of 4) x8))
                                         (* 16  ((_ int_of 3) x8))
                                         (* 32  ((_ int_of 2) x8))
                                         (* 64  ((_ int_of 1) x8))
                                         (* 128 ((_ int_of 0) x8))
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
                                            (+ (* 1 ((_ int_of 1) y2)) 0)   ; y sum
                                            (* 2 ((_ int_of 0) y2))         ; y sign
                                        )
                                        (-
                                            (* 2 ((_ int_of 0) x2))         ; x sign
                                            (+ (* 1 ((_ int_of 1) x2)) 0)   ; x sum
                                        )
                                    ) 1))) :rule pbblast_bvslt)"#: true,
            }

            // Omitting the explicit multiplication by 1 in the sum parts.
            "bvslt on two bits omitting multiplication by 1 in sum parts" {
                r#"(step t1 (cl (= (bvslt x2 y2)
                                (>= (+
                                        (-
                                            (+ ((_ int_of 1) y2) 0)               ; y sum omitted "* 1"
                                            (* 2 ((_ int_of 0) y2))
                                        )
                                        (-
                                            (* 2 ((_ int_of 0) x2))
                                            (+ ((_ int_of 1) x2) 0)               ; x sum omitted "* 1"
                                        )
                                    ) 1))) :rule pbblast_bvslt)"#: true,
            }

            // Wrong scalar of the sign bit
            "bvslt on two bits wrong scalar of the sign bit" {
                r#"(step t1 (cl (= (bvslt x2 y2)
                                (>= (+
                                        (-
                                            ((_ int_of 1) y2)
                                            (* 1 ((_ int_of 0) y2))         ; should be * 2
                                        )
                                        (-
                                            (* 2 ((_ int_of 0) x2))
                                            ((_ int_of 1) x2)
                                        )
                                    ) 1))) :rule pbblast_bvslt)"#: false,
            }

            // Wrong indexing of the summation term
            "bvslt on two bits with wrong indexing of the summation term" {
                r#"(step t1 (cl (= (bvslt x2 y2)
                                (>= (+
                                        (-
                                            (+ (* 1 ((_ int_of 0) y2)) 0)   ; should be int_of 1
                                            (* 2 ((_ int_of 0) y2))
                                        )
                                        (-
                                            (* 2 ((_ int_of 0) x2))
                                            (+ (* 1 ((_ int_of 1) x2)) 0)
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
                                            (+ (* 1 ((_ int_of 3) y4))
                                               (* 2 ((_ int_of 2) y4))
                                               (* 4 ((_ int_of 1) y4))
                                               0)
                                            (* 8 ((_ int_of 0) y4)))
                                        (-
                                            (* 8 ((_ int_of 0) x4))
                                            (+ (* 1 ((_ int_of 3) x4))
                                               (* 2 ((_ int_of 2) x4))
                                               (* 4 ((_ int_of 1) x4))
                                               0)
                                        )
                                    ) 1))) :rule pbblast_bvslt)"#: true,
            }

            // Omitting explicit multiplication by 1 in the sum parts.
            "bvslt on 4 bits omitting multiplication by 1 in sum parts" {
                r#"(step t1 (cl (= (bvslt x4 y4)
                                (>= (+
                                        (-
                                            (+ ((_ int_of 3) y4)
                                               (* 2 ((_ int_of 2) y4))
                                               (* 4 ((_ int_of 1) y4))
                                               0)
                                            (* 8 ((_ int_of 0) y4)))
                                        (-
                                            (* 8 ((_ int_of 0) x4))
                                            (+ ((_ int_of 3) x4)
                                               (* 2 ((_ int_of 2) x4))
                                               (* 4 ((_ int_of 1) x4))
                                               0)
                                        )
                                    ) 1))) :rule pbblast_bvslt)"#: true,
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
    fn pbblast_pbbvar_1() {
        test_cases! {
           definitions = "
                (declare-const x (_ BitVec 1))
                (declare-const y (_ BitVec 1))
                ",
            // No restriction, only create a vector of pseudo-boolean variables that are free
            "pbbvar on single bits" {
                r#"(step t1 (cl (= x (pbbterm ((_ int_of 0) x)))) :rule pbblast_pbbvar)"#: true,
                r#"(step t1 (cl (= x (pbbterm ((_ int_of 1) x)))) :rule pbblast_pbbvar)"#: false, // Wrong index
                r#"(step t1 (cl (= x (pbbterm ((_ int_of 0) y)))) :rule pbblast_pbbvar)"#: false, // Mismatched vectors
                r#"(step t1 (cl (= y (pbbterm ((_ int_of 0) x)))) :rule pbblast_pbbvar)"#: false, // Mismatched vectors
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
                r#"(step t1 (cl (= x2 (pbbterm ((_ int_of 0) x2) ((_ int_of 1) x2)))) :rule pbblast_pbbvar)"#: true,
            }
            // ! parser error during test "Mismatched term count": parser error: sort error: expected '(_ BitVec 2)', got '(_ BitVec 1)'
            // "Invalid 2-bit pbbvar (wrong index)" {
            //     r#"(step t1 (cl (= x2 (pbbterm ((_ int_of 2) x2) ((_ int_of 1) x2)))) :rule pbblast_pbbvar)"#: false,
            // }
            // ! parser error during test "Mismatched term count": parser error: sort error: expected '(_ BitVec 2)', got '(_ BitVec 1)'
            // "Mismatched term count" {
            //     r#"(step t1 (cl (= x2 (pbbterm ((_ int_of 0) x2)))) :rule pbblast_pbbvar"#: false,
            // }
            "Mixed variables" {
                r#"(step t1 (cl (= x2 (pbbterm ((_ int_of 0) x2) ((_ int_of 1) y2)))) :rule pbblast_pbbvar)"#: false,
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
                r#"(step t1 (cl (= x8 (pbbterm
                    ((_ int_of 0) x8) ((_ int_of 1) x8)
                    ((_ int_of 2) x8) ((_ int_of 3) x8)
                    ((_ int_of 4) x8) ((_ int_of 5) x8)
                    ((_ int_of 6) x8) ((_ int_of 7) x8)
                ))) :rule pbblast_pbbvar)"#: true,
            }

            "Invalid 8-bit (missing term)" {
                r#"(step t1 (cl (= x8 (pbbterm
                    ((_ int_of 0) x8) ((_ int_of 1) x8)
                    ((_ int_of 2) x8) ((_ int_of 3) x8)
                    ((_ int_of 4) x8) ((_ int_of 5) x8)
                    ((_ int_of 6) x8) ((_ int_of 6) x8) ;; index 6 twice
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
                r#"(step t1 (cl (= (= r #b1)
                              (and (= ((_ int_of 0) r) 1) true))) 
                      :rule pbblast_pbbconst)"#: true,
            }
            "Invalid 1-bit value" {
                r#"(step t1 (cl (= (= r #b1)
                              (and (= ((_ int_of 0) r) 0) true)))
                      :rule pbblast_pbbconst)"#: false,
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
                r#"(step t1 (cl (= (= r #b10)
                              (and 
                                (= ((_ int_of 0) r) 0)  ; LSB
                                (= ((_ int_of 1) r) 1)  ; MSB
                                true))) 
                      :rule pbblast_pbbconst)"#: true,
            }
            "Invalid bit order" {
                r#"(step t1 (cl (= (= r #b10)
                              (and 
                                (= ((_ int_of 1) r) 0)  ; Swapped indices
                                (= ((_ int_of 0) r) 1)
                                true))) 
                      :rule pbblast_pbbconst)"#: false,
            }
        }
    }

    #[test]
    fn pbblast_pbbconst_4() {
        test_cases! {
           definitions = "
                (declare-const r (_ BitVec 4))
                ",
            // Consider a constant bitvector like #b0111, we blast the restrictions for each bit
            "pbbconst on single bits" {
                r#"(step t1 (cl (=
                                  (= r #b0111)
                                  (and  ; list of bit restrictions
                                    (= ((_ int_of 0) r) 1)
                                    (= ((_ int_of 1) r) 1)
                                    (= ((_ int_of 2) r) 1)
                                    (= ((_ int_of 3) r) 0)
                                    true ; end of list
                                  )
                                )) :rule pbblast_pbbconst)"#: true,
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
                r#"(step t1 (cl (= (= r #b11110000)
                              (and
                                (= ((_ int_of 0) r) 0)  ; Bit 0 (LSB)
                                (= ((_ int_of 1) r) 0)
                                (= ((_ int_of 2) r) 0)
                                (= ((_ int_of 3) r) 0)
                                (= ((_ int_of 4) r) 1)
                                (= ((_ int_of 5) r) 1)
                                (= ((_ int_of 6) r) 1)
                                (= ((_ int_of 7) r) 1)  ; Bit 7 (MSB)
                                true))) 
                      :rule pbblast_pbbconst)"#: true,
            }
            "Missing bit constraint" {
                r#"(step t1 (cl (= (= r #b11110000)
                              (and
                                (= ((_ int_of 0) r) 0)
                                (= ((_ int_of 1) r) 0)
                                (= ((_ int_of 2) r) 0)
                                (= ((_ int_of 4) r) 1)  ; Missing bit 3
                                (= ((_ int_of 5) r) 1)
                                (= ((_ int_of 6) r) 1)
                                (= ((_ int_of 7) r) 1)
                                true))) 
                      :rule pbblast_pbbconst)"#: false,
            }
        }
    }

    #[test]
    fn pbblast_bvxor_1() {
        test_cases! {
           definitions = "
                (declare-const x1 (_ BitVec 1))
                (declare-const y1 (_ BitVec 1))
                (declare-const r1 (_ BitVec 1))
                ",
            "Valid 1-bit XOR" {
                r#"(step t1 (cl (and (= (bvxor x1 y1) r1)
                                (and        ; list of constraints for each bit terminating on `true`
                                    (and    ; i = 0
                                        (>= (- (+ ((_ int_of 0) x1) ((_ int_of 0) y1)) ((_ int_of 0) r1)) 0)    ; (xi + yi) - ri >= 0
                                        (>= (- 0 (+ ((_ int_of 0) r1) ((_ int_of 0) x1) ((_ int_of 0) y1))) -2) ; 0 - (ri + xi + yi) >= -2
                                        (>= (- (+ ((_ int_of 0) r1) ((_ int_of 0) x1)) ((_ int_of 0) y1)) 0)    ; (ri + xi) - yi >= 0
                                        (>= (- (+ ((_ int_of 0) r1) ((_ int_of 0) y1)) ((_ int_of 0) x1)) 0)    ; (ri + yi) - xi >= 0
                                    )
                                    true    ; end of list
                                ))
                        ) :rule pbblast_bvxor)"#: true,
            }
            "Invalid 1-bit XOR (missing constraint)" {
                r#"(step t1 (cl (and (= (bvxor x1 y1) r1)
                                (and
                                    (and ; i=0
                                        (>= (- (+ ((_ int_of 0) x1) ((_ int_of 0) y1)) ((_ int_of 0) r1)) 0)
                                        ;; Missing third constraint
                                        (>= (- (+ ((_ int_of 0) r1) ((_ int_of 0) y1)) ((_ int_of 0) x1)) 0)
                                    )
                                    true
                                ))
                        ) :rule pbblast_bvxor)"#: false,
            }
        }
    }

    #[test]
    fn pbblast_bvxor_2() {
        test_cases! {
            definitions = "
            (declare-const x2 (_ BitVec 2))
            (declare-const y2 (_ BitVec 2))
            (declare-const r2 (_ BitVec 2))
        ",
            "Valid 2-bit XOR" {
                r#"(step t1 (cl (and (= (bvxor x2 y2) r2)
                                (and
                                    (and ; i=0 (LSB)
                                        (>= (- (+ ((_ int_of 0) x2) ((_ int_of 0) y2)) ((_ int_of 0) r2)) 0)
                                        (>= (- 0 (+ ((_ int_of 0) r2) ((_ int_of 0) x2) ((_ int_of 0) y2))) -2)
                                        (>= (- (+ ((_ int_of 0) r2) ((_ int_of 0) x2)) ((_ int_of 0) y2)) 0)
                                        (>= (- (+ ((_ int_of 0) r2) ((_ int_of 0) y2)) ((_ int_of 0) x2)) 0)
                                    )
                                    (and ; i=1 (MSB)
                                        (>= (- (+ ((_ int_of 1) x2) ((_ int_of 1) y2)) ((_ int_of 1) r2)) 0)
                                        (>= (- 0 (+ ((_ int_of 1) r2) ((_ int_of 1) x2) ((_ int_of 1) y2))) -2)
                                        (>= (- (+ ((_ int_of 1) r2) ((_ int_of 1) x2)) ((_ int_of 1) y2)) 0)
                                        (>= (- (+ ((_ int_of 1) r2) ((_ int_of 1) y2)) ((_ int_of 1) x2)) 0)
                                    )
                                    true
                                ))
                        ) :rule pbblast_bvxor)"#: true,
            }

            "Invalid 2-bit XOR (wrong inequality bound)" {
                r#"(step t1 (cl (and (= (bvxor x2 y2) r2)
                                (and
                                    (and ; i=0
                                        (>= (- (+ ((_ int_of 0) x2) ((_ int_of 0) y2)) ((_ int_of 0) r2)) 0)
                                        (>= (- 0 (+ ((_ int_of 0) r2) ((_ int_of 0) x2) ((_ int_of 0) y2))) -1) ;; Should be -2
                                        (>= (- (+ ((_ int_of 0) r2) ((_ int_of 0) x2)) ((_ int_of 0) y2)) 0)
                                        (>= (- (+ ((_ int_of 0) r2) ((_ int_of 0) y2)) ((_ int_of 0) x2)) 0)
                                    )
                                    (and ; i=1
                                        (>= (- (+ ((_ int_of 1) x2) ((_ int_of 1) y2)) ((_ int_of 1) r2)) 0)
                                        (>= (- 0 (+ ((_ int_of 1) r2) ((_ int_of 1) x2) ((_ int_of 1) y2))) -2)
                                        (>= (- (+ ((_ int_of 1) r2) ((_ int_of 1) x2)) ((_ int_of 1) y2)) 0)
                                        (>= (- (+ ((_ int_of 1) r2) ((_ int_of 1) y2)) ((_ int_of 1) x2)) 0)
                                    )
                                    true
                                ))
                        ) :rule pbblast_bvxor)"#: false,
            }
        }
    }

    #[test]
    fn pbblast_bvxor_8() {
        test_cases! {
            definitions = "
            (declare-const x8 (_ BitVec 8))
            (declare-const y8 (_ BitVec 8))
            (declare-const r8 (_ BitVec 8))
        ",
            "Valid 8-bit XOR" {
                r#"(step t1 (cl (and (= (bvxor x8 y8) r8)
                                (and
                                    (and ; i=0 (LSB)
                                        (>= (- (+ ((_ int_of 0) x8) ((_ int_of 0) y8)) ((_ int_of 0) r8)) 0)
                                        (>= (- 0 (+ ((_ int_of 0) r8) ((_ int_of 0) x8) ((_ int_of 0) y8))) -2)
                                        (>= (- (+ ((_ int_of 0) r8) ((_ int_of 0) x8)) ((_ int_of 0) y8)) 0)
                                        (>= (- (+ ((_ int_of 0) r8) ((_ int_of 0) y8)) ((_ int_of 0) x8)) 0)
                                    )
                                    (and ; i=1
                                        (>= (- (+ ((_ int_of 1) x8) ((_ int_of 1) y8)) ((_ int_of 1) r8)) 0)
                                        (>= (- 0 (+ ((_ int_of 1) r8) ((_ int_of 1) x8) ((_ int_of 1) y8))) -2)
                                        (>= (- (+ ((_ int_of 1) r8) ((_ int_of 1) x8)) ((_ int_of 1) y8)) 0)
                                        (>= (- (+ ((_ int_of 1) r8) ((_ int_of 1) y8)) ((_ int_of 1) x8)) 0)
                                    )
                                    (and ; i=2
                                        (>= (- (+ ((_ int_of 2) x8) ((_ int_of 2) y8)) ((_ int_of 2) r8)) 0)
                                        (>= (- 0 (+ ((_ int_of 2) r8) ((_ int_of 2) x8) ((_ int_of 2) y8))) -2)
                                        (>= (- (+ ((_ int_of 2) r8) ((_ int_of 2) x8)) ((_ int_of 2) y8)) 0)
                                        (>= (- (+ ((_ int_of 2) r8) ((_ int_of 2) y8)) ((_ int_of 2) x8)) 0)
                                    )
                                    (and ; i=3 
                                        (>= (- (+ ((_ int_of 3) x8) ((_ int_of 3) y8)) ((_ int_of 3) r8)) 0)
                                        (>= (- 0 (+ ((_ int_of 3) r8) ((_ int_of 3) x8) ((_ int_of 3) y8))) -2)
                                        (>= (- (+ ((_ int_of 3) r8) ((_ int_of 3) x8)) ((_ int_of 3) y8)) 0)
                                        (>= (- (+ ((_ int_of 3) r8) ((_ int_of 3) y8)) ((_ int_of 3) x8)) 0)
                                    )
                                    (and ; i=4 
                                        (>= (- (+ ((_ int_of 4) x8) ((_ int_of 4) y8)) ((_ int_of 4) r8)) 0)
                                        (>= (- 0 (+ ((_ int_of 4) r8) ((_ int_of 4) x8) ((_ int_of 4) y8))) -2)
                                        (>= (- (+ ((_ int_of 4) r8) ((_ int_of 4) x8)) ((_ int_of 4) y8)) 0)
                                        (>= (- (+ ((_ int_of 4) r8) ((_ int_of 4) y8)) ((_ int_of 4) x8)) 0)
                                    )
                                    (and ; i=5 
                                        (>= (- (+ ((_ int_of 5) x8) ((_ int_of 5) y8)) ((_ int_of 5) r8)) 0)
                                        (>= (- 0 (+ ((_ int_of 5) r8) ((_ int_of 5) x8) ((_ int_of 5) y8))) -2)
                                        (>= (- (+ ((_ int_of 5) r8) ((_ int_of 5) x8)) ((_ int_of 5) y8)) 0)
                                        (>= (- (+ ((_ int_of 5) r8) ((_ int_of 5) y8)) ((_ int_of 5) x8)) 0)
                                    )
                                    (and ; i=6 
                                        (>= (- (+ ((_ int_of 6) x8) ((_ int_of 6) y8)) ((_ int_of 6) r8)) 0)
                                        (>= (- 0 (+ ((_ int_of 6) r8) ((_ int_of 6) x8) ((_ int_of 6) y8))) -2)
                                        (>= (- (+ ((_ int_of 6) r8) ((_ int_of 6) x8)) ((_ int_of 6) y8)) 0)
                                        (>= (- (+ ((_ int_of 6) r8) ((_ int_of 6) y8)) ((_ int_of 6) x8)) 0)
                                    )
                                    (and ; i=7 (MSB)
                                        (>= (- (+ ((_ int_of 7) x8) ((_ int_of 7) y8)) ((_ int_of 7) r8)) 0)
                                        (>= (- 0 (+ ((_ int_of 7) r8) ((_ int_of 7) x8) ((_ int_of 7) y8))) -2)
                                        (>= (- (+ ((_ int_of 7) r8) ((_ int_of 7) x8)) ((_ int_of 7) y8)) 0)
                                        (>= (- (+ ((_ int_of 7) r8) ((_ int_of 7) y8)) ((_ int_of 7) x8)) 0)
                                    )
                                    true
                                ))
                        ) :rule pbblast_bvxor)"#: true,
            }
            "Invalid 8-bit XOR (missing i=3)" {
                r#"(step t1 (cl (and (= (bvxor x8 y8) r8)
                                (and
                                    (and ; i=0 (LSB)
                                        (>= (- (+ ((_ int_of 0) x8) ((_ int_of 0) y8)) ((_ int_of 0) r8)) 0)
                                        (>= (- 0 (+ ((_ int_of 0) r8) ((_ int_of 0) x8) ((_ int_of 0) y8))) -2)
                                        (>= (- (+ ((_ int_of 0) r8) ((_ int_of 0) x8)) ((_ int_of 0) y8)) 0)
                                        (>= (- (+ ((_ int_of 0) r8) ((_ int_of 0) y8)) ((_ int_of 0) x8)) 0)
                                    )
                                    (and ; i=1
                                        (>= (- (+ ((_ int_of 1) x8) ((_ int_of 1) y8)) ((_ int_of 1) r8)) 0)
                                        (>= (- 0 (+ ((_ int_of 1) r8) ((_ int_of 1) x8) ((_ int_of 1) y8))) -2)
                                        (>= (- (+ ((_ int_of 1) r8) ((_ int_of 1) x8)) ((_ int_of 1) y8)) 0)
                                        (>= (- (+ ((_ int_of 1) r8) ((_ int_of 1) y8)) ((_ int_of 1) x8)) 0)
                                    )
                                    (and ; i=2
                                        (>= (- (+ ((_ int_of 2) x8) ((_ int_of 2) y8)) ((_ int_of 2) r8)) 0)
                                        (>= (- 0 (+ ((_ int_of 2) r8) ((_ int_of 2) x8) ((_ int_of 2) y8))) -2)
                                        (>= (- (+ ((_ int_of 2) r8) ((_ int_of 2) x8)) ((_ int_of 2) y8)) 0)
                                        (>= (- (+ ((_ int_of 2) r8) ((_ int_of 2) y8)) ((_ int_of 2) x8)) 0)
                                    )
                                    ; i=3 missing
                                    (and ; i=4 
                                        (>= (- (+ ((_ int_of 4) x8) ((_ int_of 4) y8)) ((_ int_of 4) r8)) 0)
                                        (>= (- 0 (+ ((_ int_of 4) r8) ((_ int_of 4) x8) ((_ int_of 4) y8))) -2)
                                        (>= (- (+ ((_ int_of 4) r8) ((_ int_of 4) x8)) ((_ int_of 4) y8)) 0)
                                        (>= (- (+ ((_ int_of 4) r8) ((_ int_of 4) y8)) ((_ int_of 4) x8)) 0)
                                    )
                                    (and ; i=5 
                                        (>= (- (+ ((_ int_of 5) x8) ((_ int_of 5) y8)) ((_ int_of 5) r8)) 0)
                                        (>= (- 0 (+ ((_ int_of 5) r8) ((_ int_of 5) x8) ((_ int_of 5) y8))) -2)
                                        (>= (- (+ ((_ int_of 5) r8) ((_ int_of 5) x8)) ((_ int_of 5) y8)) 0)
                                        (>= (- (+ ((_ int_of 5) r8) ((_ int_of 5) y8)) ((_ int_of 5) x8)) 0)
                                    )
                                    (and ; i=6 
                                        (>= (- (+ ((_ int_of 6) x8) ((_ int_of 6) y8)) ((_ int_of 6) r8)) 0)
                                        (>= (- 0 (+ ((_ int_of 6) r8) ((_ int_of 6) x8) ((_ int_of 6) y8))) -2)
                                        (>= (- (+ ((_ int_of 6) r8) ((_ int_of 6) x8)) ((_ int_of 6) y8)) 0)
                                        (>= (- (+ ((_ int_of 6) r8) ((_ int_of 6) y8)) ((_ int_of 6) x8)) 0)
                                    )
                                    (and ; i=7 (MSB)
                                        (>= (- (+ ((_ int_of 7) x8) ((_ int_of 7) y8)) ((_ int_of 7) r8)) 0)
                                        (>= (- 0 (+ ((_ int_of 7) r8) ((_ int_of 7) x8) ((_ int_of 7) y8))) -2)
                                        (>= (- (+ ((_ int_of 7) r8) ((_ int_of 7) x8)) ((_ int_of 7) y8)) 0)
                                        (>= (- (+ ((_ int_of 7) r8) ((_ int_of 7) y8)) ((_ int_of 7) x8)) 0)
                                    )
                                    true
                                ))
                        ) :rule pbblast_bvxor)"#: false,
            }
        }
    }

    #[test]
    fn pbblast_bvand_1() {
        test_cases! {
            definitions = "
            (declare-const x1 (_ BitVec 1))
            (declare-const y1 (_ BitVec 1))
            (declare-const r1 (_ BitVec 1))
        ",
            "Valid 1-bit AND" {
                r#"(step t1 (cl (and (= (bvand x1 y1) r1)
                                (and        ; list of constraints for each bit terminating on `true`
                                    (and    ; i = 0
                                        (>= (- ((_ int_of 0) x1) ((_ int_of 0) r1)) 0)                          ; xi - ri >= 0
                                        (>= (- ((_ int_of 0) y1) ((_ int_of 0) r1)) 0)                          ; yi - ri >= 0
                                        (>= (- ((_ int_of 0) r1) (+ ((_ int_of 0) x1) ((_ int_of 0) y1))) -1)   ; ri - (xi + yi) >= -1
                                    )
                                    true    ; end of list
                                ))
                        ) :rule pbblast_bvand)"#: true,
            }

            "Invalid 1-bit AND (missing constraint)" {
                r#"(step t1 (cl (and (= (bvand x1 y1) r1)
                                (and
                                    (and
                                        (>= (- ((_ int_of 0) x1) ((_ int_of 0) r1)) 0)
                                        ;; Missing y_i - r_i >= 0
                                        (>= (- ((_ int_of 0) r1) (+ ((_ int_of 0) x1) ((_ int_of 0) y1))) -1)
                                    )
                                    true
                                ))
                        ) :rule pbblast_bvand)"#: false,
            }
        }
    }

    #[test]
    fn pbblast_bvand_2() {
        test_cases! {
            definitions = "
            (declare-const x2 (_ BitVec 2))
            (declare-const y2 (_ BitVec 2))
            (declare-const r2 (_ BitVec 2))
        ",
            "Valid 2-bit AND" {
                r#"(step t1 (cl (and (= (bvand x2 y2) r2)
                                (and
                                    (and ; i=0
                                        (>= (- ((_ int_of 0) x2) ((_ int_of 0) r2)) 0)
                                        (>= (- ((_ int_of 0) y2) ((_ int_of 0) r2)) 0)
                                        (>= (- ((_ int_of 0) r2) (+ ((_ int_of 0) x2) ((_ int_of 0) y2))) -1)
                                    )
                                    (and ; i=1
                                        (>= (- ((_ int_of 1) x2) ((_ int_of 1) r2)) 0)
                                        (>= (- ((_ int_of 1) y2) ((_ int_of 1) r2)) 0)
                                        (>= (- ((_ int_of 1) r2) (+ ((_ int_of 1) x2) ((_ int_of 1) y2))) -1)
                                    )
                                    true
                                ))
                        ) :rule pbblast_bvand)"#: true,
            }

            "Invalid 2-bit AND (wrong coefficient)" {
                r#"(step t1 (cl (and (= (bvand x2 y2) r2)
                                (and
                                    (and ; i=0
                                        (>= (- ((_ int_of 0) x2) ((_ int_of 0) r2)) 0)
                                        (>= (- ((_ int_of 0) y2) (* 2 ((_ int_of 0) r2))) 0) ;; Invalid coefficient 2
                                        (>= (- ((_ int_of 0) r2) (+ ((_ int_of 0) x2) ((_ int_of 0) y2))) -1)
                                    )
                                    (and ; i=1
                                        (>= (- ((_ int_of 1) x2) ((_ int_of 1) r2)) 0)
                                        (>= (- ((_ int_of 1) y2) ((_ int_of 1) r2)) 0)
                                        (>= (- ((_ int_of 1) r2) (+ ((_ int_of 1) x2) ((_ int_of 1) y2))) -1)
                                    )
                                    true
                                ))
                        ) :rule pbblast_bvand)"#: false,
            }
        }
    }

    #[test]
    fn pbblast_bvand_8() {
        test_cases! {
            definitions = "
            (declare-const x8 (_ BitVec 8))
            (declare-const y8 (_ BitVec 8))
            (declare-const r8 (_ BitVec 8))
        ",
            "Valid 8-bit AND" {
                r#"(step t1 (cl (and (= (bvand x8 y8) r8)
                                (and
                                    (and ; i=0
                                        (>= (- ((_ int_of 0) x8) ((_ int_of 0) r8)) 0)
                                        (>= (- ((_ int_of 0) y8) ((_ int_of 0) r8)) 0)
                                        (>= (- ((_ int_of 0) r8) (+ ((_ int_of 0) x8) ((_ int_of 0) y8))) -1)
                                    )
                                    (and ; i=1
                                        (>= (- ((_ int_of 1) x8) ((_ int_of 1) r8)) 0)
                                        (>= (- ((_ int_of 1) y8) ((_ int_of 1) r8)) 0)
                                        (>= (- ((_ int_of 1) r8) (+ ((_ int_of 1) x8) ((_ int_of 1) y8))) -1)
                                    )
                                    (and ; i=2
                                        (>= (- ((_ int_of 2) x8) ((_ int_of 2) r8)) 0)
                                        (>= (- ((_ int_of 2) y8) ((_ int_of 2) r8)) 0)
                                        (>= (- ((_ int_of 2) r8) (+ ((_ int_of 2) x8) ((_ int_of 2) y8))) -1)
                                    )
                                    (and ; i=3
                                        (>= (- ((_ int_of 3) x8) ((_ int_of 3) r8)) 0)
                                        (>= (- ((_ int_of 3) y8) ((_ int_of 3) r8)) 0)
                                        (>= (- ((_ int_of 3) r8) (+ ((_ int_of 3) x8) ((_ int_of 3) y8))) -1)
                                    )
                                    (and ; i=4
                                        (>= (- ((_ int_of 4) x8) ((_ int_of 4) r8)) 0)
                                        (>= (- ((_ int_of 4) y8) ((_ int_of 4) r8)) 0)
                                        (>= (- ((_ int_of 4) r8) (+ ((_ int_of 4) x8) ((_ int_of 4) y8))) -1)
                                    )
                                    (and ; i=5
                                        (>= (- ((_ int_of 5) x8) ((_ int_of 5) r8)) 0)
                                        (>= (- ((_ int_of 5) y8) ((_ int_of 5) r8)) 0)
                                        (>= (- ((_ int_of 5) r8) (+ ((_ int_of 5) x8) ((_ int_of 5) y8))) -1)
                                    )
                                    (and ; i=6
                                        (>= (- ((_ int_of 6) x8) ((_ int_of 6) r8)) 0)
                                        (>= (- ((_ int_of 6) y8) ((_ int_of 6) r8)) 0)
                                        (>= (- ((_ int_of 6) r8) (+ ((_ int_of 6) x8) ((_ int_of 6) y8))) -1)
                                    )
                                    (and ; i=7 (MSB)
                                        (>= (- ((_ int_of 7) x8) ((_ int_of 7) r8)) 0)
                                        (>= (- ((_ int_of 7) y8) ((_ int_of 7) r8)) 0)
                                        (>= (- ((_ int_of 7) r8) (+ ((_ int_of 7) x8) ((_ int_of 7) y8))) -1)
                                    )
                                    true
                                ))
                        ) :rule pbblast_bvand)"#: true,
            }
            "Invalid 8-bit AND (swapped order)" {
                r#"(step t1 (cl (and (= (bvand x8 y8) r8)
                                (and
                                    (and ; i=0
                                        (>= (- ((_ int_of 0) x8) ((_ int_of 0) r8)) 0)
                                        (>= (- ((_ int_of 0) y8) ((_ int_of 0) r8)) 0)
                                        (>= (- ((_ int_of 0) r8) (+ ((_ int_of 0) x8) ((_ int_of 0) y8))) -1)
                                    )
                                    (and ; i=1
                                        (>= (- ((_ int_of 1) x8) ((_ int_of 1) r8)) 0)
                                        (>= (- ((_ int_of 1) y8) ((_ int_of 1) r8)) 0)
                                        (>= (- ((_ int_of 1) r8) (+ ((_ int_of 1) x8) ((_ int_of 1) y8))) -1)
                                    )
                                    (and ; i=2
                                        (>= (- ((_ int_of 2) x8) ((_ int_of 2) r8)) 0)
                                        (>= (- ((_ int_of 2) y8) ((_ int_of 2) r8)) 0)
                                        (>= (- ((_ int_of 2) r8) (+ ((_ int_of 2) x8) ((_ int_of 2) y8))) -1)
                                    )
                                    (and ; i=3
                                        (>= (- ((_ int_of 3) x8) ((_ int_of 3) r8)) 0)
                                        (>= (- ((_ int_of 3) y8) ((_ int_of 3) r8)) 0)
                                        (>= (- ((_ int_of 3) r8) (+ ((_ int_of 3) x8) ((_ int_of 3) y8))) -1)
                                    )
                                    (and ; i=4
                                        (>= (- ((_ int_of 4) r8) ((_ int_of 4) x8)) 0) ; swapped order x8-r8
                                        (>= (- ((_ int_of 4) y8) ((_ int_of 4) r8)) 0)
                                        (>= (- ((_ int_of 4) r8) (+ ((_ int_of 4) x8) ((_ int_of 4) y8))) -1)
                                    )
                                    (and ; i=5
                                        (>= (- ((_ int_of 5) x8) ((_ int_of 5) r8)) 0)
                                        (>= (- ((_ int_of 5) y8) ((_ int_of 5) r8)) 0)
                                        (>= (- ((_ int_of 5) r8) (+ ((_ int_of 5) x8) ((_ int_of 5) y8))) -1)
                                    )
                                    (and ; i=6
                                        (>= (- ((_ int_of 6) x8) ((_ int_of 6) r8)) 0)
                                        (>= (- ((_ int_of 6) y8) ((_ int_of 6) r8)) 0)
                                        (>= (- ((_ int_of 6) r8) (+ ((_ int_of 6) x8) ((_ int_of 6) y8))) -1)
                                    )
                                    (and ; i=7 (MSB)
                                        (>= (- ((_ int_of 7) x8) ((_ int_of 7) r8)) 0)
                                        (>= (- ((_ int_of 7) y8) ((_ int_of 7) r8)) 0)
                                        (>= (- ((_ int_of 7) r8) (+ ((_ int_of 7) x8) ((_ int_of 7) y8))) -1)
                                    )
                                    true
                                ))
                        ) :rule pbblast_bvand)"#: false,
            }
        }
    }
}
