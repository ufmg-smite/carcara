use super::{assert_eq, RuleArgs, RuleResult};
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

// Helper to check that a summation has the expected shape
// when the bitvector is a @pbbterm application "short-circuiting"
fn check_pbblast_sum_short_circuit(pbbterm: &[Rc<Term>], sum: &[Rc<Term>]) -> RuleResult {
    // The summation must have at most as many summands as the bitvector has bits.
    rassert!(
        pbbterm.len() >= sum.len(),
        CheckerError::Explanation(format!(
            "Mismatched number of summands {} and bits {}",
            pbbterm.len(),
            sum.len()
        ))
    );

    for (i, element) in sum.iter().enumerate() {
        // Try to match (* c bv))
        let (c, bv) = match match_term!((* c bv) = element) {
            Some((c, bv)) => (c.as_integer_err()?, bv),
            None => {
                if i == 0 {
                    (Integer::from(1), element)
                } else {
                    return Err(CheckerError::Explanation(
                        "Coefficient was not found and i != 0".into(),
                    ));
                }
            }
        };

        // Check that the coefficient is 2^i.
        rassert!(
            c == (Integer::from(1) << i),
            CheckerError::Explanation(format!("Coefficient {} is not 2^{}", c, i))
        );

        assert_eq(bv, &pbbterm[i])?;
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
    if let Some(pbb_l) = match_term!((pbbterm ...) = left_bv) {
        // Case when x is application of `@pbbterm` so we must short-circuit the indexing
        let pbb_r = match_term_err!((pbbterm ...) = right_bv)?;
        check_pbblast_sum_short_circuit(pbb_l, left_sum)?;
        check_pbblast_sum_short_circuit(pbb_r, right_sum)
    } else {
        check_pbblast_sum(pool, left_bv, left_sum)?;
        check_pbblast_sum(pool, right_bv, right_sum)
    }
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
    // Short-circuited
    if let Some(pbb) = match_term!((pbbterm ...) = bitvector) {
        let last = pbb
            .last()
            .ok_or(CheckerError::Explanation("No sign bit in pbbterm".into()))?;
        let (coeff, sign_bit) = match_term_err!((* coeff sign_bit) = sign)?;
        let coeff = coeff.as_integer_err()?;

        // Check that the coefficient is 2^(n-1)
        rassert!(
            coeff == (Integer::from(1) << (n - 1)), // 2^(n-1)
            CheckerError::Explanation(format!("Expected coefficient 2^{} got {coeff}", (n - 1)))
        );
        return assert_eq(sign_bit, last);
    }

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

/// Helper to transform a bitvector to a list of terms, both when short-circuited or not
/// Ex: `get_bitvector_terms(x, 2)`
/// >>> `[((int_of 0) x),((int_of 1) x)]`
///
/// Ex: `get_bitvector_terms((pbbterm @x0 @x1), 2)`
/// >>> `[@x0, @x1]`
fn get_bitvector_terms(bv: &Rc<Term>, pool: &mut dyn TermPool) -> Vec<Rc<Term>> {
    if let Some(xs) = match_term!((pbbterm ...) = bv) {
        xs.to_vec()
    } else {
        // Get bit width of `x`
        let n = get_bit_width(bv, pool).unwrap();
        (0..n)
            .map(|i| {
                build_term!(
                    pool,
                    ((_ int_of { pool.add(Term::new_int(i)) }) { bv.clone() })
                )
            })
            .collect()
    }
}

/// Implements the bitwise exclusive or operation.
pub fn pbblast_bvxor(RuleArgs { pool, conclusion, .. }: RuleArgs) -> RuleResult {
    let ((x, y), bit_constraints) =
        match_term_err!((= (bvxor x y) (pbbterm ...)) = &conclusion[0])?;

    let xs = get_bitvector_terms(x, pool);
    let ys = get_bitvector_terms(y, pool);

    // Zip three lists into tuples
    for ((bc, xi), yi) in bit_constraints.iter().zip(xs.iter()).zip(ys.iter()) {
        let (bindings, (c1, c2, c3, c4)) = match_term_err!((choice ... (and c1 c2 c3 c4)) = bc)?;

        // Check z -> Int
        let (z_name, z_type) = &bindings[0];
        rassert!(
            z_name == "z",
            CheckerError::Explanation(format!("Expected {z_name} to be \"z\""))
        );
        rassert!(
            *z_type.as_sort().unwrap() == Sort::Int,
            CheckerError::Explanation(format!("Expected {z_type} to be Sort::Int"))
        );

        // c1 : (>= (+ xi yi) z)
        let ((xic, yic), zc) = match_term_err!((>= (+ xi yi) z) = c1)?;
        assert_eq(xic, xi)?;
        assert_eq(yic, yi)?;
        rassert!(
            zc.as_var() == Some(z_name) && pool.sort(zc) == *z_type,
            CheckerError::Explanation(format!("Expected {z_name} but got {zc}"))
        );

        // c2 : (>= (+ z xi) yi)
        let ((zc, xic), yic) = match_term_err!((>= (+ z xi) yi) = c2)?;
        assert_eq(xic, xi)?;
        assert_eq(yic, yi)?;
        rassert!(
            zc.as_var() == Some(z_name) && pool.sort(zc) == *z_type,
            CheckerError::Explanation(format!("Expected {z_name} but got {zc}"))
        );

        // c3 : (>= (+ z yi) xi)
        let ((zc, yic), xic) = match_term_err!((>= (+ z yi) xi) = c3)?;
        assert_eq(xic, xi)?;
        assert_eq(yic, yi)?;
        rassert!(
            zc.as_var() == Some(z_name) && pool.sort(zc) == *z_type,
            CheckerError::Explanation(format!("Expected {z_name} but got {zc}"))
        );

        // c4 : (>= 2 (+ z xi yi)
        let (_, (zc, xic, yic)) = match_term_err!((>= 2 (+ z xi yi)) = c4)?;
        assert_eq(xic, xi)?;
        assert_eq(yic, yi)?;
        rassert!(
            zc.as_var() == Some(z_name) && pool.sort(zc) == *z_type,
            CheckerError::Explanation(format!("Expected {z_name} but got {zc}"))
        );
    }

    Ok(())
}

/// Implements the bitwise and operation.
pub fn pbblast_bvand(RuleArgs { pool, conclusion, .. }: RuleArgs) -> RuleResult {
    let ((x, y), bit_constraints) =
        match_term_err!((= (bvand x y) (pbbterm ...)) = &conclusion[0])?;

    let xs = get_bitvector_terms(x, pool);
    let ys = get_bitvector_terms(y, pool);

    // Zip three lists into tuples
    for ((bc, xi), yi) in bit_constraints.iter().zip(xs.iter()).zip(ys.iter()) {
        let (bindings, (c1, c2, c3)) = match_term_err!((choice ... (and c1 c2 c3)) = bc)?;

        // Check z -> Int
        let (z_name, z_type) = &bindings[0];
        rassert!(
            z_name == "z",
            CheckerError::Explanation(format!("Expected {z_name} to be \"z\""))
        );
        rassert!(
            *z_type.as_sort().unwrap() == Sort::Int,
            CheckerError::Explanation(format!("Expected {z_type} to be Sort::Int"))
        );

        // c1 : (>= @x0 z)
        let (xic, zc) = match_term_err!((>= xi z) = c1)?;
        assert_eq(xic, xi)?;
        rassert!(
            zc.as_var() == Some(z_name) && pool.sort(zc) == *z_type,
            CheckerError::Explanation(format!("Expected {z_name} but got {zc}"))
        );

        // c2 : (>= @y0 z)
        let (yic, zc) = match_term_err!((>= yi z) = c2)?;
        assert_eq(yic, yi)?;
        rassert!(
            zc.as_var() == Some(z_name) && pool.sort(zc) == *z_type,
            CheckerError::Explanation(format!("Expected {z_name} but got {zc}"))
        );

        // c3 : (>= (+ z 1) (+ @x0 @y0))
        let ((zc, _), (xic, yic)) = match_term_err!((>= (+ z 1) (+ xi yi)) = c3)?;
        rassert!(
            zc.as_var() == Some(z_name) && pool.sort(zc) == *z_type,
            CheckerError::Explanation(format!("Expected {z_name} but got {zc}"))
        );
        assert_eq(xic, xi)?;
        assert_eq(yic, yi)?;
    }

    Ok(())
}

/// This rule extracts assertions of the ith bit of an application of
/// `pbblast_bvand`, given its arguments were x and y, we conclude
///  `(>= x r) (>= y r) (>= (+ r 1) (+ x y)))`
/// In which ri is the choice element from the pseudo boolean bit blasting
/// of the bvand rule
pub fn pbblast_bvand_ith_bit(RuleArgs { args, pool, conclusion, .. }: RuleArgs) -> RuleResult {
    let x = &args[0];
    let y = &args[1];
    let (c1, c2, c3) = match_term_err!((and c1 c2 c3) = &conclusion[0])?;

    // Build the expected choice term
    // `(choice ((z Int)) (and (>= x z) (>= y z) (>= (+ z 1) (+ x y))))`
    // TODO 1. Build without the macro
    // TODO 2. Extend the macro to build choice terms
    // let r = build_term!(pool, (choice ((z Int)) (0)) );
    // let r = build_term!(pool, (choice ((z Int)) (and (>= x z) (>= y z) (>= (+ z 1) (+ x y)))) );

    // c1 : (>= x r)
    let (xc, rc) = match_term_err!((>= x r) = c1)?;
    assert_eq(xc, x)?;
    // rassert!(
    //     zc.as_var() == Some(z_name) && pool.sort(zc) == *z_type,
    //     CheckerError::Explanation(format!("Expected {z_name} but got {zc}"))
    // );

    // c2 : (>= y r)
    let (yc, rc) = match_term_err!((>= y r) = c2)?;
    assert_eq(yc, y)?;

    // c3 : (>= (+ r 1) (+ x y))
    let ((r, _), (x, y)) = match_term_err!((>= (+ r 1) (+ x y)) = c3)?;
    assert_eq(xc, x)?;
    assert_eq(yc, y)?;

    Ok(())
}
