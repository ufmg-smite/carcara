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

// Test that uses the @pbbterm application to exercise short-circuiting
#[test]
fn pbblast_bveq_1_short_circuit() {
    test_cases! {
        definitions = "
            (declare-const @x0 Int)
            (declare-const @y0 Int)
        ",
        // Check that equality on single-bit bitvectors is accepted when
        // the summation for each side explicitly multiplies by 1.
        "Equality on single bits with short-circuit" {
            r#"(step t1 (cl (= (= (@pbbterm @x0) (@pbbterm @y0))
                             (= (- (* 1 @x0)
                                   (* 1 @y0))
                                0))) :rule pbblast_bveq)"#: true,
        }

        // Check that equality on single-bit bitvectors is accepted even when
        // the multiplication by 1 is omitted (i.e. defaulting to 1).
        "Omit multiplication by 1" {
            r#"(step t1 (cl (= (= (@pbbterm @x0) (@pbbterm @y0))
                             (= (- @x0 @y0)
                                0))) :rule pbblast_bveq)"#: true,
        }

        // Check that a term which is not a subtraction of sums is rejected.
        "Not a subtraction of sums" {
            r#"(step t1 (cl (= (= (@pbbterm @x0) (@pbbterm @y0))
                             (= (* 1 @x0)
                                0))) :rule pbblast_bveq)"#: false,
        }

        // Check that malformed products are rejected:
        // Case 1: the first summand uses a zero coefficient.
        "Malformed products: coefficient 0 in first summand" {
            r#"(step t1 (cl (= (= (@pbbterm @x0) (@pbbterm @y0))
                             (= (- (* 0 @x0)
                                   (* 1 @y0))
                                0))) :rule pbblast_bveq)"#: false,
        }

        // Check that malformed products are rejected:
        // Case 2: the second summand uses a zero coefficient.
        "Malformed products: coefficient 0 in second summand" {
            r#"(step t1 (cl (= (= (@pbbterm @x0) (@pbbterm @y0))
                             (= (- (* 1 @x0)
                                   (* 0 @y0))
                                0))) :rule pbblast_bveq)"#: false,
        }

        // In the past a trailing zero was used. This checks that
        // only the current format is allowed by the checker
        "Trailing Zero" {
            r#"(step t1 (cl (= (= (@pbbterm @x0) (@pbbterm @y0))
                             (= (- (+ (* 1 @x0) 0)
                                   (+ (* 1 @y0) 0))
                                0))) :rule pbblast_bveq)"#: false,

            r#"(step t1 (cl (= (= (@pbbterm @x0) (@pbbterm @y0))
                             (= (- (+ @x0 0)
                                   (+ @y0 0))
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
fn pbblast_bveq_2_short_circuit() {
    test_cases! {
        definitions = "
            (declare-const @x0 Int)
            (declare-const @x1 Int)
            (declare-const @y0 Int)
            (declare-const @y1 Int)
        ",
        // Check equality on two-bit bitvectors, ensuring that:
        // - The most significant bit (index 1) uses a coefficient of 1,
        // - The least significant bit (index 0) uses a coefficient of 2.
        "Equality on two bits" {
            r#"(step t1 (cl (= (= (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                             (= (- (+ (* 1 @x0)
                                      (* 2 @x1))
                                   (+ (* 1 @y0)
                                      (* 2 @y1)))
                                0))) :rule pbblast_bveq)"#: true,
        }
        "Trailing Zero" {
            r#"(step t1 (cl (= (= (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                             (= (- (+ (* 1 @x0)
                                      (* 2 @x1) 0)
                                   (+ (* 1 @y0)
                                      (* 2 @y1) 0))
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
fn pbblast_bveq_8_short_circuit() {
    test_cases! {
        definitions = "
            (declare-const @x0 Int)
            (declare-const @x1 Int)
            (declare-const @x2 Int)
            (declare-const @x3 Int)
            (declare-const @x4 Int)
            (declare-const @x5 Int)
            (declare-const @x6 Int)
            (declare-const @x7 Int)
            (declare-const @y0 Int)
            (declare-const @y1 Int)
            (declare-const @y2 Int)
            (declare-const @y3 Int)
            (declare-const @y4 Int)
            (declare-const @y5 Int)
            (declare-const @y6 Int)
            (declare-const @y7 Int)
        ",
        // Check equality on eight-bit bitvectors
        "Equality on 8-bit bitvectors" {
            r#"(step t1 (cl (= (= (@pbbterm @x0 @x1 @x2 @x3 @x4 @x5 @x6 @x7) (@pbbterm @y0 @y1 @y2 @y3 @y4 @y5 @y6 @y7))
                             (= (- (+ (* 1 @x0) (* 2 @x1) (* 4 @x2) (* 8 @x3) (* 16 @x4) (* 32 @x5) (* 64 @x6) (* 128 @x7))
                                   (+ (* 1 @y0) (* 2 @y1) (* 4 @y2) (* 8 @y3) (* 16 @y4) (* 32 @y5) (* 64 @y6) (* 128 @y7)))
                            0))) :rule pbblast_bveq)"#: true,
        }

        // We introduce a wrong coefficient (63 instead of 64).
        "bveq wrong coefficient in (@pbbterm @x0 @x1 @x2 @x3 @x4 @x5 @x6 @x7)" {
            r#"(step t1 (cl (= (= (@pbbterm @x0 @x1 @x2 @x3 @x4 @x5 @x6 @x7) (@pbbterm @y0 @y1 @y2 @y3 @y4 @y5 @y6 @y7))
                             (= (- (+ (* 1 @x0) (* 2 @x1) (* 4 @x2) (* 8 @x3) (* 16 @x4) (* 32 @x5) (* 63 @x6) (* 128 @x7)) ; WRONG: should be (* 64 @x1)
                                   (+ (* 1 @y0) (* 2 @y1) (* 4 @y2) (* 8 @y3) (* 16 @y4) (* 32 @y5) (* 64 @y6) (* 128 @y7)))
                             0))) :rule pbblast_bveq)"#: false,
        }

        // We introduce a wrong constant (1 instead of 0).
        "bveq wrong constant in equality" {
            r#"(step t1 (cl (= (= (@pbbterm @x0 @x1 @x2 @x3 @x4 @x5 @x6 @x7) (@pbbterm @y0 @y1 @y2 @y3 @y4 @y5 @y6 @y7))
                             (= (- (+ (* 1 @x0) (* 2 @x1) (* 4 @x2) (* 8 @x3) (* 16 @x4) (* 32 @x5) (* 64 @x6) (* 128 @x7))
                                   (+ (* 1 @y0) (* 2 @y1) (* 4 @y2) (* 8 @y3) (* 16 @y4) (* 32 @y5) (* 64 @y6) (* 128 @y7)))
                             1) ; WRONG: should be 0
                             )) :rule pbblast_bveq)"#: false,
        }
        "Trailing Zero" {
            r#"(step t1 (cl (= (= (@pbbterm @x0 @x1 @x2 @x3 @x4 @x5 @x6 @x7) (@pbbterm @y0 @y1 @y2 @y3 @y4 @y5 @y6 @y7))
                             (= (- (+ (* 1 @x0) (* 2 @x1) (* 4 @x2) (* 8 @x3) (* 16 @x4) (* 32 @x5) (* 64 @x6) (* 128 @x7) 0)
                                   (+ (* 1 @y0) (* 2 @y1) (* 4 @y2) (* 8 @y3) (* 16 @y4) (* 32 @y5) (* 64 @y6) (* 128 @y7) 0))
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
fn pbblast_bvult_2_short_circuit() {
    test_cases! {
        definitions = "
            (declare-const @x0 Int)
            (declare-const @x1 Int)
            (declare-const @y0 Int)
            (declare-const @y1 Int)
        ",
        // Test on two-bit bitvectors.
        "bvult on two bits" {
            r#"(step t1 (cl (= (bvult (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                             (>= (- (+ (* 1 @y0) (* 2 @y1))
                                    (+ (* 1 @x0) (* 2 @x1)))
                                 1))) :rule pbblast_bvult)"#: true,
        }
        "bvult mismatched index on two bits" {
            r#"(step t1 (cl (= (bvult (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                             (>= (- (+ (* 1 @y1) (* 2 @y0))
                                    (+ (* 1 @x1) (* 2 @x0)))
                                 1))) :rule pbblast_bvult)"#: false,
        }
        "Trailing Zero" {
            r#"(step t1 (cl (= (bvult (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                             (>= (- (+ (* 1 @y0) (* 2 @y1) 0)
                                    (+ (* 1 @x0) (* 2 @x1) 0))
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
fn pbblast_bvugt_2_short_circuit() {
    test_cases! {
        definitions = "
            (declare-const @x0 Int)
            (declare-const @x1 Int)
            (declare-const @y0 Int)
            (declare-const @y1 Int)
        ",
        // Correct formulation for two-bit bitvectors.
        // Expected summands for x2: most-significant bit uses coefficient 1, least-significant uses coefficient 2.
        "bvugt on two bits" {
            r#"(step t1 (cl (= (bvugt (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                             (>= (- (+ (* 1 @x0) (* 2 @x1))
                                    (+ (* 1 @y0) (* 2 @y1)))
                                 1))) :rule pbblast_bvugt)"#: true,
        }
        "bvugt mismatched indices on two bits" {
            r#"(step t1 (cl (= (bvugt (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                             (>= (- (+ (* 1 @x1) (* 2 @x0))
                                    (+ (* 1 @y1) (* 2 @y0)))
                                 1))) :rule pbblast_bvugt)"#: false,
        }
        "Trailing Zero" {
            r#"(step t1 (cl (= (bvugt (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                             (>= (- (+ (* 1 @x0) (* 2 @x1) 0)
                                    (+ (* 1 @y0) (* 2 @y1) 0))
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
fn pbblast_bvuge_2_short_circuit() {
    test_cases! {
        definitions = "
            (declare-const @x0 Int)
            (declare-const @x1 Int)
            (declare-const @y0 Int)
            (declare-const @y1 Int)
        ",
        "bvuge on two bits" {
            r#"(step t1 (cl (= (bvuge (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                             (>= (- (+ (* 1 @x0) (* 2 @x1))
                                    (+ (* 1 @y0) (* 2 @y1)))
                                 0))) :rule pbblast_bvuge)"#: true,
        }
        "bvuge mismatched indices on two bits" {
            r#"(step t1 (cl (= (bvuge (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                             (>= (- (+ (* 1 @x1) (* 2 @x0))
                                    (+ (* 1 @y1) (* 2 @y0)))
                                 0))) :rule pbblast_bvuge)"#: false,
        }
        "Trailing Zero" {
            r#"(step t1 (cl (= (bvuge (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                             (>= (- (+ (* 1 @x0) (* 2 @x1) 0)
                                    (+ (* 1 @y0) (* 2 @y1) 0))
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
fn pbblast_bvule_2_short_circuit() {
    test_cases! {
        definitions = "
            (declare-const @x0 Int)
            (declare-const @x1 Int)
            (declare-const @y0 Int)
            (declare-const @y1 Int)
        ",
        // Correct formulation for two-bit bitvectors.
        "bvule on two bits" {
            r#"(step t1 (cl (= (bvule (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                             (>= (- (+ (* 1 @y0) (* 2 @y1))
                                    (+ (* 1 @x0) (* 2 @x1)))
                                 0))) :rule pbblast_bvule)"#: true,
        }
        "bvule mismatched indices on two bits" {
            r#"(step t1 (cl (= (bvule (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                             (>= (- (+ (* 1 @y1) (* 2 @y0))
                                    (+ (* 1 @x1) (* 2 @x0)))
                                 0))) :rule pbblast_bvule)"#: false,
        }
        "Trailing Zero" {
            r#"(step t1 (cl (= (bvule (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                             (>= (- (+ (* 1 @y0) (* 2 @y1) 0)
                                    (+ (* 1 @x0) (* 2 @x1) 0))
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
fn pbblast_bvslt_2_short_circuit() {
    test_cases! {
        definitions = "
            (declare-const @x0 Int)
            (declare-const @x1 Int)
            (declare-const @y0 Int)
            (declare-const @y1 Int)
        ",

        // Using explicit multiplication everywhere.
        "bvslt on two bits with explicit multiplication" {
            r#"(step t1 (cl (= (bvslt (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                            (>= (+
                                    (-
                                        (* 1 @y0)         ; y sum
                                        (* 2 @y1)         ; y sign
                                    )
                                    (-
                                        (* 2 @x1)         ; x sign
                                        (* 1 @x0)         ; x sum
                                    )
                                ) 1))) :rule pbblast_bvslt)"#: true,
        }

        // Omitting the explicit multiplication by 1 in the sum parts.
        "bvslt on two bits omitting multiplication by 1 in sum parts" {
            r#"(step t1 (cl (= (bvslt (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                            (>= (+
                                    (-
                                        @y0               ; y sum omitted "* 1"
                                        (* 2 @y1) 
                                    )
                                    (-
                                        (* 2 @x1)         
                                        @x0               ; x sum omitted "* 1"
                                    )
                                ) 1))) :rule pbblast_bvslt)"#: true,
        }

        // Wrong scalar of the sign bit
        "bvslt on two bits wrong scalar of the sign bit of y" {
            r#"(step t1 (cl (= (bvslt (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                            (>= (+
                                    (-
                                        (* 1 @y0)
                                        (* 1 @y1)         ; should be * 2
                                    )
                                    (-
                                        (* 2 @x1)
                                        (* 1 @x0)
                                    )
                                ) 1))) :rule pbblast_bvslt)"#: false,
        }

        "bvslt on two bits wrong scalar of the sign bit of x" {
            r#"(step t1 (cl (= (bvslt (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                            (>= (+
                                    (-
                                        (* 1 @y0)
                                        (* 2 @y1)    
                                    )
                                    (-
                                        (* 1 @x1)         ; should be * 2
                                        (* 1 @x0)
                                    )
                                ) 1))) :rule pbblast_bvslt)"#: false,
        }

        // Wrong indexing of the sign bit
        "bvslt on two bits wrong indexing of the sign bit of y" {
            r#"(step t1 (cl (= (bvslt (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                            (>= (+
                                    (-
                                        (* 1 @y0)
                                        (* 2 @y0)         ; should be (_ @int_of 1)
                                    )
                                    (-
                                        (* 2 @x1)
                                        (* 1 @x0)
                                    )
                                ) 1))) :rule pbblast_bvslt)"#: false,
        }

        "bvslt on two bits wrong indexing of the sign bit of x" {
            r#"(step t1 (cl (= (bvslt (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                            (>= (+
                                    (-
                                        (* 1 @y0)
                                        (* 2 @y1)    
                                    )
                                    (-
                                        (* 2 @x0)         ; should be (_ @int_of 1)
                                        (* 1 @x0)
                                    )
                                ) 1))) :rule pbblast_bvslt)"#: false,
        }

        "bvslt on two bits wrong bitvector of the sign bit of x" {
            r#"(step t1 (cl (= (bvslt (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                            (>= (+
                                    (-
                                        (* 1 @y0)
                                        (* 2 @y1)    
                                    )
                                    (-
                                        (* 2 @y1)         ; should be(@pbbterm @x0 @x1) 
                                        (* 1 @x0)
                                    )
                                ) 1))) :rule pbblast_bvslt)"#: false,
        }

        "bvslt on two bits wrong bitvector of the sign bit of y" {
            r#"(step t1 (cl (= (bvslt (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                            (>= (+
                                    (-
                                        (* 1 @y0)
                                        (* 2 @x1)         ; should be(@pbbterm @y0 @y1) 
                                    )
                                    (-
                                        (* 2 @x1)         
                                        (* 1 @x0)
                                    )
                                ) 1))) :rule pbblast_bvslt)"#: false,
        }

        // Wrong indexing of the summation term
        "bvslt on two bits with wrong indexing of the summation term" {
            r#"(step t1 (cl (= (bvslt (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                            (>= (+
                                    (-
                                        (* 1 @y1)         ; should be "@int_of 0"
                                        (* 2 @y1)
                                    )
                                    (-
                                        (* 2 @x1)
                                        (* 1 @x0)
                                    )
                                ) 1))) :rule pbblast_bvslt)"#: false,
        }

        "Trailing Zero" {
            r#"(step t1 (cl (= (bvslt (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                            (>= (+
                                    (-
                                        (+ (* 1 @y0) 0)   ; y sum
                                        (* 2 @y1)         ; y sign
                                    )
                                    (-
                                        (* 2 @x1)         ; x sign
                                        (+ (* 1 @x0) 0)   ; x sum
                                    )
                                ) 1))) :rule pbblast_bvslt)"#: false,

            r#"(step t1 (cl (= (bvslt (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                            (>= (+
                                    (-
                                        (+ @y0 0)         ; y sum omitted "* 1"
                                        (* 2 @y1) 
                                    )
                                    (-
                                        (* 2 @x1)         
                                        (+ @x0 0)         ; x sum omitted "* 1"
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
fn pbblast_bvsgt_2_short_circuit() {
    test_cases! {
        definitions = "
            (declare-const @x0 Int)
            (declare-const @x1 Int)
            (declare-const @y0 Int)
            (declare-const @y1 Int)
        ",

        // Using explicit multiplication everywhere.
        "bvsgt on two bits with explicit multiplication" {
            r#"(step t1 (cl (= (bvsgt (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                            (>= (+ (-
                                        (* 1 @x0)   ; x sum
                                        (* 2 @x1)         ; x sign
                                    )
                                    (-
                                        (* 2 @y1)         ; y sign
                                        (* 1 @y0)   ; y sum
                                    )
                                ) 1))) :rule pbblast_bvsgt)"#: true,
        }

        // Omitting the explicit multiplication by 1 in the sum parts.
        "bvsgt on two bits omitting multiplication by 1 in sum parts" {
            r#"(step t1 (cl (= (bvsgt (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                            (>= (+
                                    (-
                                        @x0         ; x sum omitted "* 1"
                                        (* 2 @x1) 
                                    )
                                    (-
                                        (* 2 @y1)         
                                        @y0         ; y sum omitted "* 1"
                                    )
                                ) 1))) :rule pbblast_bvsgt)"#: true,
        }

        // Wrong scalar of the sign bit
        "bvsgt on two bits wrong scalar of the sign bit of y" {
            r#"(step t1 (cl (= (bvsgt (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                            (>= (+
                                    (-
                                        (* 1 @x0)
                                        (* 1 @x1)         ; should be * 2
                                    )
                                    (-
                                        (* 2 @y1)
                                        (* 1 @y0)
                                    )
                                ) 1))) :rule pbblast_bvsgt)"#: false,
        }

        "bvsgt on two bits wrong scalar of the sign bit of y" {
            r#"(step t1 (cl (= (bvsgt (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                            (>= (+
                                    (-
                                        (* 1 @x0)
                                        (* 2 @x1)    
                                    )
                                    (-
                                        (* 1 @y1)         ; should be * 2
                                        (* 1 @y0)
                                    )
                                ) 1))) :rule pbblast_bvsgt)"#: false,
        }

        // Wrong indexing of the sign bit
        "bvsgt on two bits wrong indexing of the sign bit of x" {
            r#"(step t1 (cl (= (bvsgt (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                            (>= (+
                                    (-
                                        (* 1 @x0)
                                        (* 2 @x0)         ; should be (_ @int_of 1)
                                    )
                                    (-
                                        (* 2 @y1)
                                        (* 1 @y0)
                                    )
                                ) 1))) :rule pbblast_bvsgt)"#: false,
        }

        "bvsgt on two bits wrong indexing of the sign bit of y" {
            r#"(step t1 (cl (= (bvsgt (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                            (>= (+
                                    (-
                                        (* 1 @x0)
                                        (* 2 @x1)    
                                    )
                                    (-
                                        (* 2 @y0)         ; should be (_ @int_of 1)
                                        (* 1 @y0)
                                    )
                                ) 1))) :rule pbblast_bvsgt)"#: false,
        }

        "bvsgt on two bits wrong bitvector of the sign bit of y" {
            r#"(step t1 (cl (= (bvsgt (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                            (>= (+
                                    (-
                                        (* 1 @x0)
                                        (* 2 @x1)    
                                    )
                                    (-
                                        (* 2 @x1)         ; should be(@pbbterm @y0 @y1) 
                                        (* 1 @y0)
                                    )
                                ) 1))) :rule pbblast_bvsgt)"#: false,
        }

        "bvsgt on two bits wrong bitvector of the sign bit of x" {
            r#"(step t1 (cl (= (bvsgt (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                            (>= (+
                                    (-
                                        (* 1 @x0)
                                        (* 2 @y1)         ; should be(@pbbterm @x0 @x1) 
                                    )
                                    (-
                                        (* 2 @y1)         
                                        (* 1 @y0)
                                    )
                                ) 1))) :rule pbblast_bvsgt)"#: false,
        }

        // Wrong indexing of the summation term
        "bvsgt on two bits with wrong indexing of the summation term" {
            r#"(step t1 (cl (= (bvsgt (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                            (>= (+
                                    (-
                                        (* 1 @x1)   ; should be "@int_of 0"
                                        (* 2 @x1)
                                    )
                                    (-
                                        (* 2 @y1)
                                        (* 1 @y0)
                                    )
                                ) 1))) :rule pbblast_bvsgt)"#: false,
        }

        "Trailing Zero" {
            r#"(step t1 (cl (= (bvsgt (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                            (>= (+ (-
                                        (+ (* 1 @x0) 0)   ; x sum
                                        (* 2 @x1)         ; x sign
                                    )
                                    (-
                                        (* 2 @y1)         ; y sign
                                        (+ (* 1 @y0) 0)   ; y sum
                                    )
                                ) 1))) :rule pbblast_bvsgt)"#: false,

            r#"(step t1 (cl (= (bvsgt (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                            (>= (+
                                    (-
                                        (+ @x0 0)         ; x sum omitted "* 1"
                                        (* 2 @x1) 
                                    )
                                    (-
                                        (* 2 @y1)         
                                        (+ @y0 0)         ; y sum omitted "* 1"
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
fn pbblast_bvsge_2_short_circuit() {
    test_cases! {
        definitions = "
            (declare-const @x0 Int)
            (declare-const @x1 Int)
            (declare-const @y0 Int)
            (declare-const @y1 Int)
        ",

        // Using explicit multiplication everywhere.
        "bvsge on two bits with explicit multiplication" {
            r#"(step t1 (cl (= (bvsge (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                            (>= (+
                                    (-
                                        (* 1 @x0)   ; x sum
                                        (* 2 @x1)   ; x sign
                                    )
                                    (-
                                        (* 2 @y1)   ; y sign
                                        (* 1 @y0)   ; y sum
                                    )
                                ) 0))) :rule pbblast_bvsge)"#: true,
        }

        // Omitting the explicit multiplication by 1 in the sum parts.
        "bvsge on two bits omitting multiplication by 1 in sum parts" {
            r#"(step t1 (cl (= (bvsge (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                            (>= (+
                                    (-
                                        @x0         ; x sum omitted "* 1"
                                        (* 2 @x1) 
                                    )
                                    (-
                                        (* 2 @y1)         
                                        @y0         ; y sum omitted "* 1"
                                    )
                                ) 0))) :rule pbblast_bvsge)"#: true,
        }

        // Wrong scalar of the sign bit
        "bvsge on two bits wrong scalar of the sign bit of y" {
            r#"(step t1 (cl (= (bvsge (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                            (>= (+
                                    (-
                                        (* 1 @x0)
                                        (* 1 @x1)   ; should be * 2
                                    )
                                    (-
                                        (* 2 @y1)
                                        (* 1 @y0)
                                    )
                                ) 0))) :rule pbblast_bvsge)"#: false,
        }

        "bvsge on two bits wrong scalar of the sign bit of y" {
            r#"(step t1 (cl (= (bvsge (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                            (>= (+
                                    (-
                                        (* 1 @x0)
                                        (* 2 @x1)    
                                    )
                                    (-
                                        (* 1 @y1)   ; should be * 2
                                        (* 1 @y0)
                                    )
                                ) 0))) :rule pbblast_bvsge)"#: false,
        }

        // Wrong indexing of the sign bit
        "bvsge on two bits wrong indexing of the sign bit of x" {
            r#"(step t1 (cl (= (bvsge (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                            (>= (+
                                    (-
                                        (* 1 @x0)
                                        (* 2 @x0)   ; should be (_ @int_of 1)
                                    )
                                    (-
                                        (* 2 @y1)
                                        (* 1 @y0)
                                    )
                                ) 0))) :rule pbblast_bvsge)"#: false,
        }

        "bvsge on two bits wrong indexing of the sign bit of y" {
            r#"(step t1 (cl (= (bvsge (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                            (>= (+
                                    (-
                                        (* 1 @x0)
                                        (* 2 @x1)    
                                    )
                                    (-
                                        (* 2 @y0)   ; should be (_ @int_of 1)
                                        (* 1 @y0)
                                    )
                                ) 0))) :rule pbblast_bvsge)"#: false,
        }

        "bvsge on two bits wrong bitvector of the sign bit of y" {
            r#"(step t1 (cl (= (bvsge (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                            (>= (+
                                    (-
                                        (* 1 @x0)
                                        (* 2 @x1)    
                                    )
                                    (-
                                        (* 2 @x1)   ; should be(@pbbterm @y0 @y1) 
                                        (* 1 @y0)
                                    )
                                ) 0))) :rule pbblast_bvsge)"#: false,
        }

        "bvsge on two bits wrong bitvector of the sign bit of x" {
            r#"(step t1 (cl (= (bvsge (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                            (>= (+
                                    (-
                                        (* 1 @x0)
                                        (* 2 @y1)   ; should be(@pbbterm @x0 @x1) 
                                    )
                                    (-
                                        (* 2 @y1)         
                                        (* 1 @y0)
                                    )
                                ) 0))) :rule pbblast_bvsge)"#: false,
        }

        // Wrong indexing of the summation term
        "bvsge on two bits with wrong indexing of the summation term" {
            r#"(step t1 (cl (= (bvsge (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                            (>= (+
                                    (-
                                        (* 1 @x1)   ; should be "@int_of 0"
                                        (* 2 @x1)
                                    )
                                    (-
                                        (* 2 @y1)
                                        (* 1 @y0)
                                    )
                                ) 0))) :rule pbblast_bvsge)"#: false,
        }

        "Trailing Zero" {
            r#"(step t1 (cl (= (bvsge (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                            (>= (+
                                    (-
                                        (+ (* 1 @x0) 0)   ; x sum
                                        (* 2 @x1)         ; x sign
                                    )
                                    (-
                                        (* 2 @y1)         ; y sign
                                        (+ (* 1 @y0) 0)   ; y sum
                                    )
                                ) 0))) :rule pbblast_bvsge)"#: false,

            r#"(step t1 (cl (= (bvsge (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                            (>= (+
                                    (-
                                        (+ @x0 0)         ; x sum omitted "* 1"
                                        (* 2 @x1) 
                                    )
                                    (-
                                        (* 2 @y1)         
                                        (+ @y0 0)         ; y sum omitted "* 1"
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
fn pbblast_bvsle_2_short_circuit() {
    test_cases! {
        definitions = "
            (declare-const @x0 Int)
            (declare-const @x1 Int)
            (declare-const @y0 Int)
            (declare-const @y1 Int)
        ",

        // Using explicit multiplication everywhere.
        "bvsle on two bits with explicit multiplication" {
            r#"(step t1 (cl (= (bvsle (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                            (>= (+
                                    (-
                                        (* 1 @y0)   ; y sum
                                        (* 2 @y1)   ; y sign
                                    )
                                    (-
                                        (* 2 @x1)   ; x sign
                                        (* 1 @x0)   ; x sum
                                    )
                                ) 0))) :rule pbblast_bvsle)"#: true,
        }

        // Omitting the explicit multiplication by 1 in the sum parts.
        "bvsle on two bits omitting multiplication by 1 in sum parts" {
            r#"(step t1 (cl (= (bvsle (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                            (>= (+
                                    (-
                                        @y0         ; y sum omitted "* 1"
                                        (* 2 @y1) 
                                    )
                                    (-
                                        (* 2 @x1)         
                                        @x0         ; x sum omitted "* 1"
                                    )
                                ) 0))) :rule pbblast_bvsle)"#: true,
        }

        // Wrong scalar of the sign bit
        "bvsle on two bits wrong scalar of the sign bit of y" {
            r#"(step t1 (cl (= (bvsle (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                            (>= (+
                                    (-
                                        (* 1 @y0)
                                        (* 1 @y1)   ; should be * 2
                                    )
                                    (-
                                        (* 2 @x1)
                                        (* 1 @x0)
                                    )
                                ) 0))) :rule pbblast_bvsle)"#: false,
        }

        "bvsle on two bits wrong scalar of the sign bit of x" {
            r#"(step t1 (cl (= (bvsle (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                            (>= (+
                                    (-
                                        (* 1 @y0)
                                        (* 2 @y1)    
                                    )
                                    (-
                                        (* 1 @x1)   ; should be * 2
                                        (* 1 @x0)
                                    )
                                ) 0))) :rule pbblast_bvsle)"#: false,
        }

        // Wrong indexing of the sign bit
        "bvsle on two bits wrong indexing of the sign bit of y" {
            r#"(step t1 (cl (= (bvsle (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                            (>= (+
                                    (-
                                        (* 1 @y0)
                                        (* 2 @y0)   ; should be (_ @int_of 1)
                                    )
                                    (-
                                        (* 2 @x1)
                                        (* 1 @x0)
                                    )
                                ) 0))) :rule pbblast_bvsle)"#: false,
        }

        "bvsle on two bits wrong indexing of the sign bit of x" {
            r#"(step t1 (cl (= (bvsle (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                            (>= (+
                                    (-
                                        (* 1 @y0)
                                        (* 2 @y1)    
                                    )
                                    (-
                                        (* 2 @x0)   ; should be (_ @int_of 1)
                                        (* 1 @x0)
                                    )
                                ) 0))) :rule pbblast_bvsle)"#: false,
        }

        "bvsle on two bits wrong bitvector of the sign bit of x" {
            r#"(step t1 (cl (= (bvsle (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                            (>= (+
                                    (-
                                        (* 1 @y0)
                                        (* 2 @y1)    
                                    )
                                    (-
                                        (* 2 @y1)   ; should be(@pbbterm @x0 @x1) 
                                        (* 1 @x0)
                                    )
                                ) 0))) :rule pbblast_bvsle)"#: false,
        }

        "bvsle on two bits wrong bitvector of the sign bit of y" {
            r#"(step t1 (cl (= (bvsle (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                            (>= (+
                                    (-
                                        (* 1 @y0)
                                        (* 2 @x1)   ; should be(@pbbterm @y0 @y1) 
                                    )
                                    (-
                                        (* 2 @x1)         
                                        (* 1 @x0)
                                    )
                                ) 0))) :rule pbblast_bvsle)"#: false,
        }

        // Wrong indexing of the summation term
        "bvsle on two bits with wrong indexing of the summation term" {
            r#"(step t1 (cl (= (bvsle (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                            (>= (+
                                    (-
                                        (* 1 @y1)   ; should be "@int_of 0"
                                        (* 2 @y1)
                                    )
                                    (-
                                        (* 2 @x1)
                                        (* 1 @x0)
                                    )
                                ) 0))) :rule pbblast_bvsle)"#: false,
        }

        "Trailing Zero" {
            r#"(step t1 (cl (= (bvsle (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                            (>= (+
                                    (-
                                        (+ (* 1 @y0) 0)   ; y sum
                                        (* 2 @y1)         ; y sign
                                    )
                                    (-
                                        (* 2 @x1)         ; x sign
                                        (+ (* 1 @x0) 0)   ; x sum
                                    )
                                ) 0))) :rule pbblast_bvsle)"#: false,

            r#"(step t1 (cl (= (bvsle (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                            (>= (+
                                    (-
                                        (+ @y0 0)         ; y sum omitted "* 1"
                                        (* 2 @y1) 
                                    )
                                    (-
                                        (* 2 @x1)         
                                        (+ @x0 0)         ; x sum omitted "* 1"
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
fn pbblast_bvxor_1() {
    test_cases! {
        definitions = "
            (declare-const x1 (_ BitVec 1))
            (declare-const y1 (_ BitVec 1))
        ",
        "Valid 1-bit XOR" {
            r#"(step t1 (cl (=
                        (bvxor x1 y1)
                        (@pbbterm (! (choice ((z Int)) (and
                                                            (>= (+ ((_ @int_of 0) x1) ((_ @int_of 0) y1)) z)    ; (>= (+ xi yi) z)
                                                            (>= (+ z ((_ @int_of 0) x1)) ((_ @int_of 0) y1))    ; (>= (+ z xi) yi)
                                                            (>= (+ z ((_ @int_of 0) y1)) ((_ @int_of 0) x1))    ; (>= (+ z yi) xi)
                                                            (>= 2 (+ z ((_ @int_of 0) x1) ((_ @int_of 0) y1)))  ; (>= 2 (+ z xi yi))
                                            )) :named @r0))
                )) :rule pbblast_bvxor)"#: true,
        }
        "Invalid 1-bit XOR (missing constraint)" {
            r#"(step t1 (cl (=
                        (bvxor x1 y1)
                        (@pbbterm (! (choice ((z Int)) (and
                                                            (>= (+ ((_ @int_of 0) x1) ((_ @int_of 0) y1)) z)     ; (>= (+ xi yi) z)
                                                            ; MISSING (>= (+ z xi) yi)
                                                            (>= (+ z ((_ @int_of 0) y1)) ((_ @int_of 0) x1))     ; (>= (+ z yi) xi)
                                                            (>= 2 (+ z ((_ @int_of 0) x1) ((_ @int_of 0) y1)))   ; (>= 2 (+ z xi yi))
                                            )) :named @r0))
                )) :rule pbblast_bvxor)"#: false,
        }
    }
}

#[test]
fn pbblast_bvxor_2() {
    test_cases! {
        definitions = "
            (declare-const x2 (_ BitVec 2))
            (declare-const y2 (_ BitVec 2))
        ",
        "Valid 2-bit XOR" {
            r#"(step t1 (cl (=
                        (bvxor x2 y2)
                        (@pbbterm
                            (! (choice ((z Int)) (and
                                    (>= (+ ((_ @int_of 0) x2) ((_ @int_of 0) y2)) z)    ; (>= (+ xi yi) z)
                                    (>= (+ z ((_ @int_of 0) x2)) ((_ @int_of 0) y2))    ; (>= (+ z xi) yi)
                                    (>= (+ z ((_ @int_of 0) y2)) ((_ @int_of 0) x2))    ; (>= (+ z yi) xi)
                                    (>= 2 (+ z ((_ @int_of 0) x2) ((_ @int_of 0) y2)))  ; (>= 2 (+ z xi yi))
                                )) :named @r0)
                            (! (choice ((z Int)) (and
                                    (>= (+ ((_ @int_of 1) x2) ((_ @int_of 1) y2)) z)    ; (>= (+ xi yi) z)
                                    (>= (+ z ((_ @int_of 1) x2)) ((_ @int_of 1) y2))    ; (>= (+ z xi) yi)
                                    (>= (+ z ((_ @int_of 1) y2)) ((_ @int_of 1) x2))    ; (>= (+ z yi) xi)
                                    (>= 2 (+ z ((_ @int_of 1) x2) ((_ @int_of 1) y2)))  ; (>= 2 (+ z xi yi))
                                )) :named @r1))
                )) :rule pbblast_bvxor)"#: true,
        }

        "Invalid 2-bit XOR (wrong inequality bound)" {
            r#"(step t1 (cl (=
                        (bvxor x2 y2)
                        (@pbbterm
                            (! (choice ((z Int)) (and
                                    (>= (+ ((_ @int_of 0) x2) ((_ @int_of 0) y2)) z)    
                                    (>= (+ z ((_ @int_of 0) x2)) ((_ @int_of 0) y2))    
                                    (>= (+ z ((_ @int_of 0) y2)) ((_ @int_of 0) x2))    
                                    (>= 1 (+ z ((_ @int_of 0) x2) ((_ @int_of 0) y2)))  ; SHOULD BE (>= 2 (+ z xi yi))
                                )) :named @r0)
                            (! (choice ((z Int)) (and
                                    (>= (+ ((_ @int_of 1) x2) ((_ @int_of 1) y2)) z)    
                                    (>= (+ z ((_ @int_of 1) x2)) ((_ @int_of 1) y2))    
                                    (>= (+ z ((_ @int_of 1) y2)) ((_ @int_of 1) x2))    
                                    (>= 2 (+ z ((_ @int_of 1) x2) ((_ @int_of 1) y2)))  
                                )) :named @r1))
                )) :rule pbblast_bvxor)"#: false,
        }
    }
}

#[test]
fn pbblast_bvxor_2_short_circuit() {
    test_cases! {
        definitions = "
            (declare-const @x0 Int)
            (declare-const @x1 Int)
            (declare-const @y0 Int)
            (declare-const @y1 Int)
        ",
        "Valid 2-bit XOR (short-circuit)" {
            r#"(step t1 (cl (=
                        (bvxor (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                        (@pbbterm
                            (! (choice ((z Int)) (and
                                    (>= (+ @x0 @y0) z)    ; (>= (+ xi yi) z)
                                    (>= (+ z @x0) @y0)    ; (>= (+ z xi) yi)
                                    (>= (+ z @y0) @x0)    ; (>= (+ z yi) xi)
                                    (>= 2 (+ z @x0 @y0))  ; (>= 2 (+ z xi yi))
                                )) :named @r0)
                            (! (choice ((z Int)) (and
                                    (>= (+ @x1 @y1) z)    ; (>= (+ xi yi) z)
                                    (>= (+ z @x1) @y1)    ; (>= (+ z xi) yi)
                                    (>= (+ z @y1) @x1)    ; (>= (+ z yi) xi)
                                    (>= 2 (+ z @x1 @y1))  ; (>= 2 (+ z xi yi))
                                )) :named @r1))
                )) :rule pbblast_bvxor)"#: true,
        }

        "Invalid 2-bit XOR (wrong inequality bound)" {
            r#"(step t1 (cl (=
                        (bvxor (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                        (@pbbterm
                            (! (choice ((z Int)) (and
                                    (>= (+ @x0 @y0) z)    
                                    (>= (+ z @x0) @y0)    
                                    (>= (+ z @y0) @x0)    
                                    (>= 1 (+ z @x0 @y0))  ; SHOULD BE (>= 2 (+ z xi yi))
                                )) :named @r0)
                            (! (choice ((z Int)) (and
                                    (>= (+ @x1 @y1) z)    
                                    (>= (+ z @x1) @y1)    
                                    (>= (+ z @y1) @x1)    
                                    (>= 2 (+ z @x1 @y1))  
                                )) :named @r1))
                )) :rule pbblast_bvxor)"#: false,
        }
    }
}

#[test]
fn pbblast_bvxor_8() {
    test_cases! {
        definitions = "
            (declare-const x8 (_ BitVec 8))
            (declare-const y8 (_ BitVec 8))
        ",
        "Valid 8-bit XOR" {
            r#"(step t1 (cl (=
                        (bvxor x8 y8)
                        (@pbbterm
                            (! (choice ((z Int)) (and
                                    (>= (+ ((_ @int_of 0) x8) ((_ @int_of 0) y8)) z)    ; (>= (+ xi yi) z)
                                    (>= (+ z ((_ @int_of 0) x8)) ((_ @int_of 0) y8))    ; (>= (+ z xi) yi)
                                    (>= (+ z ((_ @int_of 0) y8)) ((_ @int_of 0) x8))    ; (>= (+ z yi) xi)
                                    (>= 2 (+ z ((_ @int_of 0) x8) ((_ @int_of 0) y8)))  ; (>= 2 (+ z xi yi))
                                )) :named @r0)
                            (! (choice ((z Int)) (and
                                    (>= (+ ((_ @int_of 1) x8) ((_ @int_of 1) y8)) z)    
                                    (>= (+ z ((_ @int_of 1) x8)) ((_ @int_of 1) y8))    
                                    (>= (+ z ((_ @int_of 1) y8)) ((_ @int_of 1) x8))    
                                    (>= 2 (+ z ((_ @int_of 1) x8) ((_ @int_of 1) y8)))  
                                )) :named @r1)
                            (! (choice ((z Int)) (and
                                    (>= (+ ((_ @int_of 2) x8) ((_ @int_of 2) y8)) z)    
                                    (>= (+ z ((_ @int_of 2) x8)) ((_ @int_of 2) y8))    
                                    (>= (+ z ((_ @int_of 2) y8)) ((_ @int_of 2) x8))    
                                    (>= 2 (+ z ((_ @int_of 2) x8) ((_ @int_of 2) y8)))  
                                )) :named @r2)
                            (! (choice ((z Int)) (and
                                    (>= (+ ((_ @int_of 3) x8) ((_ @int_of 3) y8)) z)    
                                    (>= (+ z ((_ @int_of 3) x8)) ((_ @int_of 3) y8))    
                                    (>= (+ z ((_ @int_of 3) y8)) ((_ @int_of 3) x8))    
                                    (>= 2 (+ z ((_ @int_of 3) x8) ((_ @int_of 3) y8)))  
                                )) :named @r3)
                            (! (choice ((z Int)) (and
                                    (>= (+ ((_ @int_of 4) x8) ((_ @int_of 4) y8)) z)    
                                    (>= (+ z ((_ @int_of 4) x8)) ((_ @int_of 4) y8))    
                                    (>= (+ z ((_ @int_of 4) y8)) ((_ @int_of 4) x8))    
                                    (>= 2 (+ z ((_ @int_of 4) x8) ((_ @int_of 4) y8)))  
                                )) :named @r4)
                            (! (choice ((z Int)) (and
                                    (>= (+ ((_ @int_of 5) x8) ((_ @int_of 5) y8)) z)    
                                    (>= (+ z ((_ @int_of 5) x8)) ((_ @int_of 5) y8))    
                                    (>= (+ z ((_ @int_of 5) y8)) ((_ @int_of 5) x8))    
                                    (>= 2 (+ z ((_ @int_of 5) x8) ((_ @int_of 5) y8)))  
                                )) :named @r5)
                            (! (choice ((z Int)) (and
                                    (>= (+ ((_ @int_of 6) x8) ((_ @int_of 6) y8)) z)    
                                    (>= (+ z ((_ @int_of 6) x8)) ((_ @int_of 6) y8))    
                                    (>= (+ z ((_ @int_of 6) y8)) ((_ @int_of 6) x8))    
                                    (>= 2 (+ z ((_ @int_of 6) x8) ((_ @int_of 6) y8)))  
                                )) :named @r6)
                            (! (choice ((z Int)) (and
                                    (>= (+ ((_ @int_of 7) x8) ((_ @int_of 7) y8)) z)    
                                    (>= (+ z ((_ @int_of 7) x8)) ((_ @int_of 7) y8))    
                                    (>= (+ z ((_ @int_of 7) y8)) ((_ @int_of 7) x8))    
                                    (>= 2 (+ z ((_ @int_of 7) x8) ((_ @int_of 7) y8)))  
                                )) :named @r7))
                )) :rule pbblast_bvxor)"#: true,
        }
        "Invalid 8-bit XOR (wrong indexing)" {
            r#"(step t1 (cl (=
                        (bvxor x8 y8)
                        (@pbbterm
                            (! (choice ((z Int)) (and
                                    (>= (+ ((_ @int_of 0) x8) ((_ @int_of 0) y8)) z)
                                    (>= (+ z ((_ @int_of 0) x8)) ((_ @int_of 0) y8))
                                    (>= (+ z ((_ @int_of 0) y8)) ((_ @int_of 0) x8))
                                    (>= 2 (+ z ((_ @int_of 0) x8) ((_ @int_of 0) y8)))
                                )) :named @r0)
                            (! (choice ((z Int)) (and
                                    (>= (+ ((_ @int_of 1) x8) ((_ @int_of 1) y8)) z)    
                                    (>= (+ z ((_ @int_of 1) x8)) ((_ @int_of 1) y8))    
                                    (>= (+ z ((_ @int_of 1) y8)) ((_ @int_of 1) x8))    
                                    (>= 2 (+ z ((_ @int_of 1) x8) ((_ @int_of 1) y8)))  
                                )) :named @r1)
                            ; WRONG INDEXING
                            (! (choice ((z Int)) (and
                                    ;                  v---- SHOULD BE 2
                                    (>= (+ ((_ @int_of 1) x8) ((_ @int_of 2) y8)) z)    
                                    (>= (+ z ((_ @int_of 2) x8)) ((_ @int_of 2) y8))    
                                    (>= (+ z ((_ @int_of 2) y8)) ((_ @int_of 2) x8))    
                                    (>= 2 (+ z ((_ @int_of 2) x8) ((_ @int_of 2) y8)))  
                                )) :named @r2)
                            (! (choice ((z Int)) (and
                                    (>= (+ ((_ @int_of 3) x8) ((_ @int_of 3) y8)) z)    
                                    (>= (+ z ((_ @int_of 3) x8)) ((_ @int_of 3) y8))    
                                    (>= (+ z ((_ @int_of 3) y8)) ((_ @int_of 3) x8))    
                                    (>= 2 (+ z ((_ @int_of 3) x8) ((_ @int_of 3) y8)))  
                                )) :named @r3)
                            (! (choice ((z Int)) (and
                                    (>= (+ ((_ @int_of 4) x8) ((_ @int_of 4) y8)) z)    
                                    (>= (+ z ((_ @int_of 4) x8)) ((_ @int_of 4) y8))    
                                    (>= (+ z ((_ @int_of 4) y8)) ((_ @int_of 4) x8))    
                                    (>= 2 (+ z ((_ @int_of 4) x8) ((_ @int_of 4) y8)))  
                                )) :named @r4)
                            (! (choice ((z Int)) (and
                                    (>= (+ ((_ @int_of 5) x8) ((_ @int_of 5) y8)) z)    
                                    (>= (+ z ((_ @int_of 5) x8)) ((_ @int_of 5) y8))    
                                    (>= (+ z ((_ @int_of 5) y8)) ((_ @int_of 5) x8))    
                                    (>= 2 (+ z ((_ @int_of 5) x8) ((_ @int_of 5) y8)))  
                                )) :named @r5)
                            (! (choice ((z Int)) (and
                                    (>= (+ ((_ @int_of 6) x8) ((_ @int_of 6) y8)) z)    
                                    (>= (+ z ((_ @int_of 6) x8)) ((_ @int_of 6) y8))    
                                    (>= (+ z ((_ @int_of 6) y8)) ((_ @int_of 6) x8))    
                                    (>= 2 (+ z ((_ @int_of 6) x8) ((_ @int_of 6) y8)))  
                                )) :named @r6)
                            (! (choice ((z Int)) (and
                                    (>= (+ ((_ @int_of 7) x8) ((_ @int_of 7) y8)) z)    
                                    (>= (+ z ((_ @int_of 7) x8)) ((_ @int_of 7) y8))    
                                    (>= (+ z ((_ @int_of 7) y8)) ((_ @int_of 7) x8))    
                                    (>= 2 (+ z ((_ @int_of 7) x8) ((_ @int_of 7) y8)))  
                                )) :named @r7))
                )) :rule pbblast_bvxor)"#: false,
        }
        "Invalid 8-bit XOR (missing i=3)" {
            r#"(step t1 (cl (=
                        (bvxor x8 y8)
                        (@pbbterm
                            (! (choice ((z Int)) (and
                                    (>= (+ ((_ @int_of 0) x8) ((_ @int_of 0) y8)) z)
                                    (>= (+ z ((_ @int_of 0) x8)) ((_ @int_of 0) y8))
                                    (>= (+ z ((_ @int_of 0) y8)) ((_ @int_of 0) x8))
                                    (>= 2 (+ z ((_ @int_of 0) x8) ((_ @int_of 0) y8)))
                                )) :named @r0)
                            (! (choice ((z Int)) (and
                                    (>= (+ ((_ @int_of 1) x8) ((_ @int_of 1) y8)) z)    
                                    (>= (+ z ((_ @int_of 1) x8)) ((_ @int_of 1) y8))    
                                    (>= (+ z ((_ @int_of 1) y8)) ((_ @int_of 1) x8))    
                                    (>= 2 (+ z ((_ @int_of 1) x8) ((_ @int_of 1) y8)))  
                                )) :named @r1)
                            (! (choice ((z Int)) (and
                                    (>= (+ ((_ @int_of 2) x8) ((_ @int_of 2) y8)) z)    
                                    (>= (+ z ((_ @int_of 2) x8)) ((_ @int_of 2) y8))    
                                    (>= (+ z ((_ @int_of 2) y8)) ((_ @int_of 2) x8))    
                                    (>= 2 (+ z ((_ @int_of 2) x8) ((_ @int_of 2) y8)))  
                                )) :named @r2)
                            0 ; MISSING INDEX 3
                            (! (choice ((z Int)) (and
                                    (>= (+ ((_ @int_of 4) x8) ((_ @int_of 4) y8)) z)    
                                    (>= (+ z ((_ @int_of 4) x8)) ((_ @int_of 4) y8))    
                                    (>= (+ z ((_ @int_of 4) y8)) ((_ @int_of 4) x8))    
                                    (>= 2 (+ z ((_ @int_of 4) x8) ((_ @int_of 4) y8)))  
                                )) :named @r4)
                            (! (choice ((z Int)) (and
                                    (>= (+ ((_ @int_of 5) x8) ((_ @int_of 5) y8)) z)    
                                    (>= (+ z ((_ @int_of 5) x8)) ((_ @int_of 5) y8))    
                                    (>= (+ z ((_ @int_of 5) y8)) ((_ @int_of 5) x8))    
                                    (>= 2 (+ z ((_ @int_of 5) x8) ((_ @int_of 5) y8)))  
                                )) :named @r5)
                            (! (choice ((z Int)) (and
                                    (>= (+ ((_ @int_of 6) x8) ((_ @int_of 6) y8)) z)    
                                    (>= (+ z ((_ @int_of 6) x8)) ((_ @int_of 6) y8))    
                                    (>= (+ z ((_ @int_of 6) y8)) ((_ @int_of 6) x8))    
                                    (>= 2 (+ z ((_ @int_of 6) x8) ((_ @int_of 6) y8)))  
                                )) :named @r6)
                            (! (choice ((z Int)) (and
                                    (>= (+ ((_ @int_of 7) x8) ((_ @int_of 7) y8)) z)    
                                    (>= (+ z ((_ @int_of 7) x8)) ((_ @int_of 7) y8))    
                                    (>= (+ z ((_ @int_of 7) y8)) ((_ @int_of 7) x8))    
                                    (>= 2 (+ z ((_ @int_of 7) x8) ((_ @int_of 7) y8)))  
                                )) :named @r7))
                )) :rule pbblast_bvxor)"#: false,
        }
    }
}

#[test]
fn pbblast_bvand_1() {
    test_cases! {
        definitions = "
            (declare-const x1 (_ BitVec 1))
            (declare-const y1 (_ BitVec 1))
        ",
        "Valid 1-bit AND" {
            r#"(step t1 (cl (=
                        (bvand x1 y1)
                        (@pbbterm (! (choice ((z Int)) (and
                                                (>= ((_ @int_of 0) x1) z)
                                                (>= ((_ @int_of 0) y1) z)
                                                (>= (+ z 1) (+ ((_ @int_of 0) x1) ((_ @int_of 0) y1)))
                                            )) :named @r0))
                )) :rule pbblast_bvand)"#: true,
        }
        "Invalid 1-bit AND (missing constraint)" {
            r#"(step t1 (cl (=
                        (bvand x1 y1)
                        (@pbbterm (! (choice ((z Int)) (and
                                                (>= ((_ @int_of 0) x1) z)
                                                ;; Missing >= yi z
                                                (>= (+ z 1) (+ ((_ @int_of 0) x1) ((_ @int_of 0) y1)))
                                            )) :named @r0))
                )) :rule pbblast_bvand)"#: false,
        }
        "Invalid 1-bit AND (wrong choice binder)" {
            r#"(step t1 (cl (=
                        (bvand x1 y1)
                        (@pbbterm (! (choice ((z Int)) (and
                                                (>= ((_ @int_of 0) x1) 0)   ; should be z
                                                (>= ((_ @int_of 0) y1) z)
                                                (>= (+ z 1) (+ ((_ @int_of 0) x1) ((_ @int_of 0) y1)))
                                            )) :named @r0))
                )) :rule pbblast_bvand)"#: false,

            r#"(step t1 (cl (=
                        (bvand x1 y1)
                        (@pbbterm (! (choice ((z Int)) (and
                                                (>= ((_ @int_of 0) x1) z)
                                                (>= ((_ @int_of 0) y1) 0)   ; should be z
                                                (>= (+ z 1) (+ ((_ @int_of 0) x1) ((_ @int_of 0) y1)))
                                            )) :named @r0))
                )) :rule pbblast_bvand)"#: false,

            r#"(step t1 (cl (=
                        (bvand x1 y1)
                        (@pbbterm (! (choice ((z Int)) (and
                                                (>= ((_ @int_of 0) x1) z)   
                                                (>= ((_ @int_of 0) y1) z)
                                                ;      v--- should be z instead of 0
                                                (>= (+ 0 1) (+ ((_ @int_of 0) x1) ((_ @int_of 0) y1)))
                                            )) :named @r0))
                )) :rule pbblast_bvand)"#: false,
        }
    }
}

#[test]
fn pbblast_bvand_2() {
    test_cases! {
        definitions = "
            (declare-const x2 (_ BitVec 2))
            (declare-const y2 (_ BitVec 2))
        ",
        "Valid 2-bit AND" {
            r#"(step t1 (cl (=
                        (bvand x2 y2)
                        (@pbbterm (! (choice ((z Int)) (and
                                                (>= ((_ @int_of 0) x2) z)
                                                (>= ((_ @int_of 0) y2) z)
                                                (>= (+ z 1) (+ ((_ @int_of 0) x2) ((_ @int_of 0) y2)))
                                            )) :named @r0)
                                  (! (choice ((z Int)) (and
                                                (>= ((_ @int_of 1) x2) z)
                                                (>= ((_ @int_of 1) y2) z)
                                                (>= (+ z 1) (+ ((_ @int_of 1) x2) ((_ @int_of 1) y2)))
                                            )) :named @r1))
                    )) :rule pbblast_bvand)"#: true,
        }
       "Invalid 2-bit AND (wrong coefficient)" {
            r#"(step t1 (cl (=
                        (bvand x2 y2)
                        (@pbbterm (! (choice ((z Int)) (and
                                                (>= ((_ @int_of 0) x2) z)
                                                (>= (* 2 ((_ @int_of 0) y2)) z) ; invalid coefficient (* 2 ..)
                                                (>= (+ z 1) (+ ((_ @int_of 0) x2) ((_ @int_of 0) y2)))
                                            )) :named @r0)
                                  (! (choice ((z Int)) (and
                                                (>= ((_ @int_of 1) x2) z)
                                                (>= ((_ @int_of 1) y2) z)
                                                (>= (+ z 1) (+ ((_ @int_of 1) x2) ((_ @int_of 1) y2)))
                                            )) :named @r1))
                    )) :rule pbblast_bvand)"#: false,
        }
    }
}

#[test]
fn pbblast_bvand_2_short_circuit() {
    test_cases! {
        definitions = "
            (declare-const @x0 Int)
            (declare-const @x1 Int)
            (declare-const @y0 Int)
            (declare-const @y1 Int)
        ",
        "Valid 2-bit AND (short-circuit)" {
            r#"(step t1 (cl (=
                        (bvand (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                        (@pbbterm (! (choice ((z Int)) (and (>= @x0 z) (>= @y0 z) (>= (+ z 1) (+ @x0 @y0)))) :named @r0)
                                  (! (choice ((z Int)) (and (>= @x1 z) (>= @y1 z) (>= (+ z 1) (+ @x1 @y1)))) :named @r1))
                    )) :rule pbblast_bvand)"#: true,
        }
        // Too many binders, too few binders in choice...
        "Invalid 2-bit AND (wrong bit, short_circuit)" {
            r#"(step t1 (cl (=
                        (bvand (@pbbterm @x0 @x1) (@pbbterm @y0 @y1))
                        (@pbbterm (! (choice ((z Int)) (and (>= @x0 z) (>= @y0 z) (>= (+ z 1) (+ @x0 @y0)))) :named @r0)
                                 (! (choice ((z Int)) (and (>= @x0 z) (>= @y0 z) (>= (+ z 1) (+ @x0 @y0)))) :named @r1))
                                 ; Should be on @x1 and @y1 ----^    
                    )) :rule pbblast_bvand)"#: false,
        }
    }
}

#[test]
fn pbblast_bvand_8() {
    test_cases! {
        definitions = "
            (declare-const x8 (_ BitVec 8))
            (declare-const y8 (_ BitVec 8))
        ",
        "Valid 8-bit AND" {
            r#"(step t1 (cl (=
                        (bvand x8 y8)
                        (@pbbterm (! (choice ((z Int)) (and
                                                (>= ((_ @int_of 0) x8) z)
                                                (>= ((_ @int_of 0) y8) z)
                                                (>= (+ z 1) (+ ((_ @int_of 0) x8) ((_ @int_of 0) y8)))
                                            )) :named @r0)
                                  (! (choice ((z Int)) (and
                                                (>= ((_ @int_of 1) x8) z)
                                                (>= ((_ @int_of 1) y8) z)
                                                (>= (+ z 1) (+ ((_ @int_of 1) x8) ((_ @int_of 1) y8)))
                                            )) :named @r1)
                                   (! (choice ((z Int)) (and
                                                (>= ((_ @int_of 2) x8) z)
                                                (>= ((_ @int_of 2) y8) z)
                                                (>= (+ z 1) (+ ((_ @int_of 2) x8) ((_ @int_of 2) y8)))
                                            )) :named @r2)
                                   (! (choice ((z Int)) (and
                                                (>= ((_ @int_of 3) x8) z)
                                                (>= ((_ @int_of 3) y8) z)
                                                (>= (+ z 1) (+ ((_ @int_of 3) x8) ((_ @int_of 3) y8)))
                                            )) :named @r3)
                                   (! (choice ((z Int)) (and
                                                (>= ((_ @int_of 4) x8) z)
                                                (>= ((_ @int_of 4) y8) z)
                                                (>= (+ z 1) (+ ((_ @int_of 4) x8) ((_ @int_of 4) y8)))
                                            )) :named @r4)
                                   (! (choice ((z Int)) (and
                                                (>= ((_ @int_of 5) x8) z)
                                                (>= ((_ @int_of 5) y8) z)
                                                (>= (+ z 1) (+ ((_ @int_of 5) x8) ((_ @int_of 5) y8)))
                                            )) :named @r5)
                                   (! (choice ((z Int)) (and
                                                (>= ((_ @int_of 6) x8) z)
                                                (>= ((_ @int_of 6) y8) z)
                                                (>= (+ z 1) (+ ((_ @int_of 6) x8) ((_ @int_of 6) y8)))
                                            )) :named @r6)
                                   (! (choice ((z Int)) (and
                                                (>= ((_ @int_of 7) x8) z)
                                                (>= ((_ @int_of 7) y8) z)
                                                (>= (+ z 1) (+ ((_ @int_of 7) x8) ((_ @int_of 7) y8)))
                                            )) :named @r7))
                    )) :rule pbblast_bvand)"#: true,
        }
        "Invalid 8-bit AND (swapped order)" {
            r#"(step t1 (cl (=
                        (bvand x8 y8)
                        (@pbbterm (! (choice ((z Int)) (and
                                                (>= ((_ @int_of 0) x8) z)
                                                (>= ((_ @int_of 0) y8) z)
                                                (>= (+ z 1) (+ ((_ @int_of 0) x8) ((_ @int_of 0) y8)))
                                            )) :named @r0)
                                  (! (choice ((z Int)) (and
                                                (>= ((_ @int_of 1) x8) z)
                                                (>= ((_ @int_of 1) y8) z)
                                                (>= (+ z 1) (+ ((_ @int_of 1) x8) ((_ @int_of 1) y8)))
                                            )) :named @r1)
                                   (! (choice ((z Int)) (and
                                                (>= ((_ @int_of 2) x8) z)
                                                (>= ((_ @int_of 2) y8) z)
                                                (>= (+ z 1) (+ ((_ @int_of 2) x8) ((_ @int_of 2) y8)))
                                            )) :named @r2)
                                   (! (choice ((z Int)) (and
                                                (>= ((_ @int_of 3) x8) z)
                                                (>= ((_ @int_of 3) y8) z)
                                                (>= (+ z 1) (+ ((_ @int_of 3) x8) ((_ @int_of 3) y8)))
                                            )) :named @r3)
                                   (! (choice ((z Int)) (and
                                                (>= z ((_ @int_of 4) x8))   ; swapped order, should be (>= ((_ @int_of 4) x8) z)
                                                (>= ((_ @int_of 4) y8) z)
                                                (>= (+ z 1) (+ ((_ @int_of 4) x8) ((_ @int_of 4) y8)))
                                            )) :named @r4)
                                   (! (choice ((z Int)) (and
                                                (>= ((_ @int_of 5) x8) z)
                                                (>= ((_ @int_of 5) y8) z)
                                                (>= (+ z 1) (+ ((_ @int_of 5) x8) ((_ @int_of 5) y8)))
                                            )) :named @r5)
                                   (! (choice ((z Int)) (and
                                                (>= ((_ @int_of 6) x8) z)
                                                (>= ((_ @int_of 6) y8) z)
                                                (>= (+ z 1) (+ ((_ @int_of 6) x8) ((_ @int_of 6) y8)))
                                            )) :named @r6)
                                   (! (choice ((z Int)) (and
                                                (>= ((_ @int_of 7) x8) z)
                                                (>= ((_ @int_of 7) y8) z)
                                                (>= (+ z 1) (+ ((_ @int_of 7) x8) ((_ @int_of 7) y8)))
                                            )) :named @r7))
                    )) :rule pbblast_bvand)"#: false,
        }
    }
}

#[test]
fn pbblast_bvand_ith_bit() {
    test_cases! {
        definitions = "
            (declare-const x Int)
            (declare-const y Int)
            (define-fun id ((x Int)) Int x)
            (define-fun r () Int (choice ((z Int))
                                    (and (>= x z)
                                         (>= y z)
                                         (>= (+ z 1) (+ x y))
                                    )))
            (define-fun r_bad () Int (choice ((z Int)) (and (>= y z) (>= x z) (>= (+ z 1) (+ y x)))))
        ",
        "DEBUG: Match the ID term" {
            r#"(step t1 (cl (= 3 (id 3))
            ) :rule pbblast_bvand_ith_bit :args (x y))"#: true,
        }
        "DEBUG: Match the ID term" {
            r#"(step t1 (cl (= 3 (id 4))
            ) :rule pbblast_bvand_ith_bit :args (x y))"#: false,
        }

        // "Valid bvand ith bit" {
        //     r#"(step t1 (cl (and (>= x r)
        //                          (>= y r)
        //                          (>= (+ r 1) (+ x y)))
        //     ) :rule pbblast_bvand_ith_bit :args (x y))"#: true,
        // }
        // "Bvand ith bit - Swapped terms" {
        //     r#"(step t1 (cl (and (>= y r)
        //                          (>= x r)
        //                          (>= (+ r 1) (+ x y)))
        //     ) :rule pbblast_bvand_ith_bit :args (x y))"#: false,

        //     r#"(step t1 (cl (and (>= x r)
        //                          (>= x r)
        //                          (>= (+ r 1) (+ x y)))
        //     ) :rule pbblast_bvand_ith_bit :args (x y))"#: false,

        //     r#"(step t1 (cl (and (>= y r)
        //                          (>= y r)
        //                          (>= (+ r 1) (+ x y)))
        //     ) :rule pbblast_bvand_ith_bit :args (x y))"#: false,

        //     r#"(step t1 (cl (and (>= x r)
        //                          (>= y r)
        //                          (>= (+ r 1) (+ y x)))
        //     ) :rule pbblast_bvand_ith_bit :args (x y))"#: false,
        // }
        // "Bvand ith bit malformed choice" {
        //     r#"(step t1 (cl (and (>= x r_bad)
        //                          (>= y r_bad)
        //                          (>= (+ r_bad 1) (+ x y)))
        //     ) :rule pbblast_bvand_ith_bit :args (x y))"#: false,
        // }

    }
}
