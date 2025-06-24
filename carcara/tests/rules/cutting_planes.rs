#[test]
fn cp_addition() {
    test_cases! {
       definitions = "
            (declare-fun x1 () Int)
            (declare-fun x2 () Int)
            (declare-fun x3 () Int)
        ",
        "Addition with Reduction" {
            r#"(assume c1 (>= (* 1 (- 1 x1)) 1))
               (assume c2 (>= (* 2 x1) 1))
               (step t1 (cl (>= (+ (* 1 x1) (* 0 x2)) 1)) :rule cp_addition :premises (c1 c2))"#: true,

            r#"(assume c1 (>= (* 2 x1) 1))
               (assume c2 (>= (* 1 (- 1 x1)) 1))
               (step t1 (cl (>= (* 1 x1) 1)) :rule cp_addition :premises (c1 c2))"#: true,

            r#"(assume c1 (>= (+ (* 2 x1) (* 3 x2)) 2))
               (assume c2 (>= (+ (* 1 (- 1 x1)) (* 3 (- 1 x2))) 4))
               (step t1 (cl (>= (* 1 x1) 2)) :rule cp_addition :premises (c1 c2))"#: true,

            r#"(assume c1 (>= (* 1 x1) 0))
               (assume c2 (>= (* 1 (- 1 x1)) 2))
               (step t1 (cl (>= 0 1)) :rule cp_addition :premises (c1 c2))"#: true,

            r#"(assume c1 (>= (+ (* 1 x1) (* 2 x2)) 4))
               (assume c2 (>= (+ (* 1 (- 1 x1)) (* 2 (- 1 x2))) 0))
               (step t1 (cl (>= 0 1)) :rule cp_addition :premises (c1 c2))"#: true,
        }
        "Simple working examples" {
            r#"(assume c1 (>= (* 1 x1) 1))
               (step t1 (cl (>= (* 2 x1) 2)) :rule cp_addition :premises (c1 c1))"#: true,

            r#"(assume c1 (>= (* 1 x1) 1))
               (assume c2 (>= (* 1 x2) 1))
               (step t1 (cl (>= (+ (* 1 x1) (* 1 x2)) 2)) :rule cp_addition :premises (c1 c2))"#: true,

            r#"(assume c1 (>= (+ (* 1 x1) (* 2 x2)) 1))
               (assume c2 (>= (+ (* 1 x2) (* 1 x1)) 1))
               (step t1 (cl (>= (+ (* 2 x1) (* 3 x2)) 2)) :rule cp_addition :premises (c1 c2))"#: true,

        }
        "Missing Terms" {
            r#"(assume c1 (>= (* 1 x1) 1))
               (assume c2 (>= (* 1 x2) 1))
               (step t1 (cl (>= (* 1 x1) 2)) :rule cp_addition :premises (c1 c2))"#: false,

            r#"(assume c1 (>= (* 1 x1) 1))
               (assume c2 (>= (* 1 x2) 1))
               (step t1 (cl (>= (* 1 x2) 2)) :rule cp_addition :premises (c1 c2))"#: false,

            r#"(assume c1 (>= (* 1 x1) 1))
               (assume c2 (>= (* 1 x2) 1))
               (step t1 (cl (>= (+ (* 1 x1) (* 1 x2) (* 1 x3)) 2)) :rule cp_addition :premises (c1 c2))"#: false,

            r#"(assume c1 (>= (+ (* 1 x1) (* 2 x2) (* 1 x3)) 1))
               (assume c2 (>= (+ (* 1 x2) (* 1 x1)) 1))
               (step t1 (cl (>= (+ (* 2 x1) (* 3 x2)) 2)) :rule cp_addition :premises (c1 c2))"#: false,

        }
        "Wrong Addition" {
            r#"(assume c1 (>= (+ (* 1 x1) (* 2 x2)) 1))
               (assume c2 (>= (+ (* 1 x2) (* 1 x1)) 1))
               (step t1 (cl (>= (+ (* 2 x1) (* 2 x2)) 2)) :rule cp_addition :premises (c1 c2))"#: false,

            r#"(assume c1 (>= (+ (* 1 x1) (* 2 x2)) 1))
               (assume c2 (>= (+ (* 1 x2) (* 1 x1)) 1))
               (step t1 (cl (>= (+ (* 2 x1) (* 3 x2)) 3)) :rule cp_addition :premises (c1 c2))"#: false,
        }
        "Trailing Zero" {
            r#"(assume c1 (>= (+ (* 1 (- 1 x1)) 0) 1))
               (assume c2 (>= (+ (* 2 x1) 0) 1))
               (step t1 (cl (>= (+ (* 1 x1) (* 0 x2) 0) 1)) :rule cp_addition :premises (c1 c2))"#: false,

            r#"(assume c1 (>= (+ (* 2 x1) 0) 1))
               (assume c2 (>= (+ (* 1 (- 1 x1)) 0) 1))
               (step t1 (cl (>= (+ (* 1 x1) 0) 1)) :rule cp_addition :premises (c1 c2))"#: false,

            r#"(assume c1 (>= (+ (* 2 x1) (* 3 x2) 0) 2))
               (assume c2 (>= (+ (* 1 (- 1 x1)) (* 3 (- 1 x2)) 0) 4))
               (step t1 (cl (>= (+ (* 1 x1) 0) 2)) :rule cp_addition :premises (c1 c2))"#: false,

            r#"(assume c1 (>= (+ (* 1 x1) 0) 1))
               (step t1 (cl (>= (+ (* 2 x1) 0) 2)) :rule cp_addition :premises (c1 c1))"#: false,

            r#"(assume c1 (>= (+ (* 1 x1) 0) 1))
               (assume c2 (>= (+ (* 1 x2) 0) 1))
               (step t1 (cl (>= (+ (* 1 x1) (* 1 x2) 0) 2)) :rule cp_addition :premises (c1 c2))"#: false,

            r#"(assume c1 (>= (+ (* 1 x1) (* 2 x2) 0) 1))
               (assume c2 (>= (+ (* 1 x2) (* 1 x1) 0) 1))
               (step t1 (cl (>= (+ (* 2 x1) (* 3 x2) 0) 2)) :rule cp_addition :premises (c1 c2))"#: false,

        }
    }
}

#[test]
fn cp_multiplication() {
    test_cases! {
        definitions = "
            (declare-fun x1 () Int)
            (declare-fun x2 () Int)
            (declare-fun x3 () Int)
        ",
        "Simple working examples" {
            r#"(assume c1 (>= (* 1 x1) 1))
               (step t1 (cl (>= (* 2 x1) 2)) :rule cp_multiplication :premises (c1) :args (2))"#: true,
            r#"(assume c1 (>= (+ (* 1 x1) (* 2 x2)) 1))
               (step t1 (cl (>= (+ (* 2 x1) (* 4 x2)) 2)) :rule cp_multiplication :premises (c1) :args (2))"#: true,
            r#"(assume c1 (>= (+ (* 1 x1) (* 2 x2) (* 3 x3)) 1))
               (step t1 (cl (>= (+ (* 2 x1) (* 4 x2) (* 6 x3)) 2)) :rule cp_multiplication :premises (c1) :args (2))"#: true,
            r#"(assume c1 (>= (+ (* 1 x1) (* 2 (- 1 x2)) (* 3 x3)) 1))
               (step t1 (cl (>= (+ (* 2 x1) (* 4 (- 1 x2)) (* 6 x3)) 2)) :rule cp_multiplication :premises (c1) :args (2))"#: true,
        }
        "Wrong number of premises" {
            r#"(assume c1 (>= x1 1))
               (step t1 (cl (>= (* 2 x1) 2)) :rule cp_multiplication :args (2))"#: false,
            r#"(assume c1 (>= x1 1))
               (step t1 (cl (>= (* 2 x1) 2)) :rule cp_multiplication :premises (c1 c1) :args (2))"#: false,
        }
        "Wrong number of args" {
            r#"(assume c1 (>= x1 1))
               (step t1 (cl (>= (* 2 x1) 2)) :rule cp_multiplication :premises (c1))"#: false,
            r#"(assume c1 (>= x1 1))
               (step t1 (cl (>= (* 2 x1) 2)) :rule cp_multiplication :premises (c1) :args (2 3))"#: false,
        }
        "Wrong number of clauses in the conclusion" {
            r#"(assume c1 (>= (* 1 x1) 1))
               (step t1 (cl (>= (+ (* 2 x1) (* 2 x2)) 2)) :rule cp_multiplication :premises (c1) :args (2))"#: false,

            r#"(assume c1 (>= (+ (* 1 x1) (* 2 x2)) 1))
               (step t1 (cl (>= (* 2 x1) 2)) :rule cp_multiplication :premises (c1) :args (2))"#: false,
        }
        "Wrong product" {
            r#"(assume c1 (>= (* 1 x1) 1))
               (step t1 (cl (>= (* 3 x1) 2)) :rule cp_multiplication :premises (c1) :args (2))"#: false,
            r#"(assume c1 (>= (+ (* 1 x1) (* 2 x2)) 1))
               (step t1 (cl (>= (+ (* 1 x1) (* 4 x2)) 2)) :rule cp_multiplication :premises (c1) :args (2))"#: false,
            r#"(assume c1 (>= (+ (* 1 x1) (* 2 x2) (* 3 x3)) 1))
               (step t1 (cl (>= (+ (* 2 x1) (* 4 x2) (* 3 x3)) 2)) :rule cp_multiplication :premises (c1) :args (2))"#: false,
        }
        "Trailing Zero" {
            r#"(assume c1 (>= (+ (* 1 x1) 0) 1))
               (step t1 (cl (>= (+ (* 2 x1) 0) 2)) :rule cp_multiplication :premises (c1) :args (2))"#: false,
            r#"(assume c1 (>= (+ (* 1 x1) (* 2 x2) 0) 1))
               (step t1 (cl (>= (+ (* 2 x1) (* 4 x2) 0) 2)) :rule cp_multiplication :premises (c1) :args (2))"#: false,
            r#"(assume c1 (>= (+ (* 1 x1) (* 2 x2) (* 3 x3) 0) 1))
               (step t1 (cl (>= (+ (* 2 x1) (* 4 x2) (* 6 x3) 0) 2)) :rule cp_multiplication :premises (c1) :args (2))"#: false,
            r#"(assume c1 (>= (+ (* 1 x1) (* 2 (- 1 x2)) (* 3 x3) 0) 1))
               (step t1 (cl (>= (+ (* 2 x1) (* 4 (- 1 x2)) (* 6 x3) 0) 2)) :rule cp_multiplication :premises (c1) :args (2))"#: false,
        }

    }
}

#[test]
fn cp_division() {
    test_cases! {
        definitions = "
            (declare-fun x1 () Int)
            (declare-fun x2 () Int)
        ",
        "Simple working examples" {
            r#"(assume c1 (>= (* 2 x1) 2))
               (step t1 (cl (>= (* 1 x1) 1)) :rule cp_division :premises (c1) :args (2) )"#: true,
            r#"(assume c1 (>= (* 2 (- 1 x1)) 2))
               (step t1 (cl (>= (* 1 (- 1 x1)) 1)) :rule cp_division :premises (c1) :args (2) )"#: true,
        }
        "Wrong division" {
            r#"(assume c1 (>= (* 2 x1) 2))
               (step t1 (cl (>= (* 2 x1) 1)) :rule cp_division :premises (c1) :args (2) )"#: false,
            r#"(assume c1 (>= (* 2 x1) 2))
               (step t1 (cl (>= (* 1 x1) 2)) :rule cp_division :premises (c1) :args (2) )"#: false,
        }
        "Division by Zero" {
            r#"(assume c1 (>= (* 2 x1) 2))
               (step t1 (cl (>= (* 1 x1) 1)) :rule cp_division :premises (c1) :args (0) )"#: false,
            r#"(assume c1 (>= (* 2 (- 1 x1)) 2))
               (step t1 (cl (>= (* 1 (- 1 x1)) 1)) :rule cp_division :premises (c1) :args (0) )"#: false,
        }
        "Division by Negative" {
            r#"(assume c1 (>= (* 2 x1) 2))
               (step t1 (cl (>= (* 1 x1) 1)) :rule cp_division :premises (c1) :args (-2) )"#: false,
            r#"(assume c1 (>= (* 2 (- 1 x1)) 2))
               (step t1 (cl (>= (* 1 (- 1 x1)) 1)) :rule cp_division :premises (c1) :args (-2) )"#: false,
        }
        "Ceiling of Division" {
            r#"(assume c1 (>= (* 3 x1) 2))
               (step t1 (cl (>= (* 2 x1) 1)) :rule cp_division :premises (c1) :args (2) )"#: true,
            r#"(assume c1 (>= (* 3 x1) 2))
               (step t1 (cl (>= (* 1 x1) 1)) :rule cp_division :premises (c1) :args (2) )"#: false,

            r#"(assume c1 (>= (* 7 x1) 2))
               (step t1 (cl (>= (* 4 x1) 1)) :rule cp_division :premises (c1) :args (2) )"#: true,
            r#"(assume c1 (>= (* 7 x1) 2))
               (step t1 (cl (>= (* 3 x1) 1)) :rule cp_division :premises (c1) :args (2) )"#: false,

            r#"(assume c1 (>= (* 9 x1) 2))
               (step t1 (cl (>= (* 5 x1) 1)) :rule cp_division :premises (c1) :args (2) )"#: true,
            r#"(assume c1 (>= (* 9 x1) 2))
               (step t1 (cl (>= (* 4 x1) 1)) :rule cp_division :premises (c1) :args (2) )"#: false,

            r#"(assume c1 (>= (* 10 x1) 3))
               (step t1 (cl (>= (* 4 x1) 1)) :rule cp_division :premises (c1) :args (3) )"#: true,
            r#"(assume c1 (>= (* 10 x1) 3))
               (step t1 (cl (>= (* 3 x1) 1)) :rule cp_division :premises (c1) :args (3) )"#: false,
       }
       "Missing terms" {
            r#"(assume c1 (>= (+ (* 2 x1) (* 1 x2)) 2))
               (step t1 (cl (>= (* 1 x1) 1)) :rule cp_division :premises (c1) :args (2) )"#: false,

             r#"(assume c1 (>= (* 2 x1) 2))
               (step t1 (cl (>= (+ (* 1 x1) (* 1 x2)) 1)) :rule cp_division :premises (c1) :args (2) )"#: false,
       }
       "Trailing Zero" {
            r#"(assume c1 (>= (+ (* 2 x1) 0) 2))
               (step t1 (cl (>= (+ (* 1 x1) 0) 1)) :rule cp_division :premises (c1) :args (2) )"#: false,
            r#"(assume c1 (>= (+ (* 2 (- 1 x1)) 0) 2))
               (step t1 (cl (>= (+ (* 1 (- 1 x1)) 0) 1)) :rule cp_division :premises (c1) :args (2) )"#: false,
        }

    }
}

#[test]
fn cp_saturation() {
    test_cases! {
        definitions = "
            (declare-fun x1 () Int)
            (declare-fun x2 () Int)
            (declare-fun x3 () Int)
        ",
        "Simple working examples" {
            r#"(assume c1 (>= (* 2 x1) 1))
               (step t1 (cl (>= (* 1 x1) 1)) :rule cp_saturation :premises (c1))"#: true,

            r#"(assume c1 (>= (+ (* 2 x1) (* 5 x2) (* 3 x3)) 3))
               (step t1 (cl (>= (+ (* 2 x1) (* 3 x2) (* 3 x3)) 3)) :rule cp_saturation :premises (c1))"#: true,

            r#"(assume c1 (>= (+ (* 3 x1) (* 4 x2) (* 5 x3)) 3))
               (step t1 (cl (>= (+ (* 3 x1) (* 3 x2) (* 3 x3)) 3)) :rule cp_saturation :premises (c1))"#: true,

            r#"(assume c1 (>= (+ (* 3 x1) (* 4 x2) (* 5 (- 1 x3))) 3))
               (step t1 (cl (>= (+ (* 3 x1) (* 3 x2) (* 3 (- 1 x3))) 3)) :rule cp_saturation :premises (c1))"#: true,

        }
        "Wrong saturation" {
            r#"(assume c1 (>= (* 2 x1) 1))
               (step t1 (cl (>= (* 2 x1) 1)) :rule cp_saturation :premises (c1))"#: false,

            r#"(assume c1 (>= (* 2 x1) 1))
               (step t1 (cl (>= (* 0 x1) 1)) :rule cp_saturation :premises (c1))"#: false,

            r#"(assume c1 (>= (+ (* 3 x1) (* 4 x2) (* 5 x3)) 3))
               (step t1 (cl (>= (+ (* 3 x1) (* 3 x2) (* 2 x3)) 3)) :rule cp_saturation :premises (c1))"#: false,

        }
        "Missing terms" {
            r#"(assume c1 (>= (+ (* 3 x1) (* 4 x2) (* 5 x3)) 3))
               (step t1 (cl (>= (+ (* 3 x1) (* 3 x2)) 3)) :rule cp_saturation :premises (c1))"#: false,

            r#"(assume c1 (>= (+ (* 3 x1) (* 4 x2)) 3))
               (step t1 (cl (>= (+ (* 3 x1) (* 3 x2) (* 3 x3)) 3)) :rule cp_saturation :premises (c1))"#: false,
        }
        "Trailing Zero" {
            r#"(assume c1 (>= (+ (* 2 x1) 0) 1))
               (step t1 (cl (>= (+ (* 1 x1) 0) 1)) :rule cp_saturation :premises (c1))"#: false,

            r#"(assume c1 (>= (+ (* 2 x1) (* 5 x2) (* 3 x3) 0) 3))
               (step t1 (cl (>= (+ (* 2 x1) (* 3 x2) (* 3 x3) 0) 3)) :rule cp_saturation :premises (c1))"#: false,

            r#"(assume c1 (>= (+ (* 3 x1) (* 4 x2) (* 5 x3) 0) 3))
               (step t1 (cl (>= (+ (* 3 x1) (* 3 x2) (* 3 x3) 0) 3)) :rule cp_saturation :premises (c1))"#: false,

            r#"(assume c1 (>= (+ (* 3 x1) (* 4 x2) (* 5 (- 1 x3)) 0) 3))
               (step t1 (cl (>= (+ (* 3 x1) (* 3 x2) (* 3 (- 1 x3)) 0) 3)) :rule cp_saturation :premises (c1))"#: false,
        }

    }
}

#[test]
fn cp_literal() {
    test_cases! {
        definitions = "
            (declare-fun l () Int)
            (define-fun neg_l () Int (- 1 l))
        ",
        "cp_literal correctly applied" {
            r#"(step t1 (cl (>= l 0)) :rule cp_literal :args (l))"#: true,
            r#"(step t1 (cl (>= (* 1 l) 0)) :rule cp_literal :args (l))"#: true,
            r#"(step t1 (cl (>= neg_l 0)) :rule cp_literal :args (neg_l))"#: true,
            r#"(step t1 (cl (>= (* 1 neg_l) 0)) :rule cp_literal :args (neg_l))"#: true,
        }
        "cp_literal invalid (coefficients)" {
            r#"(step t1 (cl (>= (* 1 l) 0)) :rule cp_literal :args ((* 2 l)))"#: false,
            r#"(step t1 (cl (>= (* 2 l) 0)) :rule cp_literal :args ((* 2 l)))"#: false,

            r#"(step t1 (cl (>= (* 1 neg_l) 0)) :rule cp_literal :args ((* 2 neg_l)))"#: false,
            r#"(step t1 (cl (>= (* 2 neg_l) 0)) :rule cp_literal :args ((* 2 neg_l)))"#: false,

            // ! THIS SHOULD BE AVOIDED WHEN l is a PSEUDO BOOLEAN
            r#"(step t1 (cl (>= (* 1 (* 2 l)) 0)) :rule cp_literal :args ((* 2 l)))"#: true,
            r#"(step t1 (cl (>= (* 1 (* 2 neg_l)) 0)) :rule cp_literal :args ((* 2 neg_l)))"#: true,
        }
        "cp_literal invalid (number of args)" {
            r#"(step t1 (cl (>= (* 1 l) 0)) :rule cp_literal)"#: false,
            r#"(step t1 (cl (>= (* 1 l) 0)) :rule cp_literal :args (l neg_l))"#: false,
            r#"(step t1 (cl (>= (* 1 neg_l) 0)) :rule cp_literal :args (neg_l l))"#: false,
        }
    }
}

#[test]
fn cp_normalize() {
    test_cases! {
        definitions = "
            (declare-fun a () Int)
            (declare-fun b () Int)
            (declare-fun c () Int)
            (declare-fun d () Int)
            (declare-fun r0 () Int)
            (declare-fun r1 () Int)
            (declare-fun z0 () Int)
            (declare-fun z1 () Int)
        ",
        "Term is already normalized" {
            r#"(step t1 (cl (= (>= a 0) (>= a 0))) :rule cp_normalize)"#: true,
            r#"(step t1 (cl (= (>= (- 1 a) 0) (>= (- 1 a) 0))) :rule cp_normalize)"#: true,
            r#"(step t1 (cl (= (>= (* 2 a) 0) (>= (* 2 a) 0))) :rule cp_normalize)"#: true,

            r#"(step t1 (cl (= (>= (+ a b) 0) (>= (+ a b) 0))) :rule cp_normalize)"#: true,
            r#"(step t1 (cl (= (>= (+ (- 1 a) b) 0) (>= (+ (- 1 a) b) 0))) :rule cp_normalize)"#: true,
            r#"(step t1 (cl (= (>= (+ (* 2 a) (* 3 b)) 0) (>= (+ (* 2 a) (* 3 b)) 0))) :rule cp_normalize)"#: true,
        }
        "Negative coefficient is pushed" {
            r#"(step t1 (cl (= (>= (* -1 a) 0) (>= (* 1 (- 1 a)) 1))) :rule cp_normalize)"#: true,
            r#"(step t1 (cl (= (>= (* -1 a) 0) (>= (- 1 a) 1))) :rule cp_normalize)"#: true,
            r#"(step t1 (cl (= (>= (* -5 a) 0) (>= (* 5 (- 1 a)) 5))) :rule cp_normalize)"#: true,
            r#"(step t1 (cl (= (>= (+ (* -1 a) (* -3 b)) 0) (>= (+ (- 1 a) (* 3 (- 1 b))) 4))) :rule cp_normalize)"#: true,
            r#"(step t1 (cl (= (>= (+ (* -5 a) b) 0) (>= (+ (* 5 (- 1 a)) b) 5))) :rule cp_normalize)"#: true,
        }
        "Other relations are eliminated" {
            r#"(step t1 (cl (= (<= a 0) (>= (- 1 a) 1))) :rule cp_normalize)"#: true,
            r#"(step t1 (cl (= (<= (- 1 a) 0) (>= a 1))) :rule cp_normalize)"#: true,
            r#"(step t1 (cl (= (<= (* -1 a) 0) (>= a 0))) :rule cp_normalize)"#: true,
            r#"(step t1 (cl (= (> a 0) (>= a 1))) :rule cp_normalize)"#: true,
            r#"(step t1 (cl (= (< a 0) (>= (- 1 a) 2))) :rule cp_normalize)"#: true,
            r#"(step t1 (cl (= (= a 0) (and (>= a 0) (>= (- 1 a) 1)))) :rule cp_normalize)"#: true,
            r#"(step t1 (cl (= (= (* 1 a) 0) (and (>= a 0) (>= (- 1 a) 1)))) :rule cp_normalize)"#: true,
        }
        "Constants are moved to the right" {
            r#"(step t1 (cl (= (>= (+ a 1) 0) (>= a -1))) :rule cp_normalize)"#: true,
            r#"(step t1 (cl (= (>= (+ a b 1) 0) (>= (+ a b) -1))) :rule cp_normalize)"#: true,
            r#"(step t1 (cl (= (>= (+ a 3 b 1) 0) (>= (+ a b) -4))) :rule cp_normalize)"#: true,
        }
        "Variables are moved to the left" {
            r#"(step t1 (cl (= (>= a b) (>= (+ a (- 1 b)) 1))) :rule cp_normalize)"#: true,
            r#"(step t1 (cl (= (>= a (+ b c)) (>= (+ a (- 1 b) (- 1 c)) 2))) :rule cp_normalize)"#: true,
            r#"(step t1 (cl (= (>= (+ a 2) (+ b c)) (>= (+ a (- 1 b) (- 1 c)) 0))) :rule cp_normalize)"#: true,
        }
        "Invalid relations" {
            r#"(step t1 (cl (= (and true true) (>= a 0))) :rule cp_normalize)"#: false,
            r#"(step t1 (cl (not (= (>= a 1) (>= a 0)))) :rule cp_normalize)"#: false,
            r#"(step t1 (cl (not (= (+ a 1) (+ 1 a)))) :rule cp_normalize)"#: false,
            r#"(step t1 (cl (= (<= (* -1 a 1) 0) (>= a 0))) :rule cp_normalize)"#: false,
            r#"(step t1 (cl (= (>= (+ a 1) 0) (>= a 0))) :rule cp_normalize)"#: false,
            r#"(step t1 (cl (= (= a 0 0) (and (>= a 0) (>= (* -1 a) 1)))) :rule cp_normalize)"#: false,
            r#"(step t1 (cl (= true (>= a 0))) :rule cp_normalize)"#: false,
        }
        "Instance of bigger example"  {
            r#"(step t1 (cl (=
                        (= (-       ;; This syntax is not a flat summation list
                             (+ (* 1 r0) (* 2 r1))
                             (+ (* 1 z0) (* 2 z1))
                           ) 0)
                        (and
                            (>= (+
                                    (* 1 r0)
                                    (* 2 r1)
                                    (* 1 (- 1 z0))
                                    (* 2 (- 1 z1))
                                ) 3)
                            (>= (+
                                    (* 1 (- 1 r0))
                                    (* 2 (- 1 r1))
                                    (* 1 z0)
                                    (* 2 z1)
                                ) 3)
                        )
                    )) :rule cp_normalize)"#: true,
            r#"(step t1 (cl (=
                        (= (-       
                             (+ (* 1 r0) (* 2 r1))
                             (+ (* 4 z0) (* 2 z1))
                           ) 0)
                        (and
                            (>= (+
                                    (* 1 r0)
                                    (* 2 r1)
                                    (* 4 (- 1 z0))
                                    (* 2 (- 1 z1))
                                ) 6)
                            (>= (+
                                    (* 1 (- 1 r0))
                                    (* 2 (- 1 r1))
                                    (* 4 z0)
                                    (* 2 z1)
                                ) 3)
                        )
                    )) :rule cp_normalize)"#: true,

        }
        "Validates variable list length" {
            r#"(step t1 (cl (=
                (= (- (+ (* 1 a) (* 2 b)) (+ (* 1 c) (* 2 d))) 0)
                (and (>= (+ a (* 2 b) (- 1 c) (* 2 (- 1 d))) 3)
                     (>= (+ (- 1 a) (* 2 (- 1 b)) (* 1 c) (* 2 d)) 3)
                )
            )) :rule cp_normalize)"#: true,
            r#"(step t1 (cl (=
                ; Constants b, c and d were forgotten on RHS                        
                (= (- (+ (* 1 a) (* 2 b)) (+ (* 1 c) (* 2 d))) 0)
                (and (>= a 3)
                     (>= (- 1 a) 3)
                )
            )) :rule cp_normalize)"#: false,
            r#"(step t1 (cl (=
                (= (- (+ (* 1 a) (* 2 b)) (+ (* 1 c) (* 2 d))) 0)
                ; Constants c and d were forgotten on RHS                        
                (and (>= (+ a (* 2 b)) 3)
                     (>= (+ (- 1 a) (* 2 (- 1 b))) 3)
                )
            )) :rule cp_normalize)"#: false,
        }
        "Unfolds enough constants" {
            r#"(step t1 (cl (=
                ;; See how 1 and 2*0 collapse into the constant on RHS of >=
                (= (- (+ a (* 2 b)) (+ 1 (* 2 0))) 0)
                (and (>= (+ a (* 2 b)) 1)
                     (>= (+ (- 1 a) (* 2 (- 1 b))) 2)
                )
            )) :rule cp_normalize)"#: true,

            r#"(step t1 (cl (=
                (= (- (+ (* 1 a) (* 2 b)) (+ (* 1 1) (* 2 0))) 0)
                ;; Consts must be on RHS --v------------v
                (and (>= (+ a (* 2 b) (- 1 1) (* 2 (- 1 0))) 3)
                     (>= (+ (- 1 a) (* 2 (- 1 b)) (* 1 1) (* 2 0)) 3)
                )
            )) :rule cp_normalize)"#: false,
        }
        "Improper normalized term" {
            r#"(step t1 (cl (=
                (= a 0)
                (and
                    (>= (+ a (* 1 1)) 0)
                    (>= (- 1 a) 1)
                )
            )) :rule cp_normalize)"#: false,
        }
    }
}
