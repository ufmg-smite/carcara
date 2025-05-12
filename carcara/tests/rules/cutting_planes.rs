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
