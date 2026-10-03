#[test]
fn poly_simp() {
    test_cases! {
        definitions = "
            (declare-fun k () Int)
            (declare-fun n () Int)
            (declare-fun a () Int)
            (declare-fun x () Real)
            (declare-fun y () Real)
        ",
        "Simple working examples" {
            "(step t1 (cl (= (+ (* 2 k) (* 1 n)) (+ n (* k 2)))) :rule poly_simp)": true,
            "(step t1 (cl (=
                (+ (* 2.0 y) (* 1.0 x))
                (+ x (* y 2.0))
            )) :rule poly_simp)": true,
        }
        "Coefficient cancellation" {
            "(step t1 (cl (=
                (+ (* 2.0 x) (* (- 2.0) x) y)
                (* y 1.0)
            )) :rule poly_simp)": true,
            "(step t1 (cl (= (+ 2 (- 1) (- 1)) 0)) :rule poly_simp)": true,
            "(step t1 (cl (= (* 0.0 x) 0.0)) :rule poly_simp)": true,
        }
        "Failing examples" {
            "(step t1 (cl (= (+ k k) (+ k 0))) :rule poly_simp)": false,
            "(step t1 (cl (= (* 2.0 x) (+ 2.0 x))) :rule poly_simp)": false,
        }
        "Regression" {
            "(step t1 (cl (= (- a (* 2 2)) (+ a (* -1 (* 2 2))) )) :rule poly_simp)": true,
            "(step t1 (cl (= (* 0 (div 0 0)) 0)) :rule poly_simp)": true,
        }
    }
}

#[test]
fn poly_simp_rel() {
    test_cases! {
        definitions = "
            (declare-fun x () Real)
            (declare-fun y () Real)
            (declare-fun z () Real)
            (declare-fun w () Real)
            (declare-fun a () Int)
            (declare-fun b () Int)
            (declare-fun c () Int)
            (declare-fun d () Int)
            (declare-fun u () (_ BitVec 4))
            (declare-fun v () (_ BitVec 4))
            (declare-fun s () (_ BitVec 4))
            (declare-fun t () (_ BitVec 4))
        ",
        "Simple working examples" {
            "(assume h1 (= (* 2.0 (- x y)) (* 1.0 (- z w))))
            (step t1 (cl (= (< x y) (< z w))) :rule poly_simp_rel :premises (h1))": true,

            "(assume h1 (= (* (/ 1.0 2.0) (- x y)) (* 3.0 (- z w))))
            (step t1 (cl (= (>= x y) (>= z w))) :rule poly_simp_rel :premises (h1))": true,
        }
        "Negative coefficients" {
            "(assume h1 (= (* (- 2.0) (- x y)) (* (- 1.0) (- z w))))
            (step t1 (cl (= (<= x y) (<= z w))) :rule poly_simp_rel :premises (h1))": true,

            // For equalities, the coefficients may have different signs
            "(assume h1 (= (* 2.0 (- x y)) (* (- 3.0) (- z w))))
            (step t1 (cl (= (= x y) (= z w))) :rule poly_simp_rel :premises (h1))": true,
        }
        "Integer differences" {
            "(assume h1 (= (* 1.0 (to_real (- a b))) (* 3.0 (to_real (- c d)))))
            (step t1 (cl (= (> a b) (> c d))) :rule poly_simp_rel :premises (h1))": true,
        }
        "Bitvectors" {
            "(assume h1 (= (bvmul #b0011 (bvsub u v)) (bvmul #b0001 (bvsub s t))))
            (step t1 (cl (= (= u v) (= s t))) :rule poly_simp_rel :premises (h1))": true,
        }
        "Division by zero in coefficient" {
            "(assume h1 (= (* (/ 1.0 0.0) (- x y)) (* 1.0 (- x y))))
            (step t1 (cl (= (< x y) (< x y))) :rule poly_simp_rel :premises (h1))": false,
        }
    }
}
