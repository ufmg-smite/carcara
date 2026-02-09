#[test]
fn poly_simp() {
    test_cases! {
        definitions = "
            (declare-fun k () Int)
            (declare-fun n () Int)
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
    }
}
