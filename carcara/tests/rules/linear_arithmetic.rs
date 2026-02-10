#[test]
fn la_rw_eq() {
    test_cases! {
        definitions = "
            (declare-fun a () Int)
            (declare-fun b () Int)
            (declare-fun x () Real)
            (declare-fun y () Real)
        ",
        "Simple working examples" {
            "(step t1 (cl (= (= a b) (and (<= a b) (<= b a)))) :rule la_rw_eq)": true,
            "(step t1 (cl (= (= x y) (and (<= x y) (<= y x)))) :rule la_rw_eq)": true,
        }
        "Clause term is not of the correct form" {
            "(step t1 (cl (= (= b a) (and (<= a b) (<= b a)))) :rule la_rw_eq)": false,
            "(step t1 (cl (= (= x y) (and (<= x y) (<= x y)))) :rule la_rw_eq)": false,
        }
    }
}

#[test]
fn la_generic() {
    test_cases! {
        definitions = "
            (declare-fun a () Real)
            (declare-fun b () Real)
            (declare-fun c () Real)
            (declare-fun m () Int)
            (declare-fun n () Int)
        ",
        "Simple working examples" {
            "(step t1 (cl (> a 0.0) (<= a 0.0)) :rule la_generic :args (1.0 1.0))": true,
            "(step t1 (cl (>= a 0.0) (< a 0.0)) :rule la_generic :args (1.0 1.0))": true,
            "(step t1 (cl (<= 0.0 0.0)) :rule la_generic :args (1.0))": true,

            "(step t1 (cl (< (+ a b) 1.0) (> (+ a b) 0.0))
                :rule la_generic :args (1.0 (- 1.0)))": true,

            "(step t1 (cl (<= (+ a (- b a)) b)) :rule la_generic :args (1.0))": true,

            "(step t1 (cl (not (<= (- a b) (- c 1.0))) (<= (+ 1.0 (- a c)) b))
                :rule la_generic :args (1.0 1.0))": true,
        }
        "Empty clause" {
            "(step t1 (cl) :rule la_generic)": false,
        }
        "Wrong number of arguments" {
            "(step t1 (cl (>= a 0.0) (< a 0.0)) :rule la_generic :args (1.0 1.0 1.0))": false,
        }
        "Invalid argument term" {
            "(step t1 (cl (>= a 0.0) (< a 0.0)) :rule la_generic :args (1.0 b))": false,
        }
        "Clause term is not of the correct form" {
            "(step t1 (cl (ite (= a b) false true)) :rule la_generic :args (1.0))": false,
            "(step t1 (cl (= a 0.0) (< a 0.0)) :rule la_generic :args (1.0 1.0))": false,
        }
        "Negation of disequalities is satisfiable" {
            "(step t1 (cl (< 0.0 0.0)) :rule la_generic :args (1.0))": false,

            "(step t1 (cl (< (+ a b) 1.0) (> (+ a b c) 0.0))
                :rule la_generic :args (1.0 (- 1.0)))": false,
        }
        "Edge case where the strengthening rules need to be stronger" {
            "(step t1 (cl
                (not (<= (- 1) n))
                (not (<= (- 1) (+ n m)))
                (<= (- 2) (* 2 n))
                (not (<= m 1))
            ) :rule la_generic :args (1 1 1 1))": true,
        }
    }
}

#[test]
fn la_disequality() {
    test_cases! {
        definitions = "
            (declare-fun a () Int)
            (declare-fun b () Int)
            (declare-fun x () Real)
            (declare-fun y () Real)
        ",
        "Simple working examples" {
            "(step t1 (cl (or (= a b) (not (<= a b)) (not (<= b a))))
                :rule la_disequality)": true,
            "(step t1 (cl (or (= x y) (not (<= x y)) (not (<= y x))))
                :rule la_disequality)": true,
        }
        "Clause term is not of the correct form" {
            "(step t1 (cl (or (= b a) (not (<= a b)) (not (<= b a))))
                :rule la_disequality)": false,
            "(step t1 (cl (or (= x y) (not (<= y x)) (not (<= y x))))
                :rule la_disequality)": false,
        }
    }
}

#[test]
fn la_totality() {
    test_cases! {
        definitions = "
            (declare-fun a () Int)
            (declare-fun b () Int)
            (declare-fun x () Real)
            (declare-fun y () Real)
        ",
        "Simple working examples" {
            "(step t1 (cl (or (<= a b) (<= b a))) :rule la_totality)": true,
            "(step t1 (cl (or (<= x y) (<= y x))) :rule la_totality)": true,
        }
        "Clause term is not of the correct form" {
            "(step t1 (cl (or (<= a b) (<= a b))) :rule la_totality)": false,
            "(step t1 (cl (<= x y) (<= x y)) :rule la_totality)": false,
            "(step t1 (cl (<= 0 1) (<= 0.0 1.0)) :rule la_totality)": false,
        }
    }
}

#[test]
fn la_tautology() {
    test_cases! {
        definitions = "
            (declare-fun n () Int)
            (declare-fun x () Real)
        ",
        "First form" {
            "(step t1 (cl (<= n (+ 1 n))) :rule la_tautology)": true,
            "(step t1 (cl (< (- n 1) n)) :rule la_tautology)": true,
            "(step t1 (cl (not (<= n (- n 1)))) :rule la_tautology)": true,
            "(step t1 (cl (< 0 (- (+ 1 n) n))) :rule la_tautology)": true,
            "(step t1 (cl (not (<= (+ 1 n) (- (+ 1 n) 1)))) :rule la_tautology)": true,
        }
        "Second form" {
            "(step t1 (cl (or (not (<= x 5.0)) (<= x 6.0))) :rule la_tautology)": true,

            "(step t1 (cl (or (<= x 6.0) (not (<= x 6.0)))) :rule la_tautology)": true,
            "(step t1 (cl (or (<= x 6.1) (not (<= x 6.0)))) :rule la_tautology)": false,

            "(step t1 (cl (or (not (>= x 6.0)) (>= x 5.0))) :rule la_tautology)": true,

            "(step t1 (cl (or (>= x 5.0) (not (>= x 5.0)))) :rule la_tautology)": true,
            "(step t1 (cl (or (>= x 5.0) (not (>= x 5.1)))) :rule la_tautology)": false,

            "(step t1 (cl (or (not (<= x 4.0)) (not (>= x 5.0)))) :rule la_tautology)": true,
            "(step t1 (cl (or (not (<= x 5.0)) (not (>= x 5.0)))) :rule la_tautology)": false,
        }
    }
}

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
