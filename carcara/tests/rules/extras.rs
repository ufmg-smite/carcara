#[test]
fn reordering() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun r () Bool)
            (declare-fun s () Bool)
        ",
        "Simple working examples" {
            "(step t1 (cl p q r s) :rule hole)
            (step t2 (cl r q p s) :rule reordering :premises (t1))": true,

            "(step t1 (cl p q q p r s) :rule hole)
            (step t2 (cl r q p p s q) :rule reordering :premises (t1))": true,

            "(step t1 (cl) :rule hole)
            (step t2 (cl) :rule reordering :premises (t1))": true,
        }
    }
}

#[test]
fn shuffle() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun r () Bool)
            (declare-fun x () Int)
            (declare-fun y () Int)
            (declare-fun z () Int)
        ",
        "Simple working examples" {
            "(step t1 (cl (= (+ x y z) (+ z x y))) :rule shuffle)": true,

            "(step t1 (cl (= (and p q q r p) (and q q p p r))) :rule shuffle)": true,
        }
        "Invalid examples" {
            "(step t1 (cl (= (- x y z) (- x y z))) :rule shuffle)": false,
            "(step t1 (cl (= (or p q r) (and p q r))) :rule shuffle)": false,
            "(step t1 (cl (= (or p q r) true)) :rule shuffle)": false,
            "(step t1 (cl (= (* x x y) (* x y y))) :rule shuffle)": false,
            "(step t1 (cl (= (* x x y) (+ x y))) :rule shuffle)": false,
        }
    }
}

#[test]
fn symm() {
    test_cases! {
        definitions = "
            (declare-sort T 0)
            (declare-fun a () T)
            (declare-fun b () T)
        ",
        "Simple working examples" {
            "(assume h1 (= a b))
            (step t1 (cl (= b a)) :rule symm :premises (h1))": true,
        }
        "Failing examples" {
            "(assume h1 (not (= a b)))
            (step t1 (cl (not (= b a))) :rule symm :premises (h1))": false,
        }
    }
}

#[test]
fn not_symm() {
    test_cases! {
        definitions = "
            (declare-sort T 0)
            (declare-fun a () T)
            (declare-fun b () T)
        ",
        "Simple working examples" {
            "(assume h1 (not (= a b)))
            (step t1 (cl (not (= b a))) :rule not_symm :premises (h1))": true,
        }
        "Failing examples" {
            "(assume h1 (= a b))
            (step t1 (cl (= b a)) :rule not_symm :premises (h1))": false,
        }
    }
}

#[test]
fn eq_symmetric() {
    test_cases! {
        definitions = "
            (declare-sort T 0)
            (declare-fun a () T)
            (declare-fun b () T)
        ",
        "Simple working examples" {
            "(step t1 (cl (= (= b a) (= a b))) :rule eq_symmetric)": true,
            "(step t1 (cl (= (= a a) (= a a))) :rule eq_symmetric)": true,
        }
        "Failing examples" {
            "(step t1 (cl (= (= a b) (= a b))) :rule eq_symmetric)": false,
            "(step t1 (cl (= (not (= a b)) (not (= b a)))) :rule eq_symmetric)": false,
        }
    }
}

#[test]
fn weakening() {
    test_cases! {
        definitions = "
            (declare-fun a () Bool)
            (declare-fun b () Bool)
            (declare-fun c () Bool)
        ",
        "Simple working examples" {
            "(step t1 (cl a b) :rule hole)
            (step t2 (cl a b c) :rule weakening :premises (t1))": true,

            "(step t1 (cl) :rule hole)
            (step t2 (cl a b) :rule weakening :premises (t1))": true,
        }
        "Failing examples" {
            "(step t1 (cl a b) :rule hole)
            (step t2 (cl a c b) :rule weakening :premises (t1))": false,

            "(step t1 (cl a b c) :rule hole)
            (step t2 (cl a b) :rule weakening :premises (t1))": false,
        }
    }
}

#[test]
fn bind_let() {
    test_cases! {
        definitions = "",
        "Simple working examples" {
            "(anchor :step t1 :args ((x Int) (y Int)))
            (step t1.t1 (cl (= x y)) :rule hole)
            (step t1 (cl (= (let ((a 0)) x) (let ((a 0)) y))) :rule bind_let)": true,
        }
        "Premise is of the wrong form" {
            "(anchor :step t1 :args ((x Int) (y Int)))
            (step t1.t1 (cl (< (+ x y) 0)) :rule hole)
            (step t1 (cl (= (let ((a 0)) x) (let ((a 0)) y))) :rule bind_let)": false,
        }
        "Premise doesn't justify inner terms' equality" {
            "(anchor :step t1 :args ((x Int) (y Int)))
            (step t1.t1 (cl (= x y)) :rule hole)
            (step t1 (cl (= (let ((a 0)) a) (let ((a 0)) 0))) :rule bind_let)": false,

            "(anchor :step t1 :args ((x Int) (y Int)))
            (step t1.t1 (cl (= x y)) :rule hole)
            (step t1 (cl (= (let ((a 0)) y) (let ((a 0)) x))) :rule bind_let)": false,
        }
        "Bindings can't be renamed" {
            "(anchor :step t1 :args ((x Int) (y Int)))
            (step t1.t1 (cl (= x y)) :rule hole)
            (step t1 (cl (= (let ((a 0)) x) (let ((b 0)) y))) :rule bind_let)": false,
        }
        "Polyequality in variable values" {
            "(anchor :step t1 :args ((x Int) (y Int)))
            (step t1.t1 (cl (= (= 0 1) (= 1 0))) :rule hole)
            (step t1.t2 (cl (= x y)) :rule hole)
            (step t1 (cl (= (let ((a (= 0 1))) x) (let ((a (= 1 0))) y)))
                :rule bind_let :premises (t1.t1))": true,
        }
    }
}

#[test]
fn la_mult_pos() {
    test_cases! {
        definitions = "
            (declare-fun a () Int)
            (declare-fun b () Int)
            (declare-fun x () Real)
            (declare-fun y () Real)
        ",
        "Simple working examples" {
            "(step t1 (cl (=> (and (> 2 0) (> a b)) (> (* 2 a) (* 2 b))))
                :rule la_mult_pos)": true,
            "(step t1 (cl (=>
                (and (> (/ 10.0 13.0) 0.0) (= x y))
                (= (* (/ 10.0 13.0) x) (* (/ 10.0 13.0) y)))
            ) :rule la_mult_pos)": true,
        }
    }
}

#[test]
fn la_mult_neg() {
    test_cases! {
        definitions = "
            (declare-fun a () Int)
            (declare-fun b () Int)
            (declare-fun x () Real)
            (declare-fun y () Real)
        ",
        "Simple working examples" {
            "(step t1 (cl (=> (and (< (- 2) 0) (>= a b)) (<= (* (- 2) a) (* (- 2) b))))
                :rule la_mult_neg)": true,
            "(step t1 (cl (=>
                (and (< (/ (- 1.0) 13.0) 0.0) (= x y))
                (= (* (/ (- 1.0) 13.0) x) (* (/ (- 1.0) 13.0) y)))
            ) :rule la_mult_neg)": true,
        }
    }
}

#[test]
fn mod_simplify() {
    test_cases! {
        definitions = "",
        "Simple working examples" {
            "(step t1 (cl (= (mod 2 2) 0)) :rule mod_simplify)": true,
            "(step t1 (cl (= (mod 42 8) 2)) :rule mod_simplify)": true,
        }
        "Negative numbers" {
            "(step t1 (cl (= (mod (- 8) 3) 1)) :rule mod_simplify)": true,
            "(step t1 (cl (= (mod 8 (- 3)) 2)) :rule mod_simplify)": true,
            "(step t1 (cl (= (mod (- 8) (- 3)) 1)) :rule mod_simplify)": true,

            "(step t1 (cl (= (mod (- 8) 3) (- 2))) :rule mod_simplify)": false,
            "(step t1 (cl (= (mod 8 (- 3)) (- 1))) :rule mod_simplify)": false,
            "(step t1 (cl (= (mod (- 8) (- 3)) (- 2))) :rule mod_simplify)": false,
        }
        "Modulo by zero" {
            "(step t1 (cl (= (mod 3 0) 1)) :rule mod_simplify)": false,
        }
    }
}

#[test]
fn evaluate() {
    test_cases! {
        definitions = "
            (declare-const x Int)
            (declare-fun f (Int Int) Int)
        ",
        "Booleans" {
            "(step t1 (cl (=
                (=> (and true true) (or true false) (ite false false true))
                true
            )) :rule evaluate)": true,

            "(step t1 (cl (= (or (= 0 0 1) (distinct 1 2 3 1)) false)) :rule evaluate)": true,
        }
        "Arithmetic" {
            "(step t1 (cl (= (+ 1 2 (* 3 (- 1))) 0)) :rule evaluate)": true,
            "(step t1 (cl (= (+ (div 3 (abs 2)) (mod (- 7) (- 3))) 0)) :rule evaluate)": true,
            "(step t1 (cl (= (/ 1.0 (to_real 7)) 1/7)) :rule evaluate)": true,
        }
        "Bitvectors" {
            "(step t1 (cl (=
                (bvnot (bvudiv #b100 (@bbterm false true false)))
                #b101
            )) :rule evaluate)": true,

            "(step t1 (cl (=
                (bvashr ((_ rotate_left 3) #b0101100) #b0000001)
                #b1110001
            )) :rule evaluate)": true,
        }
        "Partial evaluation" {
            "(step t1 (cl (= (+ x (+ 1 1)) (+ x 2))) :rule evaluate)": true,
            "(step t1 (cl (= (f x (+ 1 1)) (f x 2))) :rule evaluate)": false,
        }
        "Invalid examples" {
            "(step t1 (cl (= 2 (+ 1 1))) :rule evaluate)": false,
            "(step t1 (cl (= (forall ((x Int)) true) true)) :rule evaluate)": false,
        }
    }
}
