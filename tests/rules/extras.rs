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
fn eq_mp() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun r () Bool)
            (declare-fun a () Int)
            (declare-fun b () Int)
        ",
        "Simple working examples" {
            "(assume h1 p)
            (assume h2 (= p q))
            (step t3 (cl q) :rule eq_mp :premises (h1 h2))": true,

            "(assume h1 (not p))
            (assume h2 (= (not p) (or q r)))
            (step t3 (cl (or q r)) :rule eq_mp :premises (h1 h2))": true,

            "(assume h1 (< a b))
            (assume h2 (= (< a b) (not (>= a b))))
            (step t3 (cl (not (>= a b))) :rule eq_mp :premises (h1 h2))": true,

            "(assume h1 p)
            (assume h2 (= p p))
            (step t3 (cl p) :rule eq_mp :premises (h1 h2))": true,
        }
        "Premises in the wrong order" {
            "(assume h1 p)
            (assume h2 (= p q))
            (step t3 (cl q) :rule eq_mp :premises (h2 h1))": false,
        }
        "Equivalence is flipped" {
            "(assume h1 p)
            (assume h2 (= q p))
            (step t3 (cl q) :rule eq_mp :premises (h1 h2))": false,
        }
        "Failing examples" {
            "(assume h1 p)
            (assume h2 (= p q))
            (step t3 (cl r) :rule eq_mp :premises (h1 h2))": false,

            "(assume h1 p)
            (assume h2 (= p q))
            (step t3 (cl q r) :rule eq_mp :premises (h1 h2))": false,

            "(assume h1 p)
            (assume h2 (=> p q))
            (step t3 (cl q) :rule eq_mp :premises (h1 h2))": false,

            "(assume h1 (= p q))
            (step t3 (cl q) :rule eq_mp :premises (h1))": false,

            "(step t1 (cl p r) :rule hole)
            (assume h2 (= p q))
            (step t3 (cl q) :rule eq_mp :premises (t1 h2))": false,
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
fn and_intro() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun r () Bool)
        ",
        "Simple working examples" {
            "(assume h1 p)
            (assume h2 q)
            (step t1 (cl (and p q)) :rule and_intro :premises (h1 h2))": true,

            "(assume h1 p)
            (assume h2 q)
            (assume h3 r)
            (step t1 (cl (and p q r)) :rule and_intro :premises (h1 h2 h3))": true,
        }
        "Non-unit premise corresponds to a disjunction" {
            "(step t1 (cl p q) :rule hole)
            (assume h2 r)
            (step t2 (cl (and (or p q) r)) :rule and_intro :premises (t1 h2))": true,

            // A unit premise whose term is itself an `or` matches the same conjunct.
            "(assume h1 (or p q))
            (assume h2 r)
            (step t1 (cl (and (or p q) r)) :rule and_intro :premises (h1 h2))": true,
        }
        "Premises must be in the right order" {
            "(assume h1 p)
            (assume h2 q)
            (step t1 (cl (and q p)) :rule and_intro :premises (h1 h2))": false,
        }
        "A conjunct does not match its premise" {
            "(assume h1 p)
            (assume h2 q)
            (step t1 (cl (and p r)) :rule and_intro :premises (h1 h2))": false,

            // The disjuncts of the conjunct must match the clause order.
            "(step t1 (cl p q) :rule hole)
            (assume h2 r)
            (step t2 (cl (and (or q p) r)) :rule and_intro :premises (t1 h2))": false,

            // A non-unit premise must correspond to an `or`, not a single literal.
            "(step t1 (cl p q) :rule hole)
            (assume h2 r)
            (step t2 (cl (and p r)) :rule and_intro :premises (t1 h2))": false,
        }
        "Wrong number of premises" {
            "(assume h1 p)
            (step t1 (cl (and p q)) :rule and_intro :premises (h1))": false,

            "(assume h1 p)
            (assume h2 q)
            (assume h3 r)
            (step t1 (cl (and p q)) :rule and_intro :premises (h1 h2 h3))": false,
        }
        "Conclusion is not a conjunction" {
            "(assume h1 p)
            (step t1 (cl p) :rule and_intro :premises (h1))": false,
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
fn la_mult_sign() {
    test_cases! {
        definitions = "
            (declare-fun a () Real)
            (declare-fun b () Real)
            (declare-fun c () Real)
            (declare-fun d () Real)
        ",
        "Simple working examples" {
            "(step t1 (cl (=> (> a 0.0) (> a 0.0))) :rule la_mult_sign)": true,

            "(step t1 (cl (=>
                (and (> a 0.0) (< b 0.0) (> c 0.0))
                (< (* a b c) 0.0))
            ) :rule la_mult_sign)": true,
        }
        "Even powers" {
            "(step t1 (cl (=> (not (= a 0.0)) (> (* a a) 0.0))) :rule la_mult_sign)": true,
        }
        "Not using some variables" {
            "(step t1 (cl (=>
                (and (> a 0.0) (< b 0.0) (> c 0.0) (> d 0.0))
                (< (* a b b b) 0.0))
            ) :rule la_mult_sign)": true,
        }
        "Wrong relation" {
            "(step t1 (cl (=>
                (and (> a 0.0) (< b 0.0) (> c 0.0))
                (> (* a b c) 0.0))
            ) :rule la_mult_sign)": false,
        }
        "Could not calculate sign" {
            // this is technically sound, but still an error
            "(step t1 (cl (=>
                (and (> a 0.0) (not (= b 0.0)) (> c 0.0))
                (not (= (* a b c) 0.0)))
            ) :rule la_mult_sign)": false,
        }
        "Missing comparison for a monomial variable" {
            // Regression test: this used to hit a `todo!()` and panic instead of returning a
            // checker error
            "(step t1 (cl (=> (> a 0.0) (> (* a b) 0.0))) :rule la_mult_sign)": false,
            "(step t1 (cl (=> (> a 0.0) (> (* a b b) 0.0))) :rule la_mult_sign)": false,
        }
    }
}

#[test]
fn la_mult_abs_comparison() {
    test_cases! {
        definitions = "
            (declare-fun a () Int)
            (declare-fun b () Int)
            (declare-fun c () Int)
            (declare-fun d () Int)
        ",
        "Simple working examples" {
            "(step t1 (cl (= (abs a) (abs b))) :rule hole)
            (step t2 (cl (= (abs c) (abs d))) :rule hole)
            (step t3 (cl (= (abs (* a c)) (abs (* b d))))
                :rule la_mult_abs_comparison :premises (t1 t2))": true,

            "(step t1 (cl (> (abs a) (abs 1))) :rule hole)
            (step t2 (cl (> (abs b) (abs 1))) :rule hole)
            (step t3 (cl (and (= (abs c) (abs 1)) (not (= c 0)))) :rule hole)
            (step t4 (cl (and (= (abs d) (abs 1)) (not (= d 0)))) :rule hole)
            (step t5 (cl (> (abs (* a b c d)) (abs (* 1 1 1 1))))
                :rule la_mult_abs_comparison :premises (t1 t2 t3 t4))": true,
        }
        "Premise has the wrong form" {
            "(step t1 (cl (> (abs a) (abs b))) :rule hole)
            (step t2 (cl (= (abs c) (abs d))) :rule hole)
            (step t3 (cl (= (abs (* a c)) (abs (* b d))))
                :rule la_mult_abs_comparison :premises (t1 t2))": false,

            "(step t1 (cl (and (= (abs a) (abs 1)) (not (= a 0)))) :rule hole)
            (step t2 (cl (> (abs b) (abs 1))) :rule hole)
            (step t3 (cl (> (abs (* a b)) (abs (* 1 1))))
                :rule la_mult_abs_comparison :premises (t1 t2))": false,
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

            // Regression
            "(step t1 (cl (= ((_ extract 0 0) (_ bv1 1)) #b1)) :rule evaluate)": true,
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

#[test]
fn beta_equiv() {
    test_cases! {
        definitions = "",
        "Simple working examples" {
            "(step t1 (cl (= ((lambda ((a Int) (b Int) (c Int)) (+ a b c)) 1 2 3) (+ 1 2 3)))
                :rule beta_equiv)": true,

            "(step t1 (cl (=
                ((lambda ((a Int) (b Int) (c Int)) (+ a b c)) 1)
                (lambda ((b Int) (c Int)) (+ 1 b c))
            )) :rule beta_equiv)": true,
        }
        "Not an application" {
            "(step t1 (cl (=
                (lambda ((a Int) (b Int) (c Int)) (+ a b c))
                (lambda ((a Int) (b Int) (c Int)) (+ a b c))
            )) :rule beta_equiv)": false,
        }
        "Wrong arg names" {
            "(step t1 (cl (=
                ((lambda ((a Int) (b Int) (c Int)) (+ a b c)) 1)
                (lambda ((c Int) (b Int)) (+ 1 c b))
            )) :rule beta_equiv)": false,
        }
        "Wrong body" {
            "(step t1 (cl (=
                ((lambda ((a Int) (b Int) (c Int)) (+ a b c)) 1)
                (lambda ((b Int) (c Int)) (+ 1 c b))
            )) :rule beta_equiv)": false,
        }
    }
}

#[test]
fn div_intro() {
    test_cases! {
        definitions = "
            (declare-const a Int)
        ",
        "Simple working examples" {
            "(step t1 (cl (and (<= (* 5 (div a 5)) a) (< a (* 5 (+ (div a 5) 1)))))
                :rule div_intro)": true,

            "(step t1 (cl (and
                (<= (* (- 5) (div a (- 5))) a)
                (< a (* (- 5) (+ (div a (- 5)) (- 1))))
            )) :rule div_intro)": true,
        }
        "Division by 0!" {
            "(step t1 (cl (and (<= (* 0 (div a 0)) a) (< a (* 0 (+ (div a 0) 1)))))
                :rule div_intro)": false,
        }
        "Different values of b" {
            "(step t1 (cl (and (<= (* 5 (div a 3)) a) (< a (* 5 (+ (div a 5) 1)))))
                :rule div_intro)": false,
        }
        "Wrong coefficient" {
            "(step t1 (cl (and (<= (* 5 (div a 5)) a) (< a (* 5 (+ (div a 5) 2)))))
                :rule div_intro)": false,

            "(step t1 (cl (and (<= (* 5 (div a 5)) a) (< a (* 5 (+ (div a 5) (- 1))))))
                :rule div_intro)": false,

            "(step t1 (cl (and
                (<= (* (- 5) (div a (- 5))) a)
                (< a (* (- 5) (+ (div a (- 5)) 1)))
            )) :rule div_intro)": false,
        }
    }
}

#[test]
fn log2_intro() {
    test_cases! {
        definitions = "
            (declare-const x Int)
            (declare-const y Int)
        ",
        "Simple working examples" {
            "(step t1 (cl (and
                (=> (< 0 x)
                    (and (<= (int.pow2 (int.log2 x)) x) (< x (int.pow2 (+ (int.log2 x) 1)))))
                (=> (not (< 0 x)) (= (int.log2 x) 0))
            )) :rule log2_intro)": true,
        }
        "Different values of x" {
            "(step t1 (cl (and
                (=> (< 0 x)
                    (and (<= (int.pow2 (int.log2 x)) y) (< x (int.pow2 (+ (int.log2 x) 1)))))
                (=> (not (< 0 x)) (= (int.log2 x) 0))
            )) :rule log2_intro)": false,
        }
    }
}

#[test]
fn to_int_intro() {
    test_cases! {
        definitions = "
            (declare-const x Real)
            (declare-const y Real)
        ",
        "Simple working examples" {
            "(step t1 (cl
                (and (<= 0 (- x (to_real (to_int x)))) (< (- x (to_real (to_int x))) 1))
            ) :rule to_int_intro)": true,
        }
        "Different values of x" {
            "(step t1 (cl
                (and (<= 0 (- x (to_real (to_int x)))) (< (- y (to_real (to_int x))) 1))
            ) :rule to_int_intro)": false,
        }
    }
}
