#[test]
fn subproof() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun r () Bool)
            (declare-fun s () Bool)
        ",
        "Simple working examples" {
            "(anchor :step t1)
            (assume t1.h1 p)
            (step t1.t2 (cl q) :rule hole)
            (step t1 (cl (not p) q) :rule subproof :discharge (t1.h1))": true,

            "(anchor :step t1)
            (assume t1.h1 p)
            (step t1.t2 (cl) :rule hole)
            (assume t1.h3 q)
            (step t1.t4 (cl (= r s)) :rule hole)
            (step t1 (cl (not p) (not q) (= r s))
                :rule subproof :discharge (t1.h1 t1.h3))": true,
        }
        "Missing assumption" {
            "(anchor :step t1)
            (assume t1.h1 p)
            (step t1.t2 (cl (= r s)) :rule hole)
            (step t1 (cl (not p) (not q) (= r s)) :rule subproof :discharge (t1.h1))": false,
        }
        "Assumption terms don't match" {
            "(anchor :step t1)
            (assume t1.h1 p)
            (assume t1.h2 q)
            (step t1.t3 (cl (= r s)) :rule hole)
            (step t1 (cl (not q) (not p) (= r s))
                :rule subproof :discharge (t1.h1 t1.h2))": false,

            "(anchor :step t1)
            (assume t1.h1 (or p q))
            (assume t1.h2 (= p q))
            (step t1.t3 (cl (= r s)) :rule hole)
            (step t1 (cl (not (and p q)) (not (= q p)) (= r s))
                :rule subproof :discharge (t1.h1 t1.h2))": false,
        }
        "Conclusion terms don't match" {
            "(anchor :step t1)
            (assume t1.h1 p)
            (assume t1.h2 q)
            (step t1.t3 (cl (= r s)) :rule hole)
            (step t1 (cl (not p) (not q) (not (= r s)))
                :rule subproof :discharge (t1.h1 t1.h2))": false,
        }
    }
}

#[test]
fn bind() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun r () Bool)
            (declare-fun s () Bool)
            (declare-fun y () Real)
        ",
        "Simple working examples" {
            "(anchor :step t1 :args ((y Real) (:= (x Real) y)))
            (step t1.t1 (cl (= p q)) :rule hole)
            (step t1 (cl (= (forall ((x Real)) p) (forall ((y Real)) q))) :rule bind)": true,

            "(anchor :step t1 :args ((y1 Real) (y2 Real) (:= (x1 Real) y1) (:= (x2 Real) y2)))
            (step t1.t1 (cl (= (= x1 x2) (= y1 y2))) :rule hole)
            (step t1 (cl (= (forall ((x1 Real) (x2 Real)) (= x1 x2))
                (forall ((y1 Real) (y2 Real)) (= y1 y2)))) :rule bind)": true,
        }
        "Examples with binding arguments" {
            "(anchor :step t1 :args ((y Real) (z Real) (:= (x Real) y)))
            (step t1.t1 (cl (= p q)) :rule hole)
            (step t1 (cl (= (forall ((x Real) (z Real)) p)
                (forall ((y Real) (z Real)) q))) :rule bind)": true,
        }
        "Out-of-place variable argument in anchor" {
            "(anchor :step t1 :args ((y1 Real) (:= (x1 Real) y1) (y2 Real) (:= (x2 Real) y2)))
            (step t1.t1 (cl (= (= x1 x2) (= y1 y2))) :rule hole)
            (step t1 (cl (= (forall ((x1 Real) (x2 Real)) (= x1 x2))
                (forall ((y1 Real) (y2 Real)) (= y1 y2)))) :rule bind)": false,
        }
        "Binding `lambda` and `choice` terms" {
            "(anchor :step t1 :args ((y Real) (:= (x Real) y)))
            (step t1.t1 (cl (= x y)) :rule hole)
            (step t1 (cl (= (lambda ((x Real)) x) (lambda ((y Real)) y))) :rule bind)": true,

            "(anchor :step t1 :args ((y Int) (:= (x Int) y)))
            (step t1.t1 (cl (= p q)) :rule hole)
            (step t1 (cl (= (choice ((x Int)) p) (choice ((y Int)) q))) :rule bind)": true,
        }
        "y_i appears in phi as a free variable" {
            "(anchor :step t1 :args ((y Real) (:= (x Real) y)))
            (step t1.t1 (cl (= (= y x) (= y y))) :rule hole)
            (step t1 (cl (= (forall ((x Real)) (= y x))
                (forall ((y Real)) (= y y)))) :rule bind)": false,

            "(anchor :step t1 :args ((y Real) (z Real) (:= (x Real) y)))
            (step t1.t1 (cl (= (= y x) (= y y))) :rule hole)
            (step t1 (cl (= (forall ((z Real) (x Real)) (= y z))
                (forall ((z Real) (y Real)) (= y z)))) :rule bind)": false,
        }
        "Terms in conclusion clause don't match terms in previous command" {
            "(anchor :step t1 :args ((y Real) (:= (x Real) y)))
            (step t1.t1 (cl (= p q)) :rule hole)
            (step t1.t2 (cl (= r s)) :rule hole) ; This step shouldn't be here!
            (step t1 (cl (= (forall ((x Real)) p) (forall ((y Real)) q))) :rule bind)": false,

            "(anchor :step t1 :args ((y Real) (:= (x Real) y)))
            (step t1.t1 (cl (= p q)) :rule hole)
            (step t1 (cl (= (forall ((x Real)) q) (forall ((y Real)) p))) :rule bind)": false,
        }
        "Context substitutions don't match quantifier bindings" {
            "(anchor :step t1 :args ((y Real) (:= (x Real) y)))
            (step t1.t1 (cl (= p q)) :rule hole)
            (step t1 (cl (= (forall ((y Real)) p) (forall ((x Real)) q))) :rule bind)": false,

            "(anchor :step t1 :args ((y1 Real) (y2 Real) (:= (x1 Real) y1) (:= (x2 Real) y2)))
            (step t1.t1 (cl (= (= x1 x2) (= y1 y2))) :rule hole)
            (step t1 (cl (= (forall ((x2 Real)) (= x1 x2))
                (forall ((y1 Real) (y2 Real)) (= y1 y2)))) :rule bind)": false,
        }
    }
}

#[test]
fn r#let() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun i () Int)
            (declare-fun j () Int)
            (declare-fun k () Int)
            (declare-fun x () Int)
            (declare-fun y () Int)
            (declare-fun z () Int)
        ",
        "Simple working examples" {
            "(step t1 (cl (= i x)) :rule hole)
            (anchor :step t2 :args ((x Int) (:= (a Int) x)))
            (step t2.t1 (cl (= p q)) :rule hole)
            (step t2 (cl (= (let ((a i)) p) q)) :rule let :premises (t1))": true,

            "(step t1 (cl (= i x)) :rule hole)
            (step t2 (cl (= k z)) :rule hole)
            (anchor :step t3 :args ((x Int) (y Int) (z Int) (:= (a Int) x) (:= (b Int) y) (:= (c Int) z)))
            (step t3.t1 (cl (= p q)) :rule hole)
            (step t3 (cl (= (let ((a i) (b y) (c k)) p) q)) :rule let :premises (t1 t2))": true,
        }
        "Premise equalities may be flipped" {
            "(step t1 (cl (= x i)) :rule hole)
            (anchor :step t2 :args ((x Int) (:= (a Int) x)))
            (step t2.t1 (cl (= p q)) :rule hole)
            (step t2 (cl (= (let ((a i)) p) q)) :rule let :premises (t1))": true,
        }
        "Wrong number of premises" {
            "(step t1 (cl (= i x)) :rule hole)
            (anchor :step t2 :args ((x Int) (y Int) (z Int) (:= (a Int) x) (:= (b Int) y) (:= (c Int) z)))
            (step t2.t1 (cl (= p q)) :rule hole)
            (step t2 (cl (= (let ((a i) (b y) (c k)) p) q)) :rule let :premises (t1))": false,

            "(step t1 (cl (= i x)) :rule hole)
            (step t2 (cl (= y y)) :rule hole)
            (step t3 (cl (= k z)) :rule hole)
            (anchor :step t4 :args ((x Int) (y Int) (z Int) (:= (a Int) x) (:= (b Int) y) (:= (c Int) z)))
            (step t4.t1 (cl (= p q)) :rule hole)
            (step t4 (cl (= (let ((a i) (b y) (c k)) p) q)) :rule let :premises (t1 t2))": false,
        }
        "Number of bindings is `let` term doesn't match number of substitutions in context" {
            "(step t1 (cl (= i x)) :rule hole)
            (step t2 (cl (= j y)) :rule hole)
            (anchor :step t3 :args ((x Int) (y Int) (z Int) (:= (a Int) x) (:= (b Int) y) (:= (c Int) z)))
            (step t3.t1 (cl (= p q)) :rule hole)
            (step t3 (cl (= (let ((a i) (b j)) p) q)) :rule let :premises (t1 t2))": false,
        }
        "u and u' don't match equality in previous command" {
            "(step t1 (cl (= i x)) :rule hole)
            (anchor :step t2 :args ((x Int) (:= (a Int) x)))
            (step t2.t1 (cl (= p (= i j))) :rule hole)
            (step t2 (cl (= (let ((a i)) p) q)) :rule let :premises (t1))": false,
        }
    }
}

#[test]
fn onepoint() {
    test_cases! {
        definitions = "
            (declare-const p Bool)
            (declare-const t Int)
            (declare-const u Int)
            (declare-const v Int)
        ",
        "Simple working examples" {
            "(anchor :step t1 :args ((:= (x Int) t)))
            (step t1.t1 (cl (= (=> (= x t) p) (=> (= t t) p))) :rule hole)
            (step t1 (cl (= (forall ((x Int)) (=> (= x t) p)) (=> (= t t) p)))
                :rule onepoint)": true,

            "(anchor :step t1 :args ((:= (x Int) t)))
            (step t1.t1 (cl (= (or (not (= x t)) p) (or (not (= t t)) p))) :rule hole)
            (step t1 (cl (= (forall ((x Int)) (or (not (= x t)) p)) (or (not (= t t)) p)))
                :rule onepoint)": true,

            "(anchor :step t1 :args ((:= (x Int) t)))
            (step t1.t1 (cl (= (and (= x t) p) (and (= t t) p))) :rule hole)
            (step t1 (cl (= (exists ((x Int)) (and (= x t) p)) (and (= t t) p)))
                :rule onepoint)": true,
        }
        "Multiple quantifier bindings" {
            "(anchor :step t1 :args ((x Int) (y Int) (:= (z Int) t)))
            (step t1.t1 (cl (= (=> (= z t) (= (+ x y) (+ z t)))
                               (=> (= t t) (= (+ x y) (+ t t))))) :rule hole)
            (step t1 (cl (=
                (forall ((x Int) (y Int) (z Int)) (=> (= z t) (= (+ x y) (+ z t))))
                (forall ((x Int) (y Int))         (=> (= t t) (= (+ x y) (+ t t))))
            )) :rule onepoint)": true,

            "(anchor :step t1 :args ((x Int) (y Int) (:= (z Int) t)))
            (step t1.t1 (cl (= (and (= z t) (= (+ x y) (+ z t)))
                               (and (= t t) (= (+ x y) (+ t t))))) :rule hole)
            (step t1 (cl (=
                (exists ((x Int) (y Int) (z Int)) (and (= z t) (= (+ x y) (+ z t))))
                (exists ((x Int) (y Int))         (and (= t t) (= (+ x y) (+ t t))))
            )) :rule onepoint)": true,
        }
        "Multiple quantifier bindings eliminated" {
            "(anchor :step t1 :args ((:= (x Int) t) (:= (y Int) u) (:= (z Int) v)))
            (step t1.t1 (cl (= (=> (= x t) (=> (= y u) (=> (= z v) p)))
                               (=> (= t t) (=> (= u u) (=> (= v v) p))))) :rule hole)
            (step t1 (cl (=
                (forall ((x Int) (y Int) (z Int)) (=> (= x t) (=> (= y u) (=> (= z v) p))))
                (=> (= t t) (=> (= u u) (=> (= v v) p)))
            )) :rule onepoint)": true,

            "(anchor :step t1 :args ((:= (x Int) t) (:= (y Int) u) (:= (z Int) v)))
            (step t1.t1 (cl (= (or (not (= x t)) (or (not (= y u)) (or (not (= z v)) p)))
                               (or (not (= t t)) (or (not (= u u)) (or (not (= v v)) p)))
            )) :rule hole)
            (step t1 (cl (=
                (forall ((x Int) (y Int) (z Int))
                    (or (not (= x t)) (or (not (= y u)) (or (not (= z v)) p))))
                (or (not (= t t)) (or (not (= u u)) (or (not (= v v)) p)))
            )) :rule onepoint)": true,

            "(anchor :step t1 :args ((:= (x Int) t) (:= (y Int) u) (:= (z Int) v)))
            (step t1.t1 (cl (= (=> (and (= x t) (and (= y u) (= z v))) p)
                               (=> (and (= t t) (and (= u u) (= v v))) p))) :rule hole)
            (step t1 (cl (=
                (forall ((x Int) (y Int) (z Int)) (=> (and (= x t) (and (= y u) (= z v))) p))
                (=> (and (= t t) (and (= u u) (= v v))) p)
            )) :rule onepoint)": true,

            "(anchor :step t1 :args ((:= (x Int) t) (:= (y Int) u) (:= (z Int) v)))
            (step t1.t1 (cl (= (and (= x t) (and (= y u) (and (= z v) p)))
                               (and (= t t) (and (= u u) (and (= v v) p))))) :rule hole)
            (step t1 (cl (=
                (exists ((x Int) (y Int) (z Int)) (and (= x t) (and (= y u) (and (= z v) p))))
                (and (= t t) (and (= u u) (and (= v v) p)))
            )) :rule onepoint)": true,
        }
        "Multiple occurrences with different polarity" {
            // This test reproduces a bug that existed where the cache didn't take into account
            // the polarity of a seen term.
            "(anchor :step t3 :args ((:= (?x Int) 0)))
            (step t3.t8 (cl (=
                (=> (not (= 0 ?x)) (=> (= 2 2) (=> (= 0 ?x) (= 1 2))))
                (=> (not (= 0 0)) (=> (= 2 2) (=> (= 0 0) (= 1 2))))
            )) :rule hole)
            (step t3 (cl (=
                (forall ((?x Int)) (=> (not (= 0 ?x)) (=> (= 2 2) (=> (= 0 ?x) (= 1 2)))))
                (=> (not (= 0 0)) (=> (= 2 2) (=> (= 0 0) (= 1 2))))
            )) :rule onepoint)": true,
        }
    }
}

#[test]
fn sko_ex() {
    test_cases! {
        definitions = "
            (declare-fun p (Int) Bool)
            (declare-fun q (Int) Bool)
        ",
        "Simple working examples" {
            "(anchor :step t1 :args ((:= (x Int) (choice ((x Int)) (p x)))))
            (step t1.t1 (cl (= (p x) (p (choice ((x Int)) (p x))))) :rule hole)
            (step t1 (cl (= (exists ((x Int)) (p x)) (p (choice ((x Int)) (p x)))))
                :rule sko_ex)": true,

            "(anchor :step t1 :args (
                (:= (x Int) (choice ((x Int)) (exists ((y Int)) (= x y))))
                (:= (y Int) (choice ((y Int)) (= (choice ((x Int)) (exists ((y Int)) (= x y))) y)))
            ))
            (step t1.t1 (cl (=
                (= x y)
                (= (choice ((x Int)) (exists ((y Int)) (= x y)))
                   (choice ((y Int)) (= (choice ((x Int)) (exists ((y Int)) (= x y))) y)))
            )) :rule hole)
            (step t1 (cl (=
                (exists ((x Int) (y Int)) (= x y))
                (= (choice ((x Int)) (exists ((y Int)) (= x y)))
                   (choice ((y Int)) (= (choice ((x Int)) (exists ((y Int)) (= x y))) y)))
            )) :rule sko_ex)": true,
        }
    }
}

#[test]
fn sko_forall() {
    test_cases! {
        definitions = "
            (declare-fun p (Int) Bool)
            (declare-fun q (Int) Bool)
        ",
        "Simple working examples" {
            "(anchor :step t1 :args ((:= (x Int) (choice ((x Int)) (not (p x))))))
            (step t1.t1 (cl (= (p x) (p (choice ((x Int)) (not (p x)))))) :rule hole)
            (step t1 (cl (= (forall ((x Int)) (p x)) (p (choice ((x Int)) (not (p x))))))
                :rule sko_forall)": true,

            "(anchor :step t1 :args (
                (:= (x Int) (choice ((x Int)) (not (forall ((y Int)) (= x y)))))
                (:= (y Int)
                    (choice ((y Int))
                        (not (= (choice ((x Int)) (not (forall ((y Int)) (= x y)))) y))))
            ))
            (step t1.t1 (cl (=
                (= x y)
                (= (choice ((x Int)) (not (forall ((y Int)) (= x y))))
                    (choice ((y Int))
                        (not (= (choice ((x Int)) (not (forall ((y Int)) (= x y)))) y))))
            )) :rule hole)
            (step t1 (cl (=
                (forall ((x Int) (y Int)) (= x y))
                (= (choice ((x Int)) (not (forall ((y Int)) (= x y))))
                    (choice ((y Int))
                        (not (= (choice ((x Int)) (not (forall ((y Int)) (= x y)))) y))))
            )) :rule sko_forall)": true,
        }
    }
}
