#[test]
fn eq_reflexive() {
    test_cases! {
        definitions = "
            (declare-fun a () Int)
            (declare-fun b () Int)
            (declare-fun f (Int Int) Int)
        ",
        "Simple working examples" {
            "(step t1 (cl (= a a)) :rule eq_reflexive)": true,
            "(step t1 (cl (= false false)) :rule eq_reflexive)": true,
            "(step t1 (cl (= (f a b) (f a b))) :rule eq_reflexive)": true,
            "(step t1 (cl (= (+ b a) (+ b a))) :rule eq_reflexive)": true,
        }
        "Number of terms in clause != 1" {
            "(step t1 (cl) :rule eq_reflexive)": false,
            "(step t1 (cl (= a a) (= b b)) :rule eq_reflexive)": false,
        }
        "Term is not an equality" {
            "(step t1 (cl (not (= b b))) :rule eq_reflexive)": false,
            "(step t1 (cl (and (= a a) (= b b))) :rule eq_reflexive)": false,
        }
        "Terms in equality aren't equal" {
            "(step t1 (cl (= a b)) :rule eq_reflexive)": false,
            "(step t1 (cl (= (f a b) (f b a))) :rule eq_reflexive)": false,
            "(step t1 (cl (= (+ a b) (+ b a))) :rule eq_reflexive)": false,
        }
    }
}

#[test]
fn refl() {
    test_cases! {
        definitions = "
            (declare-fun f (Real) Real)
            (declare-fun g (Real) Real)
            (declare-fun z () Real)
        ",
        "Simple working examples" {
            "(anchor :step t1 :args ((y Real) (:= (x Real) y)))
            (step t1.t1 (cl (= x y)) :rule refl)
            (step t1 (cl) :rule hole)": true,

            "(anchor :step t1)
            (step t1.t1 (cl (= z z)) :rule refl)
            (step t1 (cl) :rule hole)": true,

        }
        "Multiple substitutions in sequence" {
            "(anchor :step t1 :args ((z Real) (:= (y Real) z) (:= (x Real) y)))
            (step t1.t1 (cl (= x z)) :rule refl)
            (step t1 (cl) :rule hole)": true,
        }
        "Nested subproofs" {
            // Since an inner subproof cannot end an outer subproof, we need to have a dummy
            // step to the end the outer subproofs in these examples

            // This step is valid because the outer context transforms the `y` in the `(:= x y)`
            // mapping, such that the context becomes `(:= x z)`
            "(anchor :step t1 :args ((z Real) (:= (y Real) z)))
            (anchor :step t1.t1 :args ((:= (x Real) y)))
            (step t1.t1.t1 (cl (= x z)) :rule refl)
            (step t1.t1 (cl) :rule hole)
            (step t1 (cl) :rule hole)": true,

            // This should fail because the semantics of `refl` are such that the substitution
            // is simultaneous, and not until a fixed point
            "(anchor :step t1 :args ((y Real) (:= (x Real) y)))
            (anchor :step t1.t1 :args ((z Real) (:= (y Real) z)))
            (step t1.t1.t1 (cl (= x z)) :rule refl)
            (step t1.t1 (cl) :rule hole)
            (step t1 (cl) :rule hole)": false,
        }
        "Terms aren't equal after applying context substitution" {
            "(anchor :step t1 :args ((y Real) (:= (x Real) y)))
            (step t1.t1 (cl (= x z)) :rule refl)
            (step t1 (cl) :rule hole)": false,
        }
        "Name collision with variables of different types" {
            "(anchor :step t1 :args ((y Int) (:= (x Int) y)))
            (step t1.t1 (cl (=
                (forall ((y Bool)) (and y (> x 0)))
                (forall ((z Bool)) (and z (> y 0)))
            )) :rule refl)
            (step t1 (cl) :rule hole)": true,
        }
    }
}
