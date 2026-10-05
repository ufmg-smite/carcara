#[test]
fn refl() {
    test_cases! {
        pipeline = Polyeq,
        problem =  "
            (declare-const a Bool)
            (declare-const b Bool)
            (declare-const y Real)
            (declare-fun f (Bool) Bool)
        ",
        "Unchanged" {
            "(step t1 (cl (= a a)) :rule refl)"
            ->
            "(step t1 (cl (= a a)) :rule refl)",
        }
        "Flipped equality" {
            "(step t1 (cl (= (= a b) (= b a))) :rule refl)"
            ->
            "(step t1.t1 (cl (= (= a b) (= b a))) :rule eq_symmetric)",
        }
        "Function application" {
            "(step t1 (cl (= (f (= a b)) (f (= b a)))) :rule refl)"
            ->
            "(step t1.t1 (cl (= (= a b) (= b a))) :rule eq_symmetric)
            (step t1.t2 (cl (= (f (= a b)) (f (= b a)))) :rule cong :premises (t1.t1))",
        }
        "With context" {
            "(anchor :step t1 :args ((:= (x Real) y)))
            (step t1.t1 (cl (= y x)) :rule refl)
            (step t1 (cl) :rule hole)"
            ->
            "(anchor :step t1 :args ((:= (x Real) y)))
            (step t1.t1.t1 (cl (= x y)) :rule refl)
            (step t1.t1 (cl (= y x)) :rule symm :premises (t1.t1.t1))
            (step t1 (cl) :rule hole)",
        }
    }
}

#[test]
fn assume() {
    test_cases! {
        pipeline = Polyeq,
        problem =  "
            (declare-const p Bool)
            (declare-const q Bool)
            (declare-const r Bool)
            (assert (= p q))
        ",
        "Assume is polyequal to a premise" {
            "(assume h1 (= q p))
            (step t2 (cl (not (= q p)) r) :rule hole)
            (step t3 (cl r) :rule resolution :premises (h1 t2))"
            ->
            "(assume h1 (= p q))
            (step h1.t1 (cl (= (= p q) (= q p))) :rule eq_symmetric)
            (step h1.t2 (cl (not (= p q)) (= q p)) :rule equiv1 :premises (h1.t1))
            (step h1.t3 (cl (= q p)) :rule resolution :premises (h1 h1.t2) :args ((= p q) true))
            (step t2 (cl (not (= q p)) r) :rule hole)
            (step t3 (cl r) :rule resolution :premises (h1.t3 t2))",
        }
    }
}

#[test]
fn forall_inst() {
    test_cases! {
        pipeline = Polyeq,
        problem =  "
            (declare-const x Int)
        ",
        "Substituted term is a flipped equality" {
            "(step t1 (cl (or (not (forall ((x Int)) (= x 0))) (= 0 1)))
                :rule forall_inst :args (1))"
            ->
            "(step t1.t1 (cl (= (= 1 0) (= 0 1))) :rule eq_symmetric)
            (step t1.t2 (cl (= (or (not (forall ((x Int)) (= x 0))) (= 1 0))
                               (or (not (forall ((x Int)) (= x 0))) (= 0 1))))
                :rule cong :premises (t1.t1))
            (step t1.t3 (cl (not (or (not (forall ((x Int)) (= x 0))) (= 1 0)))
                            (or (not (forall ((x Int)) (= x 0))) (= 0 1)))
                :rule equiv1 :premises (t1.t2))
            (step t1.t4 (cl (or (not (forall ((x Int)) (= x 0))) (= 1 0)))
                :rule forall_inst :args (1))
            (step t1 (cl (or (not (forall ((x Int)) (= x 0))) (= 0 1)))
                :rule resolution :premises (t1.t3 t1.t4)
                :args ((or (not (forall ((x Int)) (= x 0))) (= 1 0)) false))",
        }
    }
}

#[test]
fn subproof() {
    test_cases! {
        pipeline = Polyeq,
        problem =  "
            (declare-const p Bool)
            (declare-const r Bool)
            (declare-const s Bool)
        ",
        "Subproof last step conclusion is flipped" {
            "(anchor :step t1)
            (assume t1.h1 p)
            (step t1.inner (cl (= r s)) :rule hole)
            (step t1 (cl (not p) (= s r)) :rule subproof :discharge (t1.h1))"
            ->
            "(anchor :step t1)
            (assume t1.h1 p)
            (step t1.inner (cl (= r s)) :rule hole)
            (step t1.t1 (cl (= (= r s) (= s r))) :rule eq_symmetric)
            (step t1.t2 (cl (not (= r s)) (= s r)) :rule equiv1 :premises (t1.t1))
            (step t1.t3 (cl (= s r)) :rule resolution :premises (t1.t2 t1.inner)
                :args ((= r s) false))
            (step t1 (cl (not p) (= s r)) :rule subproof :discharge (t1.h1))",
        }
    }
}

#[test]
fn bfun_elim() {
    test_cases! {
        pipeline = Polyeq,
        problem =  "
            (declare-fun f (Bool) Bool)
            (declare-const a Bool)
            (assert (forall ((x Bool)) (= x true)))
        ",
        "Conclusion equality is flipped" {
            "(assume h1 (forall ((x Bool)) (= x true)))
            (step t1 (cl (and (= true false) (= true true))) :rule bfun_elim :premises (h1))"
            ->
            "(assume h1 (forall ((x Bool)) (= x true)))
            (step t1.t1 (cl (= (= false true) (= true false))) :rule eq_symmetric)
            (step t1.t2 (cl (= (and (= false true) (= true true))
                               (and (= true false) (= true true))))
                :rule cong :premises (t1.t1))
            (step t1.t3 (cl (not (and (= false true) (= true true)))
                            (and (= true false) (= true true)))
                :rule equiv1 :premises (t1.t2))
            (step t1.t4 (cl (and (= false true) (= true true)))
                :rule bfun_elim :premises (h1))
            (step t1 (cl (and (= true false) (= true true)))
                :rule resolution :premises (t1.t3 t1.t4)
                :args ((and (= false true) (= true true)) false))",
        }
    }
}

#[test]
fn distinct_elim_orientation() {
    test_cases! {
        pipeline = Polyeq,
        problem =  "
            (declare-const a Int)
            (declare-const b Int)
            (declare-const c Int)
        ",
        "One pair flipped: the step is elaborated and the original conclusion is rederived" {
            "(step t1 (cl (= (distinct a b c)
                             (and (not (= a b)) (not (= c a)) (not (= b c))))) :rule distinct_elim)"
            ->
            "(step t1.t1 (cl (= (distinct a b c)
                                (and (not (= a b)) (not (= a c)) (not (= b c))))) :rule distinct_elim)
            (step t1.t2 (cl (= (= a c) (= c a))) :rule eq_symmetric)
            (step t1.t3 (cl (= (not (= a c)) (not (= c a)))) :rule cong :premises (t1.t2))
            (step t1.t4 (cl (= (and (not (= a b)) (not (= a c)) (not (= b c)))
                               (and (not (= a b)) (not (= c a)) (not (= b c))))) :rule cong
                               :premises (t1.t3))
            (step t1 (cl (= (distinct a b c)
                            (and (not (= a b)) (not (= c a)) (not (= b c))))) :rule trans
                            :premises (t1.t1 t1.t4))",
        }
        "Binary distinct, flipped" {
            "(step t1 (cl (= (distinct a b) (not (= b a)))) :rule distinct_elim)"
            ->
            "(step t1.t1 (cl (= (distinct a b) (not (= a b)))) :rule distinct_elim)
            (step t1.t2 (cl (= (= a b) (= b a))) :rule eq_symmetric)
            (step t1.t3 (cl (= (not (= a b)) (not (= b a)))) :rule cong :premises (t1.t2))
            (step t1 (cl (= (distinct a b) (not (= b a)))) :rule trans :premises (t1.t1 t1.t3))",
        }
    }
}
