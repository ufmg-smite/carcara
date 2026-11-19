#[test]
fn cong() {
    test_cases! {
        pipeline = Local,
        problem =  "
            (declare-const a Bool)
            (declare-const b Bool)
            (declare-const c Bool)
            (declare-const d Bool)
            (declare-fun f (Bool) Bool)
        ",
        "Add symm to premises" {
            "(step t1 (cl (= b a)) :rule hole)
            (step t2 (cl (= d c)) :rule hole)
            (step t3 (cl (= (and a c) (and b d))) :rule cong :premises (t1 t2))" 
            ->
            "(step t1 (cl (= b a)) :rule hole)
            (step t2 (cl (= d c)) :rule hole)
            (step t3.t1 (cl (= a b)) :rule symm :premises (t1))
            (step t3.t2 (cl (= c d)) :rule symm :premises (t2))
            (step t3 (cl (= (and a c) (and b d))) :rule cong :premises (t3.t1 t3.t2))",

            "(step t1 (cl (= b a)) :rule hole)
            (step t2 (cl (= d c)) :rule hole)
            (step t3 (cl (= (= a c) (= b d))) :rule cong :premises (t1 t2))" 
            ->
            "(step t1 (cl (= b a)) :rule hole)
            (step t2 (cl (= d c)) :rule hole)
            (step t3.t1 (cl (= a b)) :rule symm :premises (t1))
            (step t3.t2 (cl (= c d)) :rule symm :premises (t2))
            (step t3 (cl (= (= a c) (= b d))) :rule cong :premises (t3.t1 t3.t2))",
        }
        "Congruence between identical terms" {
            "(step t2 (cl (= a a)) :rule hole)
            (step t1 (cl (= (f a) (f a))) :rule cong :premises (t2))"
            ->
            "(step t2 (cl (= a a)) :rule hole)
            (step t1 (cl (= (f a) (f a))) :rule refl)",
        }
        "Congruence between symmetric equalities" {
            "(step t2 (cl (= a b)) :rule hole)
            (step t3 (cl (= b a)) :rule hole)
            (step t1 (cl (= (= a b) (= b a))) :rule cong :premises (t2 t3))"
            ->
            "(step t2 (cl (= a b)) :rule hole)
            (step t3 (cl (= b a)) :rule hole)
            (step t1 (cl (= (= a b) (= b a))) :rule eq_symmetric)",
        }
        "Equality may be flipped" {
            "(step t2 (cl (= b c)) :rule hole)
            (step t3 (cl (= a d)) :rule hole)
            (step t1 (cl (= (= a b) (= c d))) :rule cong :premises (t2 t3))"
            ->
            "(step t2 (cl (= b c)) :rule hole)
            (step t3 (cl (= a d)) :rule hole)
            (step t1.t2 (cl (= (= a b) (= d c))) :rule cong :premises (t3 t2))
            (step t1.t1 (cl (= (= d c) (= c d))) :rule eq_symmetric)
            (step t1 (cl (= (= a b) (= c d))) :rule trans :premises (t1.t2 t1.t1))",

            "(step t2 (cl (= a d)) :rule hole)
            (step t3 (cl (= b c)) :rule hole)
            (step t1 (cl (= (= a b) (= c d))) :rule cong :premises (t2 t3))"
            ->
            "(step t2 (cl (= a d)) :rule hole)
            (step t3 (cl (= b c)) :rule hole)
            (step t1.t2 (cl (= (= a b) (= d c))) :rule cong :premises (t2 t3))
            (step t1.t1 (cl (= (= d c) (= c d))) :rule eq_symmetric)
            (step t1 (cl (= (= a b) (= c d))) :rule trans :premises (t1.t2 t1.t1))",
        }
    }
}

#[test]
fn eq_congruent_pred() {
    test_cases! {
        pipeline = Local,
        problem =  "
            (declare-const a Bool)
            (declare-const b Bool)
            (declare-const c Bool)
            (declare-const d Bool)
        ",
        "Add symm to flipped premises" {
            "(step t1 (cl (not (= b a)) (not (= d c)) (not (and a c)) (and b d))
                :rule eq_congruent_pred)"
            ->
            "(step t1.t1 (cl (not (= a b)) (not (= c d)) (not (and a c)) (and b d))
                :rule eq_congruent_pred)
            (step t1.t2 (cl (= (= b a) (= a b))) :rule eq_symmetric)
            (step t1.t3 (cl (not (= b a)) (= a b)) :rule equiv1 :premises (t1.t2))
            (step t1.t4 (cl (= (= d c) (= c d))) :rule eq_symmetric)
            (step t1.t5 (cl (not (= d c)) (= c d)) :rule equiv1 :premises (t1.t4))
            (step t1.t6 (cl (not (and a c)) (and b d) (not (= b a)) (not (= d c)))
                :rule resolution :premises (t1.t1 t1.t3 t1.t5) :args ((= a b) false (= c d) false))
            (step t1 (cl (not (= b a)) (not (= d c)) (not (and a c)) (and b d))
                :rule reordering :premises (t1.t6))",
        }
        "Conclusion terms in the flipped order" {
            "(step t1 (cl (not (= b a)) (not (= d c)) (and b d) (not (and a c)))
                :rule eq_congruent_pred)"
            ->
            "(step t1.t1 (cl (not (= a b)) (not (= c d)) (not (and a c)) (and b d))
                :rule eq_congruent_pred)
            (step t1.t2 (cl (= (= b a) (= a b))) :rule eq_symmetric)
            (step t1.t3 (cl (not (= b a)) (= a b)) :rule equiv1 :premises (t1.t2))
            (step t1.t4 (cl (= (= d c) (= c d))) :rule eq_symmetric)
            (step t1.t5 (cl (not (= d c)) (= c d)) :rule equiv1 :premises (t1.t4))
            (step t1.t6 (cl (not (and a c)) (and b d) (not (= b a)) (not (= d c)))
                :rule resolution :premises (t1.t1 t1.t3 t1.t5) :args ((= a b) false (= c d) false))
            (step t1 (cl (not (= b a)) (not (= d c)) (and b d) (not (and a c)))
                :rule reordering :premises (t1.t6))",
        }
        "No flipped premises" {
            "(step t1 (cl (not (= a b)) (not (= c d)) (not (and a c)) (and b d))
                :rule eq_congruent_pred)"
            ->
            "(step t1 (cl (not (= a b)) (not (= c d)) (not (and a c)) (and b d))
                :rule eq_congruent_pred)",
        }
        "Flipped conclusion terms, no flipped premises" {
            "(step t1 (cl (not (= a b)) (not (= c d)) (and b d) (not (and a c)))
                :rule eq_congruent_pred)"
            ->
            "(step t1.t1 (cl (not (= a b)) (not (= c d)) (not (and a c)) (and b d))
                :rule eq_congruent_pred)
            (step t1 (cl (not (= a b)) (not (= c d)) (and b d) (not (and a c)))
                :rule reordering :premises (t1.t1))",
        }
    }
}

#[test]
fn eq_congruent() {
    test_cases! {
        pipeline = Local,
        problem =  "
            (declare-const a Int)
            (declare-const b Int)
            (declare-const c Int)
            (declare-fun f (Int Int Int) Int)
        ",
        "Add symm to premises" {
            "(step t1
                (cl (not (= 0 a)) (not (= b 1)) (not (= 2 c)) (= (f a b c) (f 0 1 2)))
                :rule eq_congruent)"
            ->
            "(step t1.t1
                (cl (not (= a 0)) (not (= b 1)) (not (= c 2)) (= (f a b c) (f 0 1 2)))
                :rule eq_congruent)

            (step t1.t2 (cl (= (= 0 a) (= a 0))) :rule eq_symmetric)
            (step t1.t3 (cl (not (= 0 a)) (= a 0)) :rule equiv1 :premises (t1.t2))

            (step t1.t4 (cl (= (= 2 c) (= c 2))) :rule eq_symmetric)
            (step t1.t5 (cl (not (= 2 c)) (= c 2)) :rule equiv1 :premises (t1.t4))

            (step t1.t6
                (cl (not (= b 1)) (= (f a b c) (f 0 1 2)) (not (= 0 a)) (not (= 2 c)))
                :rule resolution :premises (t1.t1 t1.t3 t1.t5) :args ((= a 0) false (= c 2) false))

            (step t1
                (cl (not (= 0 a)) (not (= b 1)) (not (= 2 c)) (= (f a b c) (f 0 1 2)))
                :rule reordering :premises (t1.t6))",
        }
        "Duplicate premises" {
           "(step t1 (cl (not (= 1 a)) (not (= 1 a)) (= (* a a) (* 1 1))) :rule eq_congruent)"
           ->
           "(step t1.t1 (cl (not (= a 1)) (not (= a 1)) (= (* a a) (* 1 1))) :rule eq_congruent)
            (step t1.t2 (cl (not (= a 1)) (= (* a a) (* 1 1))) :rule contraction :premises (t1.t1))
            (step t1.t3 (cl (= (= 1 a) (= a 1))) :rule eq_symmetric)
            (step t1.t4 (cl (not (= 1 a)) (= a 1)) :rule equiv1 :premises (t1.t3))
            (step t1.t5 (cl (= (* a a) (* 1 1)) (not (= 1 a)))
                :rule resolution :premises (t1.t2 t1.t4) :args ((= a 1) false))
            (step t1.t6 (cl (= (* a a) (* 1 1)) (not (= 1 a)) (not (= 1 a)))
                :rule weakening :premises (t1.t5))
            (step t1 (cl (not (= 1 a)) (not (= 1 a)) (= (* a a) (* 1 1)))
                :rule reordering :premises (t1.t6))",
       }
    }
}
