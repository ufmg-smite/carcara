#[test]
fn trans() {
    test_cases! {
        pipeline = Local,
        problem =  "
            (declare-sort T 0)
            (declare-const a T)
            (declare-const b T)
            (declare-const c T)
            (declare-const d T)
        ",
        "Reorder premises" {
            "(assume h1 (= a b))
            (assume h2 (= c d))
            (assume h3 (= b c))
            (step t4 (cl (= a d)) :rule trans :premises (h1 h2 h3))"
            ->
            "(assume h1 (= a b))
            (assume h2 (= c d))
            (assume h3 (= b c))
            (step t4 (cl (= a d)) :rule trans :premises (h1 h3 h2))",
        }
        "Add symm to flipped premises" {
            "(assume h1 (= b a))
            (assume h2 (= b c))
            (step t3 (cl (= a c)) :rule trans :premises (h1 h2))"
            ->
            "(assume h1 (= b a))
            (assume h2 (= b c))
            (step t3.t1 (cl (= a b)) :rule symm :premises (h1))
            (step t3 (cl (= a c)) :rule trans :premises (t3.t1 h2))",
        }
        "Reflexive conclusion" {
            "(assume h1 (= a b))
            (assume h2 (= b a))
            (step t3 (cl (= a a)) :rule trans :premises (h1 h2))"
            ->
            "(assume h1 (= a b))
            (assume h2 (= b a))
            (step t3 (cl (= a a)) :rule eq_reflexive)",
        }
        "Remove unused premises" {
            "(assume h1 (= a b))
            (assume h2 (= c d))
            (assume h3 (= b c))
            (step t4 (cl (= a c)) :rule trans :premises (h1 h2 h3))"
            ->
            "(assume h1 (= a b))
            (assume h2 (= c d))
            (assume h3 (= b c))
            (step t4 (cl (= a c)) :rule trans :premises (h1 h3))",
        }
    }
}

#[test]
fn eq_transitive() {
    test_cases! {
        pipeline = Local,
        problem =  "
            (declare-sort T 0)
            (declare-const a T)
            (declare-const b T)
            (declare-const c T)
            (declare-const d T)
            (declare-const x T)
            (declare-const y T)
        ",
        "Reorder and flip premises" {
            "(step t1 (cl (not (= a b)) (not (= c b)) (not (= c d)) (= d a))
                :rule eq_transitive)"
            ->
            "(step t1.t1 (cl (not (= d c)) (not (= c b)) (not (= b a)) (= d a))
                :rule eq_transitive)
            (step t1.t2 (cl (= (= d c) (= c d))) :rule eq_symmetric)
            (step t1.t3 (cl (= d c) (not (= c d))) :rule equiv2 :premises (t1.t2))
            (step t1.t4 (cl (= (= b a) (= a b))) :rule eq_symmetric)
            (step t1.t5 (cl (= b a) (not (= a b))) :rule equiv2 :premises (t1.t4))
            (step t1.t6 (cl (not (= c b)) (= d a) (not (= c d)) (not (= a b)))
                :rule resolution :premises (t1.t1 t1.t3 t1.t5) :args ((= d c) false (= b a) false))
            (step t1 (cl (not (= a b)) (not (= c b)) (not (= c d)) (= d a))
                :rule reordering :premises (t1.t6))",
        }
        "Remove unused premises" {
            "(step t1 (cl (not (= a b)) (not (= b c)) (not (= c d)) (not (= x y)) (= a d))
                :rule eq_transitive)"
            ->
            "(step t1.t1 (cl (not (= a b)) (not (= b c)) (not (= c d)) (= a d))
                :rule eq_transitive)
            (step t1.t2 (cl (not (= a b)) (not (= b c)) (not (= c d)) (= a d) (not (= x y)))
                :rule weakening :premises (t1.t1))
            (step t1 (cl (not (= a b)) (not (= b c)) (not (= c d)) (not (= x y)) (= a d))
                :rule reordering :premises (t1.t2))",
        }
        "Reflexive conclusion" {
            "(step t1 (cl (not (= a b)) (not (= b c)) (= a a)) :rule eq_transitive)"
            ->
            "(step t1.t1 (cl (= a a)) :rule eq_reflexive)
            (step t1.t2 (cl (= a a) (not (= a b)) (not (= b c))) :rule weakening :premises (t1.t1))
            (step t1 (cl (not (= a b)) (not (= b c)) (= a a)) :rule reordering :premises (t1.t2))",
        }
        "Chain with a single link" {
            "(step t1 (cl (not (= a b)) (not (= b c)) (= a b)) :rule eq_transitive)"
            ->
            "(step t1.t1 (cl (not (= a b)) (= a b)) :rule eq_transitive)
            (step t1.t2 (cl (not (= a b)) (= a b) (not (= b c))) :rule weakening :premises (t1.t1))
            (step t1 (cl (not (= a b)) (not (= b c)) (= a b)) :rule reordering :premises (t1.t2))",
        }
    }
}
