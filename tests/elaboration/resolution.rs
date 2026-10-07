#[test]
fn infer_pivots() {
    test_cases! {
        pipeline = Local,
        problem =  "
            (declare-const p Bool)
            (declare-const q Bool)
            (declare-const r Bool)
            (declare-const s Bool)
        ",
        "Simple cases" {
            "(step t1 (cl p q r) :rule hole)
            (step t2 (cl (not p)) :rule hole)
            (step t3 (cl q r) :rule resolution :premises (t1 t2))"
            ->
            "(step t1 (cl p q r) :rule hole)
            (step t2 (cl (not p)) :rule hole)
            (step t3 (cl q r) :rule resolution :premises (t1 t2) :args (p true))",

            "(step t1 (cl (not p) (not q) (not r)) :rule hole)
            (step t2 (cl p) :rule hole)
            (step t3 (cl q) :rule hole)
            (step t4 (cl r) :rule hole)
            (step t5 (cl) :rule resolution :premises (t1 t2 t3 t4))"
            ->
            "(step t1 (cl (not p) (not q) (not r)) :rule hole)
            (step t2 (cl p) :rule hole)
            (step t3 (cl q) :rule hole)
            (step t4 (cl r) :rule hole)
            (step t5 (cl) :rule resolution :premises (t1 t2 t3 t4)
                :args (p false q false r false))",
        }
        "Implicit elimination of false" {
            "(step t1 (cl p q false) :rule hole)
            (step t2 (cl (not p)) :rule hole)
            (step t3 (cl (not q)) :rule hole)
            (step t4 (cl) :rule resolution :premises (t1 t2 t3))"
            ->
            "(step t1 (cl p q false) :rule hole)
            (step t2 (cl (not p)) :rule hole)
            (step t3 (cl (not q)) :rule hole)
            (step t4 (cl) :rule resolution :premises (t1 t2 t3) :args (p true q true))",
        }
        "Removal of duplicate premises" {
            "(step t1 (cl (not r)) :rule hole)
            (step t2 (cl p q r s) :rule hole)
            (step t3 (cl p q s) :rule th_resolution :premises (t1 t2 t2))"
            ->
            "(step t1 (cl (not r)) :rule hole)
            (step t2 (cl p q r s) :rule hole)
            (step t3 (cl p q s) :rule resolution :premises (t1 t2) :args (r false))",
        }
    }
}

#[test]
fn edge_cases() {
    test_cases! {
        pipeline = Local,
        problem =  "
            (declare-const p Bool)
            (declare-const q Bool)
        ",
        "Empty clause from a single (not true) premise" {
            "(step t1 (cl (not true)) :rule hole)
            (step t2 (cl) :rule th_resolution :premises (t1))"
            ->
            "(step t1 (cl (not true)) :rule hole)
            (step t2.t1 (cl true) :rule true)
            (step t2 (cl) :rule resolution :premises (t1 t2.t1) :args (true false))",
        }
        "Double negation in conclusion" {
            "(assume h1 (not p))
            (step t2 (cl p q) :rule hole)
            (step t3 (cl (not (not q))) :rule resolution :premises (h1 t2))"
            ->
            "(assume h1 (not p))
            (step t2 (cl p q) :rule hole)
            (step t3.t1 (cl q) :rule resolution :premises (h1 t2) :args (p false))
            (step t3.t2 (cl (not (not (not (not q)))) (not q)) :rule not_not)
            (step t3.t3 (cl (not (not (not (not (not q))))) (not (not q))) :rule not_not)
            (step t3 (cl (not (not q))) :rule resolution :premises (t3.t1 t3.t2 t3.t3)
                :args (q true (not (not (not (not q)))) true))",
        }
    }
}
