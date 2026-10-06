#[test]
fn drup() {
    test_cases! {
        definitions = "
            (declare-const a Bool)
            (declare-const b Bool)
            (declare-const c Bool)
            (declare-const d Bool)
            (declare-const e Bool)
        ",
        "Simple working examples" {
            "(assume a0 (or a c))
            (assume a1 (or a (not c) d))
            (assume a2 (or (not d) e))
            (assume a3 (or (not d) (not e)))
            (assume a4 (not a))
            (assume a5 (not b))
            (step t0 (cl a c) :rule or :premises (a0))
            (step t1 (cl a (not c) d) :rule or :premises (a1))
            (step t2 (cl (not d) e) :rule or :premises (a2))
            (step t3 (cl (not d) (not e)) :rule or :premises (a3))
            (step t4 (cl a b) :rule drup :premises (t0 t1 t2 t3) :args ((cl a b)))": true,

            "
            (assume a1 (not a))
            (assume a2 (not b))
            (assume a3 (or a b))
            (step t0 (cl a b) :rule or :premises (a3))
            (step t1 (cl) :rule drup :premises (a1 a2 t0) :args ((cl)))": true,
        }

        "Simple false-working examples" {
            "(assume a0 (or a c))
            (assume a1 (or a (not c) d))
            (assume a2 (or (not d) e))
            (assume a4 (not a))
            (assume a5 (not b))
            (step t0 (cl a c) :rule or :premises (a0))
            (step t1 (cl a (not c) d) :rule or :premises (a1))
            (step t2 (cl (not d) e) :rule or :premises (a2))
            (step t4 (cl a) :rule drup :premises (t0 t1 t2) :args ((cl a b)))": false,

            "
            (assume a1 (not a))
            (assume a3 (or a b))
            (step t0 (cl a b) :rule or :premises (a3))
            (step t1 (cl) :rule drup :premises (a1 t0) :args ((cl)))": false,
        }
        "Deleting unit clauses" {
            "(assume a1 (not a))
            (assume a3 (or a b))
            (step t0 (cl a b) :rule or :premises (a3))
            (step t1 (cl b) :rule drup :premises (a1 t0) :args ((cl b)))": true,

            "(assume a1 (not a))
            (assume a3 (or a b))
            (step t0 (cl a b) :rule or :premises (a3))
            (step t1 (cl b) :rule drup :premises (a1 t0) :args ((@d (cl (not a))) (cl b)))": false,
        }
        "Arguments that are not clauses" {
            "(assume a0 a)
            (step t1 (cl a) :rule drup :premises (a0) :args (a))": false,

            "(assume a0 a)
            (step t1 (cl a) :rule drup :premises (a0) :args ((@d a) (cl a)))": false,
        }
    }
}

#[test]
fn drat() {
    test_cases! {
        definitions = "
            (declare-const a Bool)
            (declare-const b Bool)
            (declare-const c Bool)
            (declare-const d Bool)
            (declare-const e Bool)
        ",
        "DRAT working examples (validates DRAT rule functionality)" {
            "(assume a1 (not a))
            (assume a2 (not b))
            (assume a3 (or a b))
            (step t0 (cl a b) :rule or :premises (a3))
            (step t1 (cl) :rule drat :premises (a1 a2 t0) :args ((cl)))": true,

            // `(cl c)` is not RUP, but it is RAT, since no clause contains `(not c)`
            "(assume a0 (or a b))
            (assume a1 (or a (not b)))
            (assume a2 (or (not a) b))
            (assume a3 (or (not a) (not b)))
            (step t0 (cl a b) :rule or :premises (a0))
            (step t1 (cl a (not b)) :rule or :premises (a1))
            (step t2 (cl (not a) b) :rule or :premises (a2))
            (step t3 (cl (not a) (not b)) :rule or :premises (a3))
            (step t4 (cl) :rule drat :premises (t0 t1 t2 t3) :args ((cl c) (cl a) (cl)))": true,
        }
        "The conclusion must be the empty clause" {
            "(assume a0 (or a c))
            (assume a1 (or a (not c) d))
            (assume a2 (or (not d) e))
            (assume a3 (or (not d) (not e)))
            (step t0 (cl a c) :rule or :premises (a0))
            (step t1 (cl a (not c) d) :rule or :premises (a1))
            (step t2 (cl (not d) e) :rule or :premises (a2))
            (step t3 (cl (not d) (not e)) :rule or :premises (a3))
            (step t4 (cl a b) :rule drat :premises (t0 t1 t2 t3) :args ((cl a b)))": false,

            // `(cl a)` is RAT, but doesn't follow from the (empty) set of premises
            "(step t1 (cl a) :rule drat :args ((cl a)))": false,
        }

        "DRAT failing examples" {
            "(assume a1 (not a))
            (assume a3 (or a b))
            (step t0 (cl a b) :rule or :premises (a3))
            (step t1 (cl) :rule drat :premises (a1 t0) :args ((cl)))": false,

            "(assume a0 (or a c))
            (assume a1 (or a (not c) d))
            (assume a2 (or (not d) e))
            (step t0 (cl a c) :rule or :premises (a0))
            (step t1 (cl a (not c) d) :rule or :premises (a1))
            (step t2 (cl (not d) e) :rule or :premises (a2))
            (step t4 (cl) :rule drat :premises (t0 t1 t2) :args ((cl a b)))": false,
        }
        "Arguments that are not clauses" {
            "(assume a0 a)
            (step t1 (cl) :rule drat :premises (a0) :args (a))": false,
        }
    }
}
