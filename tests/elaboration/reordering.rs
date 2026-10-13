#[test]
fn remove_reorderings() {
    test_cases! {
        pipeline = Reordering,
        problem =  "
            (declare-const a Bool)
            (declare-const b Bool)
            (declare-const c Bool)
            (declare-const d Bool)
        ",
        "Simple cases" {
            "(step t1 (cl a b) :rule hole)
            (step t2 (cl b a) :rule reordering :premises (t1))
            (step t3 (cl (not a)) :rule hole)
            (step t4 (cl b) :rule resolution :premises (t2 t3) :args (a true))"
            ->
            "(step t1 (cl a b) :rule hole)
            (step t3 (cl (not a)) :rule hole)
            (step t4 (cl b) :rule resolution :premises (t1 t3) :args (a true))",

            "(step t1 (cl a b) :rule hole)
            (step t2 (cl b a) :rule reordering :premises (t1))
            (step t3 (cl a b) :rule reordering :premises (t2))"
            ->
            "(step t1 (cl a b) :rule hole)",
        }
        "Contraction conclusion is recomputed" {
            "(step t1 (cl a b a) :rule hole)
            (step t2 (cl b a a) :rule reordering :premises (t1))
            (step t3 (cl b a) :rule contraction :premises (t2))"
            ->
            "(step t1 (cl a b a) :rule hole)
            (step t3 (cl a b) :rule contraction :premises (t1))",
        }
        "Weakening conclusion is recomputed" {
            "(step t1 (cl a b) :rule hole)
            (step t2 (cl b a) :rule reordering :premises (t1))
            (step t3 (cl b a c) :rule weakening :premises (t2))"
            ->
            "(step t1 (cl a b) :rule hole)
            (step t3 (cl a b c) :rule weakening :premises (t1))",
        }
        "Resolution conclusion is recomputed" {
            "(step t1 (cl a b c) :rule hole)
            (step t2 (cl c b a) :rule reordering :premises (t1))
            (step t3 (cl (not c) d) :rule hole)
            (step t4 (cl b a d) :rule resolution :premises (t2 t3) :args (c true))"
            ->
            "(step t1 (cl a b c) :rule hole)
            (step t3 (cl (not c) d) :rule hole)
            (step t4 (cl a b d) :rule resolution :premises (t1 t3) :args (c true))",
        }
        "Steps whose premises are unchanged are not recomputed" {
            "(step t1 (cl a b) :rule hole)
            (step t2 (cl (not b) a) :rule hole)
            (step t3 (cl a) :rule resolution :premises (t1 t2) :args (b true))
            (step t4 (cl a c) :rule weakening :premises (t3))"
            ->
            "(step t1 (cl a b) :rule hole)
            (step t2 (cl (not b) a) :rule hole)
            (step t3 (cl a) :rule resolution :premises (t1 t2) :args (b true))
            (step t4 (cl a c) :rule weakening :premises (t3))",
        }
        "Resolution conclusion is kept if it relies on implicit contraction" {
            "(step t1 (cl a b) :rule hole)
            (step t2 (cl (not b) a) :rule hole)
            (step t3 (cl a (not b)) :rule reordering :premises (t2))
            (step t4 (cl a) :rule resolution :premises (t1 t3) :args (b true))
            (step t5 (cl a c) :rule weakening :premises (t4))"
            ->
            "(step t1 (cl a b) :rule hole)
            (step t2 (cl (not b) a) :rule hole)
            (step t4 (cl a) :rule resolution :premises (t1 t2) :args (b true))
            (step t5 (cl a c) :rule weakening :premises (t4))",
        }
    }
}
