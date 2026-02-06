#[test]
fn forall_inst() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun a () Real)
            (declare-fun b () Real)
            (declare-fun x () Real)
        ",
        "Simple working examples" {
            "(step t1 (cl (or (not (forall ((p Bool)) p)) q))
                :rule forall_inst :args (q))": true,

            "(step t1 (cl (or (not (forall ((x Real) (y Real)) (= x y))) (= a b)))
                :rule forall_inst :args (a b))": true,

            "(step t1 (cl (or (not (forall ((x Real)) (= x a))) (= a a)))
                :rule forall_inst :args (a))": true,

            "(step t1 (cl (or (not (forall ((p Bool)) p)) (ite q (= a b) (and (= a 0.0) true))))
                :rule forall_inst :args ((ite q (= a b) (and (= a 0.0) true))))": true,
        }
        "Equalities may be flipped" {
            "(step t1 (cl (or (not (forall ((x Real) (y Real)) (and (= x y) (= 1 0))))
                (and (= b a) (= 1 0)))) :rule forall_inst :args (a b))": true,
        }
        "Bound variables may be renamed by substitution" {
            // The variable shadowing makes it so the substitution applied by Carcara renames p
            "(step t1 (cl (or
                (not (forall ((p Bool) (r Bool)) (and p (forall ((p Bool)) p))))
                (and q (forall ((p Bool)) p))
            )) :rule forall_inst :args (q q))": true,
        }
        "Argument is not in quantifier bindings" {
            "(step t1 (cl (or (not (forall ((x Real)) (= x a))) (= b 0.0)))
                :rule forall_inst :args (b 0.0))": false,
        }
        "Binding has no associated substitution" {
            "(step t1 (cl (or (not (forall ((x Real) (y Real)) (= x x))) (= a a)))
                :rule forall_inst :args (a))": false,
        }
        "Substitution was not applied" {
            "(step t1 (cl (or (not (forall ((x Real) (y Real)) (= x y))) (= x b)))
                :rule forall_inst :args (a b))": false,
        }
        "Applied substitution was not passed as argument" {
            "(step t1 (cl (or (not (forall ((x Real) (y Real)) (= x y))) (= a b)))
                :rule forall_inst :args (a))": false,
        }
        "Wrong type of rule argument" {
            "(step t1 (cl (or (not (forall ((x Real) (y Real)) (= x y))) (= a b)))
                :rule forall_inst :args ((= x a) b))": false,
        }
    }
}

#[test]
fn qnt_join() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun a () Real)
            (declare-fun b () Real)
            (declare-fun x () Real)
        ",
        "Simple working examples" {
            "(step t1 (cl (=
                (forall ((x Real)) (forall ((y Real)) (= x y)))
                (forall ((x Real) (y Real)) (= x y))
            )) :rule qnt_join)": true,

            "(step t1 (cl (=
                (forall ((x Real) (y Real)) (forall ((z Real) (w Real)) (= (+ x y) (+ z w))))
                (forall ((x Real) (y Real) (z Real) (w Real)) (= (+ x y) (+ z w)))
            )) :rule qnt_join)": true,
        }
        "Bindings in wrong order" {
            "(step t1 (cl (=
                (forall ((x Real)) (forall ((y Real)) (= x y)))
                (forall ((y Real) (x Real)) (= x y))
            )) :rule qnt_join)": false,

            "(step t1 (cl (=
                (forall ((x Real) (y Real)) (forall ((z Real) (w Real)) (= (+ x y) (+ z w))))
                (forall ((z Real) (y Real) (w Real) (x Real)) (= (+ x y) (+ z w)))
            )) :rule qnt_join)": false,
        }
        "Removing duplicates" {
            "(step t1 (cl (=
                (forall ((p Bool)) (forall ((p Bool)) p))
                (forall ((p Bool)) p)
            )) :rule qnt_join)": true,

            "(step t1 (cl (=
                (forall ((x Real) (y Real)) (forall ((y Real) (z Real)) (distinct x y z)))
                (forall ((x Real) (y Real) (z Real)) (distinct x y z))
            )) :rule qnt_join)": true,

            "(step t1 (cl (=
                (forall ((x Real) (y Real)) (forall ((x Real) (y Real)) (= x y)))
                (forall ((x Real) (y Real)) (= x y))
            )) :rule qnt_join)": true,

            "(step t1 (cl (=
                (forall ((x Real) (y Real)) (forall ((z Real) (x Real)) (distinct x y z)))
                (forall ((x Real) (y Real) (z Real) (x Real)) (distinct x y z))
            )) :rule qnt_join)": false,
        }
    }
}

#[test]
fn qnt_rm_unused() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun a () Real)
            (declare-fun b () Real)
            (declare-fun x () Real)
        ",
        "Simple working examples" {
            "(step t1 (cl (=
                (forall ((x Real) (y Real) (z Real)) (= x z))
                (forall ((x Real) (z Real)) (= x z))
            )) :rule qnt_rm_unused)": true,

            "(step t1 (cl (=
                (forall ((x Real) (y Real) (z Real) (w Real)) (= y y))
                (forall ((y Real)) (= y y))
            )) :rule qnt_rm_unused)": true,
        }
        "Bindings in wrong order" {
            // Deviates from spec, but is still sound
            "(step t1 (cl (=
                (forall ((x Real) (y Real) (z Real)) (= x z))
                (forall ((z Real) (x Real)) (= x z))
            )) :rule qnt_rm_unused)": true,
        }
        "Not all unused bindings were removed" {
            "(step t1 (cl (=
                (forall ((x Real) (y Real) (z Real) (w Real)) (= y y))
                (forall ((y Real) (w Real)) (= y y))
            )) :rule qnt_rm_unused)": true,
        }
        "Inner term is the opposite quantifier" {
            "(step t1 (cl (=
                (exists ((?v0 Int)) (forall ((?v1 Int) (?v2 Int)) (= ?v1 ?v2)))
                (forall ((?v1 Int) (?v2 Int)) (= ?v1 ?v2))
            )) :rule qnt_rm_unused)": true,
        }
        "Duplicate removal" {
            "(step t1 (cl (=
                (forall ((x Real) (y Real) (x Real)) (= x y))
                (forall ((x Real) (y Real)) (= x y))
            )) :rule qnt_rm_unused)": true,

            "(step t1 (cl (=
                (forall ((x Real) (y Real) (x Real)) (= x y))
                (forall ((y Real) (x Real)) (= x y))
            )) :rule qnt_rm_unused)": true,
        }
    }
}

#[test]
fn qnt_cnf() {
    test_cases! {
        definitions = "",
        "Simple working examples" {
            "(step t1 (cl (or (not (forall ((p Bool)) p)) (forall ((p Bool)) p)))
                :rule qnt_cnf)": true,

            "(step t1 (cl (or
                (not (forall ((p Bool) (q Bool)) (not (and p q))))
                (forall ((p Bool) (q Bool)) (or (not p) (not q)))
            )) :rule qnt_cnf)": true,
        }
        "Selecting only one clause from conjunction" {
            "(step t1 (cl (or
                (not (forall ((p Bool) (q Bool)) (or (and p true) (and q false))))
                (forall ((p Bool) (q Bool)) (or true q))
            )) :rule qnt_cnf)": true,

            "(step t1 (cl (or
                (not (forall ((p Bool) (q Bool))
                    (not (and (=> p q) (or q (not (not p))) (or true false (not q))))
                ))
                (forall ((p Bool) (q Bool)) (or p (not q) (not true)))
            )) :rule qnt_cnf)": true,
        }
        "Quantifier bindings added due to prenexing" {
            "(step t1 (cl (or
                (not (forall ((p Bool)) (forall ((q Bool)) (or p q))))
                (forall ((p Bool) (q Bool)) (or p q))
            )) :rule qnt_cnf)": true,

            "(step t1 (cl (or
                (not (forall ((p Bool)) (not (exists ((q Bool)) (and p q)))))
                (forall ((p Bool) (q Bool)) (or (not p) (not q)))
            )) :rule qnt_cnf)": true,

            "(step t1 (cl (or
                (not (forall ((p Bool)) (or p (and false (forall ((q Bool)) q)))))
                (forall ((p Bool)) (or p false))
            )) :rule qnt_cnf)": true,
        }
    }
}

#[test]
fn miniscope_distribute() {
    test_cases! {
        definitions = "
            (declare-fun r () Bool)
            (declare-fun s () Bool)
        ",
        "Simple working examples" {
            "(step t1 (cl (=
                (forall ((p Bool) (q Bool)) (and p q false))
                (and
                    (forall ((p Bool) (q Bool)) p)
                    (forall ((p Bool) (q Bool)) q)
                    (forall ((p Bool) (q Bool)) false)
                )
            )) :rule miniscope_distribute)": true,

            "(step t1 (cl (=
                (exists ((p Bool)) (or r s p))
                (or (exists ((p Bool)) r) (exists ((p Bool)) s) (exists ((p Bool)) p))
            )) :rule miniscope_distribute)": true,
        }
        "Different quantifiers" {
            "(step t1 (cl (=
                (exists ((p Bool)) (or r s p))
                (or (exists ((p Bool)) r) (forall ((p Bool)) s) (forall ((p Bool)) p))
            )) :rule miniscope_distribute)": false,
        }
        "Wrong operator" {
            "(step t1 (cl (=
                (forall ((p Bool)) (and p p))
                (or (forall ((p Bool)) p) (forall ((p Bool)) p))
            )) :rule miniscope_distribute)": false,

            "(step t1 (cl (=
                (exists ((p Bool)) (and p p))
                (or (exists ((p Bool)) p) (exists ((p Bool)) p))
            )) :rule miniscope_distribute)": false,
        }
        "Wrong number of arguments" {
            "(step t1 (cl (=
                (forall ((p Bool)) (and p p))
                (and (forall ((p Bool)) p))
            )) :rule miniscope_distribute)": false,
        }
        "Wrong binding list" {
            "(step t1 (cl (=
                (forall ((p Bool) (q Bool)) (and p q false))
                (and
                    (forall ((p Bool) (q Bool)) p)
                    (forall ((p Bool) (q Bool)) q)
                    (forall ((p Bool)) false)
                )
            )) :rule miniscope_distribute)": false,

            "(step t1 (cl (=
                (forall ((p Bool) (q Bool)) (and p q false))
                (and
                    (forall ((p Bool) (q Bool)) p)
                    (forall ((p Bool) (q Bool)) q)
                    (forall ((p Bool) (x Int)) false)
                )
            )) :rule miniscope_distribute)": false,
        }
    }
}

#[test]
fn miniscope_split() {
    test_cases! {
        definitions = "
            (declare-fun r () Bool)
        ",
        "Simple working examples" {
            "(step t1 (cl (=
                (forall ((p Bool) (q Bool)) (or p q))
                (or (forall ((p Bool)) p) (forall ((q Bool)) q))
            )) :rule miniscope_split)": true,

            "(step t1 (cl (=
                (exists ((p Bool) (q Bool)) (and p q (= p q)))
                (and
                    (exists ((p Bool)) p)
                    (exists ((q Bool)) q)
                    (exists ((p Bool) (q Bool)) (= p q))
                )
            )) :rule miniscope_split)": true,
        }
        "Different quantifiers" {
            "(step t1 (cl (=
                (forall ((p Bool)) (or p p))
                (or (forall ((p Bool)) p) (exists ((p Bool)) p))
            )) :rule miniscope_distribute)": false,
        }
        "Wrong operator" {
            "(step t1 (cl (=
                (forall ((p Bool)) (or p p))
                (and (forall ((p Bool)) p) (forall ((p Bool)) p))
            )) :rule miniscope_distribute)": false,

            "(step t1 (cl (=
                (exists ((p Bool)) (or p p))
                (and (exists ((p Bool)) p) (exists ((p Bool)) p))
            )) :rule miniscope_distribute)": false,
        }
        "Wrong number of arguments" {
            "(step t1 (cl (=
                (forall ((p Bool)) (or p p))
                (or (forall ((p Bool)) p))
            )) :rule miniscope_distribute)": false,
        }
        "Wrong binding list" {
            "(step t1 (cl (=
                (forall ((p Bool) (q Bool)) (and p q))
                (and (forall ((p Bool)) p) (forall ((q Bool) (x Int)) q))
            )) :rule miniscope_distribute)": false,

            "(step t1 (cl (=
                (forall ((p Bool) (r Bool)) (and p r))
                (and (forall ((p Bool)) p) (forall ((p Bool)) r))
            )) :rule miniscope_distribute)": false,
        }
    }
}

#[test]
fn miniscope_ite() {
    test_cases! {
        definitions = "
            (declare-fun r () Bool)
        ",
        "Simple working examples" {
            "(step t1 (cl (=
                (forall ((p Bool) (q Bool)) (ite r true false))
                (ite r (forall ((p Bool) (q Bool)) true) (forall ((p Bool) (q Bool)) false))
            )) :rule miniscope_ite)": true,
        }
        "Wrong format" {
            "(step t1 (cl (=
                (forall ((p Bool)) (ite r true false))
                (ite r (forall ((p Bool)) true) (exists ((p Bool)) false))
            )) :rule miniscope_ite)": false,

            "(step t1 (cl (=
                (forall ((p Bool)) (ite r true false))
                (ite (forall ((p Bool)) r) (forall ((p Bool)) true) (forall ((p Bool)) false))
            )) :rule miniscope_ite)": false,
        }
        "Wrong binding list" {
            "(step t1 (cl (=
                (forall ((p Bool)) (ite r true false))
                (ite r (forall ((p Bool)) true) (forall ((q Bool)) false))
            )) :rule miniscope_ite)": false,
        }
        "Wrong phis" {
            "(step t1 (cl (=
                (forall ((p Bool)) (ite r true false))
                (ite r (forall ((p Bool)) false) (forall ((p Bool)) true))
            )) :rule miniscope_ite)": false,
        }
        "Bound variable in condition" {
            "(step t1 (cl (=
                (forall ((r Bool)) (ite r true false))
                (ite r (forall ((r Bool)) false) (forall ((r Bool)) true))
            )) :rule miniscope_ite)": false,
        }
    }
}
