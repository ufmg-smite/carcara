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
            "(step t1 (cl (=
                (forall ((x Real) (y Real) (z Real)) (= x z))
                (forall ((z Real) (x Real)) (= x z))
            )) :rule qnt_rm_unused)": false,
        }
        "Not all unused bindings were removed" {
            "(step t1 (cl (=
                (forall ((x Real) (y Real) (z Real) (w Real)) (= y y))
                (forall ((y Real) (w Real)) (= y y))
            )) :rule qnt_rm_unused)": false,
        }
        "Inner term is the opposite quantifier" {
            "(step t1 (cl (=
                (exists ((?v0 Int)) (forall ((?v1 Int) (?v2 Int)) (= ?v1 ?v2)))
                (forall ((?v1 Int) (?v2 Int)) (= ?v1 ?v2))
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
