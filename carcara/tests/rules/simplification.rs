#[test]
fn ite_simplify() {
    test_cases! {
        definitions = "
            (declare-fun a () Bool)
            (declare-fun b () Bool)
            (declare-fun c () Bool)
            (declare-fun d () Bool)
        ",
        "Transformation #1" {
            "(step t1 (cl (= (ite true a b) a)) :rule ite_simplify)": true,
        }
        "Transformation #2" {
            "(step t1 (cl (= (ite false a b) b)) :rule ite_simplify)": true,
        }
        "Transformation #3" {
            "(step t1 (cl (= (ite a b b) b)) :rule ite_simplify)": true,
        }
        "Transformation #4" {
            "(step t1 (cl (= (ite (not a) b c) (ite a c b))) :rule ite_simplify)": true,
        }
        "Transformation #5" {
            "(step t1 (cl (= (ite a (ite a b c) d) (ite a b d))) :rule ite_simplify)": true,
        }
        "Transformation #6" {
            "(step t1 (cl (= (ite a b (ite a c d)) (ite a b d))) :rule ite_simplify)": true,
        }
        "Transformation #7" {
            "(step t1 (cl (= (ite a true false) a)) :rule ite_simplify)": true,
        }
        "Transformation #8" {
            "(step t1 (cl (= (ite a false true) (not a))) :rule ite_simplify)": true,
        }
        "Transformation #9" {
            "(step t1 (cl (= (ite a true b) (or a b))) :rule ite_simplify)": true,
        }
        "Transformation #10" {
            "(step t1 (cl (= (ite a b false) (and a b))) :rule ite_simplify)": true,
        }
        "Transformation #11" {
            "(step t1 (cl (= (ite a false b) (and (not a) b))) :rule ite_simplify)": true,
        }
        "Transformation #12" {
            "(step t1 (cl (= (ite a b true) (or (not a) b))) :rule ite_simplify)": true,
        }
        "Multiple transformations" {
            "(step t1 (cl (= (ite (not a) false true) (not (not a)))) :rule ite_simplify)": true,
            "(step t1 (cl (= (ite a (ite a d c) d) d)) :rule ite_simplify)": true,
            "(step t1 (cl (= (ite a (ite true b c) (ite true b c)) b))
                :rule ite_simplify)": true,
        }
    }
}

#[test]
fn eq_simplify() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun a () Int)
            (declare-fun b () Int)
        ",
        "Transformation #1" {
            "(step t1 (cl (= (= a a) true)) :rule eq_simplify)": true,
            "(step t1 (cl (= (= (and p q) (and p q)) true)) :rule eq_simplify)": true,
            "(step t1 (cl (= (= a b) true)) :rule eq_simplify)": false,
        }
        "Transformation #2" {
            "(step t1 (cl (= (= 0 1) false)) :rule eq_simplify)": true,
            "(step t1 (cl (= (= 0.0 0.01) false)) :rule eq_simplify)": true,
            "(step t1 (cl (= (= 1 (- 1)) false)) :rule eq_simplify)": true,
            "(step t1 (cl (= (= 0 1) true)) :rule eq_simplify)": false,
            "(step t1 (cl (= (= 0.0 0.0) false)) :rule eq_simplify)": false,
        }
        "Transformation #3" {
            "(step t1 (cl (= (not (= 0.0 0.0)) false)) :rule eq_simplify)": true,
            "(step t1 (cl (= (not (= (- 1) (- 1))) false)) :rule eq_simplify)": true,
            "(step t1 (cl (= (not (= 0 0)) true)) :rule eq_simplify)": false,
            "(step t1 (cl (= (not (= 0 1)) false)) :rule eq_simplify)": false,
            "(step t1 (cl (= (not (= a a)) false)) :rule eq_simplify)": false,
        }
    }
}

#[test]
fn and_simplify() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun r () Bool)
        ",
        "Transformation #1" {
            "(step t1 (cl (= (and true true true) true)) :rule and_simplify)": true,
            "(step t1 (cl (= (and true true true) (and true))) :rule and_simplify)": true,
            "(step t1 (cl (= (and true) true)) :rule and_simplify)": true,

            "(step t1 (cl (= (and true p true) true)) :rule and_simplify)": false,
            "(step t1 (cl (= (and true true) false)) :rule and_simplify)": false,
        }
        "Transformation #2" {
            "(step t1 (cl (= (and p true q) (and p q))) :rule and_simplify)": true,
            "(step t1 (cl (= (and p true q r true true) (and p q r))) :rule and_simplify)": true,
            "(step t1 (cl (= (and true q true true) q)) :rule and_simplify)": true,
            "(step t1 (cl (= (and true q true true) (and q))) :rule and_simplify)": true,

            "(step t1 (cl (= (and p true q true) (and p true q))) :rule and_simplify)": false,
            "(step t1 (cl (= (and p true q r true true) (and p r))) :rule and_simplify)": false,
        }
        "Transformation #3" {
            "(step t1 (cl (= (and p p q q q r) (and p q r))) :rule and_simplify)": true,
            "(step t1 (cl (= (and p p) (and p))) :rule and_simplify)": true,
            "(step t1 (cl (= (and p p) p)) :rule and_simplify)": true,

            "(step t1 (cl (= (and p p q q q r) (and p q q r))) :rule and_simplify)": false,
            "(step t1 (cl (= (and p p q q q) (and p q r))) :rule and_simplify)": false,
        }
        "Transformation #4" {
            "(step t1 (cl (= (and p q false r) false)) :rule and_simplify)": true,
            "(step t1 (cl (= (and p q false r) (and false))) :rule and_simplify)": true,
            "(step t1 (cl (= (and false true) false)) :rule and_simplify)": true,

            "(step t1 (cl (= (and p q false r) (and p q r))) :rule and_simplify)": false,
            "(step t1 (cl (= (and p q false r) true)) :rule and_simplify)": false,
        }
        "Transformation #5" {
            "(step t1 (cl (= (and p q (not q) r) false)) :rule and_simplify)": true,
            "(step t1 (cl (= (and p q (not q) r) (and false))) :rule and_simplify)": true,
            "(step t1 (cl (= (and p (not (not q)) (not q) r) false)) :rule and_simplify)": true,
            "(step t1 (cl (= (and p (not (not (not p))) (not p)) false))
                :rule and_simplify)": true,

            "(step t1 (cl (= (and p (not (not p)) (not q) r) false)) :rule and_simplify)": false,
            "(step t1 (cl (= (and q (not r)) false)) :rule and_simplify)": false,
            "(step t1 (cl (= (and r (not r)) true)) :rule and_simplify)": false,
        }
        "Multiple transformations" {
            "(step t1 (cl (= (and p p true q q true q r) (and p q r)))
                :rule and_simplify)": true,
            "(step t1 (cl (= (and p p (not p) q q true q r) false)) :rule and_simplify)": true,
            "(step t1 (cl (= (and p false p (not p) q true q r) false))
                :rule and_simplify)": true,
        }
        "Nested \"and\" term" {
            "(step t1 (cl (= (and (and p p true q q true q r)) (and p q r)))
                :rule and_simplify)": true,
        }
    }
}

#[test]
fn or_simplify() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun r () Bool)
        ",
        "Transformation #1" {
            "(step t1 (cl (= (or false false false) false)) :rule or_simplify)": true,
            "(step t1 (cl (= (or false false false) (or false))) :rule or_simplify)": true,
            "(step t1 (cl (= (or false) false)) :rule or_simplify)": true,

            "(step t1 (cl (= (or false p false) false)) :rule or_simplify)": false,
            "(step t1 (cl (= (or false false) true)) :rule or_simplify)": false,
        }
        "Transformation #2" {
            "(step t1 (cl (= (or p false q) (or p q))) :rule or_simplify)": true,
            "(step t1 (cl (= (or p false q r false false) (or p q r))) :rule or_simplify)": true,
            "(step t1 (cl (= (or false q false false) q)) :rule or_simplify)": true,
            "(step t1 (cl (= (or false q false false) (or q))) :rule or_simplify)": true,

            "(step t1 (cl (= (or p false q false) (or p false q))) :rule or_simplify)": false,
            "(step t1 (cl (= (or p false q r false false) (or p r))) :rule or_simplify)": false,
        }
        "Transformation #3" {
            "(step t1 (cl (= (or p p q q q r) (or p q r))) :rule or_simplify)": true,
            "(step t1 (cl (= (or p p) (or p))) :rule or_simplify)": true,
            "(step t1 (cl (= (or p p) p)) :rule or_simplify)": true,

            "(step t1 (cl (= (or p p q q q r) (or p q q r))) :rule or_simplify)": false,
            "(step t1 (cl (= (or p p q q q) (or p q r))) :rule or_simplify)": false,
        }
        "Transformation #4" {
            "(step t1 (cl (= (or p q true r) true)) :rule or_simplify)": true,
            "(step t1 (cl (= (or p q true r) (or true))) :rule or_simplify)": true,
            "(step t1 (cl (= (or true false) true)) :rule or_simplify)": true,

            "(step t1 (cl (= (or p q true r) (or p q r))) :rule or_simplify)": false,
            "(step t1 (cl (= (or p q true r) false)) :rule or_simplify)": false,
        }
        "Transformation #5" {
            "(step t1 (cl (= (or p q (not q) r) true)) :rule or_simplify)": true,
            "(step t1 (cl (= (or p q (not q) r) (or true))) :rule or_simplify)": true,
            "(step t1 (cl (= (or p (not (not q)) (not q) r) true)) :rule or_simplify)": true,
            "(step t1 (cl (= (or p (not (not (not p))) (not p)) true)) :rule or_simplify)": true,

            "(step t1 (cl (= (or p (not (not p)) (not q) r) true)) :rule or_simplify)": false,
            "(step t1 (cl (= (or q (not r)) true)) :rule or_simplify)": false,
            "(step t1 (cl (= (or r (not r)) false)) :rule or_simplify)": false,
        }
        "Multiple transformations" {
            "(step t1 (cl (= (or p p false q q false q r) (or p q r))) :rule or_simplify)": true,
            "(step t1 (cl (= (or p p (not p) q q false q r) true)) :rule or_simplify)": true,
            "(step t1 (cl (= (or p true p (not p) q false q r) true)) :rule or_simplify)": true,
        }
        "Nested \"or\" term" {
            "(step t1 (cl (= (or (or p p false q q false q r)) (or p q r)))
                :rule or_simplify)": true,
        }
    }
}

#[test]
fn not_simplify() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun r () Bool)
        ",
        "Transformation #1" {
            "(step t1 (cl (= (not (not p)) p)) :rule not_simplify)": true,
            "(step t1 (cl (= (not (not (not (not p)))) p)) :rule not_simplify)": true,
            "(step t1 (cl (= (not (not (not (and p q)))) (and p q))) :rule not_simplify)": false,
        }
        "Transformation #2" {
            "(step t1 (cl (= (not false) true)) :rule not_simplify)": true,
            "(step t1 (cl (= (not false) false)) :rule not_simplify)": false,
        }
        "Transformation #3" {
            "(step t1 (cl (= (not true) false)) :rule not_simplify)": true,
            "(step t1 (cl (= (not true) true)) :rule not_simplify)": false,
        }
        "Multiple transformations" {
            "(step t1 (cl (= (not (not (not false))) true)) :rule not_simplify)": true,
            "(step t1 (cl (= (not (not (not true))) false)) :rule not_simplify)": true,
        }
    }
}

#[test]
fn implies_simplify() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun r () Bool)
        ",
        "Transformation #1" {
            "(step t1 (cl (= (=> (not p) (not q)) (=> q p))) :rule implies_simplify)": true,
            "(step t1 (cl (= (=> (not (not p)) (not (not q))) (=> p q)))
                :rule implies_simplify)": true,
            "(step t1 (cl (= (=> (not (not p)) (not (not q))) (=> (not q) (not p))))
                :rule implies_simplify)": true,
        }
        "Transformation #2" {
            "(step t1 (cl (= (=> false p) true)) :rule implies_simplify)": true,
            "(step t1 (cl (= (=> false false) true)) :rule implies_simplify)": true,
        }
        "Transformation #3" {
            "(step t1 (cl (= (=> p true) true)) :rule implies_simplify)": true,
            "(step t1 (cl (= (=> false true) true)) :rule implies_simplify)": true,
        }
        "Transformation #4" {
            "(step t1 (cl (= (=> true p) p)) :rule implies_simplify)": true,
            "(step t1 (cl (= (=> true false) false)) :rule implies_simplify)": true,
        }
        "Transformation #5" {
            "(step t1 (cl (= (=> p false) (not p))) :rule implies_simplify)": true,
            "(step t1 (cl (= (=> false false) (not false))) :rule implies_simplify)": false,
            "(step t1 (cl (= (=> true false) (not true))) :rule implies_simplify)": false,
        }
        "Transformation #6" {
            "(step t1 (cl (= (=> p p) true)) :rule implies_simplify)": true,
        }
        "Transformation #7" {
            "(step t1 (cl (= (=> (not p) p) p)) :rule implies_simplify)": true,
            "(step t1 (cl (= (=> p (not p)) (not p))) :rule implies_simplify)": true,
        }
        "Transformation #8" {
            "(step t1 (cl (= (=> (=> p q) q) (or p q))) :rule implies_simplify)": true,
            "(step t1 (cl (= (=> (=> p q) q) (or q p))) :rule implies_simplify)": false,
            "(step t1 (cl (= (=> (=> q p) q) (or p q))) :rule implies_simplify)": false,
        }
        "Multiple transformations" {
            "(step t1 (cl (= (=> (not p) (not true)) p)) :rule implies_simplify)": true,
            "(step t1 (cl (= (=> (not (not p)) (not p)) (not p))) :rule implies_simplify)": true,
            "(step t1 (cl (= (=> (not q) (not (=> p q))) (or p q)))
                :rule implies_simplify)": true,
        }
    }
}

#[test]
fn equiv_simplify() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun r () Bool)
        ",
        "Transformation #1" {
            "(step t1 (cl (= (= (not p) (not q)) (= p q))) :rule equiv_simplify)": true,
            "(step t1 (cl (= (= (not (not p)) (not q)) (= (not p) q)))
                :rule equiv_simplify)": true,
        }
        "Transformation #2" {
            "(step t1 (cl (= (= p p) true)) :rule equiv_simplify)": true,
            "(step t1 (cl (= (= (and p q) (and p q)) true)) :rule equiv_simplify)": true,
        }
        "Transformation #3" {
            "(step t1 (cl (= (= p (not p)) false)) :rule equiv_simplify)": true,
        }
        "Transformation #4" {
            "(step t1 (cl (= (= (not p) p) false)) :rule equiv_simplify)": true,
        }
        "Transformation #5" {
            "(step t1 (cl (= (= true p) p)) :rule equiv_simplify)": true,
            "(step t1 (cl (= (= true (and q p)) (and q p))) :rule equiv_simplify)": true,
        }
        "Transformation #6" {
            "(step t1 (cl (= (= p true) p)) :rule equiv_simplify)": true,
            "(step t1 (cl (= (= (and q p) true) (and q p))) :rule equiv_simplify)": true,
        }
        "Transformation #7" {
            "(step t1 (cl (= (= false p) (not p))) :rule equiv_simplify)": true,
            "(step t1 (cl (= (= false (and q p)) (not (and q p)))) :rule equiv_simplify)": true,
        }
        "Transformation #8" {
            "(step t1 (cl (= (= p false) (not p))) :rule equiv_simplify)": true,
            "(step t1 (cl (= (= (and q p) false) (not (and q p)))) :rule equiv_simplify)": true,
        }
        "Multiple transformations" {
            "(step t1 (cl (= (= (not (not p)) (not p)) false)) :rule equiv_simplify)": true,
            "(step t1 (cl (= (= (not (not false)) (not (not p))) (not p)))
                :rule equiv_simplify)": true,
        }
    }
}

#[test]
fn bool_simplify() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun r () Bool)
        ",
        "Transformation #1" {
            "(step t1 (cl (=
                (not (=> p q)) (and p (not q))
            )) :rule bool_simplify)": true,

            "(step t1 (cl (=
                (not (=> p q)) (and (not q) p)
            )) :rule bool_simplify)": false,

            "(step t1 (cl (=
                (not (=> p (not q))) (and p q)
            )) :rule bool_simplify)": false,
        }
        "Transformation #2" {
            "(step t1 (cl (=
                (not (or p q)) (and (not p) (not q))
            )) :rule bool_simplify)": true,

            "(step t1 (cl (=
                (not (or (not p) (not q))) (and p q)
            )) :rule bool_simplify)": false,
        }
        "Transformation #3" {
            "(step t1 (cl (=
                (not (and p q)) (or (not p) (not q))
            )) :rule bool_simplify)": true,

            "(step t1 (cl (=
                (not (and (not p) (not q))) (or p q)
            )) :rule bool_simplify)": false,
        }
        "Transformation #4" {
            "(step t1 (cl (=
                (=> p (=> q r)) (=> (and p q) r)
            )) :rule bool_simplify)": true,

            "(step t1 (cl (=
                (=> p (=> q r)) (=> (and q p) r)
            )) :rule bool_simplify)": false,
        }
        "Transformation #5" {
            "(step t1 (cl (=
                (=> (=> p q) q) (or p q)
            )) :rule bool_simplify)": true,

            "(step t1 (cl (=
                (=> (=> p q) r) (or p q)
            )) :rule bool_simplify)": false,
        }
        "Transformation #6" {
            "(step t1 (cl (=
                (and p (=> p q)) (and p q)
            )) :rule bool_simplify)": true,

            "(step t1 (cl (=
                (and p (=> r q)) (and p q)
            )) :rule bool_simplify)": false,
        }
        "Transformation #7" {
            "(step t1 (cl (=
                (and (=> p q) p) (and p q)
            )) :rule bool_simplify)": true,

            "(step t1 (cl (=
                (and (=> p q) r) (and p q)
            )) :rule bool_simplify)": false,
        }
        // TODO: Add tests that combine more than one transformation
    }
}

#[test]
fn qnt_simplify() {
    test_cases! {
        definitions = "",
        "Simple working examples" {
            "(step t1 (cl (= (forall ((x Int)) false) false)) :rule qnt_simplify)": true,
            "(step t1 (cl (= (forall ((x Int) (p Bool)) true) true)) :rule qnt_simplify)": true,
        }
        "Quantifier is not \"forall\"" {
            "(step t1 (cl (= (exists ((x Int)) false) false)) :rule qnt_simplify)": true,
        }
        "Inner term is not boolean constant" {
            "(step t1 (cl (= (forall ((x Int)) (not false)) true)) :rule qnt_simplify)": false,
        }
        "Left and right terms don't match" {
            "(step t1 (cl (= (forall ((x Int)) false) true)) :rule qnt_simplify)": false,
        }
    }
}

#[test]
fn div_simplify() {
    test_cases! {
        definitions = "
            (declare-fun n () Int)
            (declare-fun x () Real)
        ",
        "Transformation #1" {
            "(step t1 (cl (= (div 1 1) 1)) :rule div_simplify)": true,
            "(step t1 (cl (= (div n n) 1)) :rule div_simplify)": true,
            "(step t1 (cl (= (/ x x) 1.0)) :rule div_simplify)": true,
            "(step t1 (cl (= (/ x x) (/ x x))) :rule div_simplify)": false,
        }
        "Transformation #2" {
            "(step t1 (cl (= (div 2 1) 2)) :rule div_simplify)": true,
            "(step t1 (cl (= (div n 1) n)) :rule div_simplify)": true,
            "(step t1 (cl (= (/ x 1.0) x)) :rule div_simplify)": true,
        }
        "Transformation #3" {
            "(step t1 (cl (= (div 4 2) 2)) :rule div_simplify)": true,
            "(step t1 (cl (= (div 27 9) 3)) :rule div_simplify)": true,
            "(step t1 (cl (= (/ 1.0 2.0) 0.5)) :rule div_simplify)": true,
            "(step t1 (cl (= (/ 2.0 20.0) (/ 1.0 10.0))) :rule div_simplify)": true,
        }
        "Division by zero" {
            "(step t1 (cl (= (div 3 0) 1)) :rule div_simplify)": false,
            "(step t1 (cl (= (/ 3.0 0.0) 1.0)) :rule div_simplify)": false,
        }
        "Integer division" {
            "(step t1 (cl (= (div 8 3) 2)) :rule div_simplify)": true,
            "(step t1 (cl (= (div (- 8) 3) (- 3))) :rule div_simplify)": true,
            "(step t1 (cl (= (div 8 (- 3)) (- 2))) :rule div_simplify)": true,
            "(step t1 (cl (= (div (- 8) (- 3)) 3)) :rule div_simplify)": true,

            "(step t1 (cl (= (div (- 8) 3) (- 2))) :rule div_simplify)": false,
            "(step t1 (cl (= (div 8 (- 3)) (- 3))) :rule div_simplify)": false,
            "(step t1 (cl (= (div (- 8) (- 3)) 2)) :rule div_simplify)": false,
        }
    }
}

#[test]
fn prod_simplify() {
    test_cases! {
        definitions = "
            (declare-fun i () Int)
            (declare-fun j () Int)
            (declare-fun k () Int)
            (declare-fun x () Real)
            (declare-fun y () Real)
            (declare-fun z () Real)
        ",
        "Transformation #1" {
            "(step t1 (cl (= (* 2 3 5 7) 210)) :rule prod_simplify)": true,
            "(step t1 (cl (= 0.555 (* 1.5 3.7 0.1))) :rule prod_simplify)": true,
            "(step t1 (cl (= (* 1 1 1) 1)) :rule prod_simplify)": true,

            "(step t1 (cl (= (* 1 2 4) 6)) :rule prod_simplify)": false,
            "(step t1 (cl (= (* 1.0 2.0 1.0) 4.0)) :rule prod_simplify)": false,
        }
        "Transformation #2" {
            "(step t1 (cl (= (* 2 3 0 7) 0)) :rule prod_simplify)": true,
            "(step t1 (cl (= (* 1.5 3.7 0.0) 0.0)) :rule prod_simplify)": true,
            "(step t1 (cl (= 0 (* i 2 k 3 0 j))) :rule prod_simplify)": true,
            "(step t1 (cl (= (* i j 0 k) 0)) :rule prod_simplify)": true,
            "(step t1 (cl (= (* x y 1.0 2.0 z 0.0 z) 0.0)) :rule prod_simplify)": true,

            "(step t1 (cl (= (* 2 4 0 3) 24)) :rule prod_simplify)": false,
            "(step t1 (cl (= (* 1 1 2 3) 0)) :rule prod_simplify)": false,
            "(step t1 (cl (= (* i j 0 k) (* i j k))) :rule prod_simplify)": false,
        }
        "Transformation #3" {
            "(step t1 (cl (= (* 30 i k j) (* i 2 k 3 5 j))) :rule prod_simplify)": true,
            "(step t1 (cl (= (* i k 6 j) (* 6 i k j))) :rule prod_simplify)": true,
            "(step t1 (cl (= (* 6.0 x y z z) (* x y 1.0 2.0 z 3.0 z)))
                :rule prod_simplify)": true,
            "(step t1 (cl (= (* x y 2.0 z z) (* 2.0 x y z z))) :rule prod_simplify)": true,

            "(step t1 (cl (= (* i 2 k 3 5 j) (* 60 i k j))) :rule prod_simplify)": false,
            "(step t1 (cl (= (* i k 6 j) (* i k 6 j))) :rule prod_simplify)": false,
            "(step t1 (cl (= (* x y 1.0 2.0 z 3.0 z) (* 4.0 x y z z)))
                :rule prod_simplify)": false,
            "(step t1 (cl (= (* x y 1.0 2.0 z 3.0 z) (* x y z z))) :rule prod_simplify)": false,
        }
        "Transformation #4" {
            "(step t1 (cl (= (* i k 1 j) (* i k j))) :rule prod_simplify)": true,
            "(step t1 (cl (= (* i 1 1 k 1 j) (* i k j))) :rule prod_simplify)": true,
            "(step t1 (cl (= (* x y z z) (* x y 1.0 z z))) :rule prod_simplify)": true,
            "(step t1 (cl (= (* x y 5.0 1.0 z 0.2 z) (* x y z z))) :rule prod_simplify)": true,

            "(step t1 (cl (= (* i k 1 j) (* 1 i k j))) :rule prod_simplify)": false,
            "(step t1 (cl (= (* x y 5.0 1.0 z 0.2 z) (* 1.0 x y z z)))
                :rule prod_simplify)": false,
        }
    }
}

#[test]
fn minus_simplify() {
    test_cases! {
        definitions = "
            (declare-fun x () Real)
            (declare-fun a () Int)
            (declare-fun b () Int)
        ",
        "Transformation #1" {
            "(step t1 (cl (= (- x x) 0.0)) :rule minus_simplify)": true,
            "(step t1 (cl (= (- (+ a b) (+ a b)) 0)) :rule minus_simplify)": true,
            "(step t1 (cl (= 0 (- a a))) :rule minus_simplify)": true,
            "(step t1 (cl (= 0 (- a b))) :rule minus_simplify)": false,
        }
        "Transformation #2" {
            "(step t1 (cl (= (- 4.5 2.0) 2.5)) :rule minus_simplify)": true,
            "(step t1 (cl (= (- 5 7) (- 2))) :rule minus_simplify)": true,
            "(step t1 (cl (= 4 (- 2 3))) :rule minus_simplify)": false,
        }
        "Transformation #3" {
            "(step t1 (cl (= (- x 0.0) x)) :rule minus_simplify)": true,
            "(step t1 (cl (= (- a 0) a)) :rule minus_simplify)": true,
            "(step t1 (cl (= (- 0.0 x) x)) :rule minus_simplify)": false,
        }
        "Transformation #4" {
            "(step t1 (cl (= (- 0.0 x) (- x))) :rule minus_simplify)": true,
            "(step t1 (cl (= (- 0 a) (- a))) :rule minus_simplify)": true,
            "(step t1 (cl (= (- a) (- 0 a))) :rule minus_simplify)": true,
            "(step t1 (cl (= (- a) (- a 0))) :rule minus_simplify)": false,
        }
        "Transformation #1 from \"unary_minus_simplify\"" {
            "(step t1 (cl (= (- (- x)) x)) :rule minus_simplify)": true,
            "(step t1 (cl (= x (- (- x)))) :rule minus_simplify)": true,
            "(step t1 (cl (= (- (- (+ a b))) (+ a b))) :rule minus_simplify)": true,
        }
        "Transformation #2 from \"unary_minus_simplify\"" {
            "(step t1 (cl (= (- 5.0) (- 5.0))) :rule minus_simplify)": true,
            "(step t1 (cl (= (- 0) 0)) :rule minus_simplify)": true,
            "(step t1 (cl (= 0.0 (- 0.0))) :rule minus_simplify)": true,
        }
    }
}

#[test]
fn sum_simplify() {
    test_cases! {
        definitions = "
            (declare-fun i () Int)
            (declare-fun j () Int)
            (declare-fun k () Int)
            (declare-fun x () Real)
            (declare-fun y () Real)
            (declare-fun z () Real)
        ",
        "Transformation #1" {
            "(step t1 (cl (= (+ 1 2 3 4) 10)) :rule sum_simplify)": true,
            "(step t1 (cl (= 5.5 (+ 1.5 3.5 0.5))) :rule sum_simplify)": true,
            "(step t1 (cl (= (+ 0 0 0) 0)) :rule sum_simplify)": true,

            "(step t1 (cl (= (+ 1 2 4) 6)) :rule sum_simplify)": false,
            "(step t1 (cl (= (+ 1.0 2.0 1.0) 2.0)) :rule sum_simplify)": false,
        }
        "Transformation #2" {
            "(step t1 (cl (= (+ 10 i k j) (+ i 2 k 3 5 j))) :rule sum_simplify)": true,
            "(step t1 (cl (= (+ i k 6 j) (+ 6 i k j))) :rule sum_simplify)": true,
            "(step t1 (cl (= (+ 6.0 x y z z) (+ x y 1.0 2.0 z 3.0 z)))
                :rule sum_simplify)": true,
            "(step t1 (cl (= (+ x y 2.0 z z) (+ 2.0 x y z z))) :rule sum_simplify)": true,

            "(step t1 (cl (= (+ i 2 k 3 5 j) (+ 20 i k j))) :rule sum_simplify)": false,
            "(step t1 (cl (= (+ i k 6 j) (+ i k 6 j))) :rule sum_simplify)": false,
            "(step t1 (cl (= (+ x y 1.0 2.0 z 3.0 z) (+ 4.0 x y z z)))
                :rule sum_simplify)": false,
            "(step t1 (cl (= (+ x y 1.0 2.0 z 3.0 z) (+ x y z z))) :rule sum_simplify)": false,
        }
        "Transformation #3" {
            "(step t1 (cl (= (+ i k 0 j) (+ i k j))) :rule sum_simplify)": true,
            "(step t1 (cl (= (+ i 0 0 k 0 j) (+ i k j))) :rule sum_simplify)": true,
            "(step t1 (cl (= (+ x y z z) (+ x y 0.0 z z))) :rule sum_simplify)": true,
            "(step t1 (cl (= (+ x y 0.0 0.0 z z) (+ x y z z))) :rule sum_simplify)": true,

            "(step t1 (cl (= (+ i k 0 j) (+ 0 i k j))) :rule sum_simplify)": false,
            "(step t1 (cl (= (+ x y 0.0 0.0 z z) (+ 0.0 x y z z))) :rule sum_simplify)": false,
        }
    }
}

#[test]
fn comp_simplify() {
    test_cases! {
        definitions = "
            (declare-fun a () Int)
            (declare-fun b () Int)
        ",
        "Transformation #1" {
            "(step t1 (cl (= (< 1 2) true)) :rule comp_simplify)": true,
            "(step t1 (cl (= (< 1.0 1.0) false)) :rule comp_simplify)": true,
            "(step t1 (cl (= (< 0.0 (- 1.0)) true)) :rule comp_simplify)": false,
        }
        "Transformation #2" {
            "(step t1 (cl (= (< a a) false)) :rule comp_simplify)": true,
            "(step t1 (cl (= (< (+ 1 2) (+ 1 2)) true)) :rule comp_simplify)": false,
        }
        "Transformation #3" {
            "(step t1 (cl (= (<= 1 2) true)) :rule comp_simplify)": true,
            "(step t1 (cl (= (<= 1.0 1.0) true)) :rule comp_simplify)": true,
            "(step t1 (cl (= (<= 0.0 (- 1.0)) true)) :rule comp_simplify)": false,
        }
        "Transformation #4" {
            "(step t1 (cl (= (<= a a) true)) :rule comp_simplify)": true,
            "(step t1 (cl (= (<= (+ 1 2) (+ 1 2)) false)) :rule comp_simplify)": false,
        }
        "Transformation #5" {
            "(step t1 (cl (= (>= a b) (<= b a))) :rule comp_simplify)": true,
            "(step t1 (cl (= (>= 1 a) (<= 1 a))) :rule comp_simplify)": false,
        }
        "Transformation #6" {
            "(step t1 (cl (= (< a b) (not (<= b a)))) :rule comp_simplify)": true,
            "(step t1 (cl (= (< a b) (> b a))) :rule comp_simplify)": false,
        }
        "Transformation #7" {
            "(step t1 (cl (= (> a b) (not (<= a b)))) :rule comp_simplify)": true,
            "(step t1 (cl (= (> a b) (not (>= b a)))) :rule comp_simplify)": false,
            "(step t1 (cl (= (> a b) (< b a))) :rule comp_simplify)": false,
        }
        "Multiple transformations" {
            "(step t1 (cl (= (>= a a) true)) :rule comp_simplify)": true,
            "(step t1 (cl (= (>= 5.0 8.0) false)) :rule comp_simplify)": true,
        }
    }
}

#[test]
fn ac_simp() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun r () Bool)
            (declare-fun s () Bool)
        ",
        "Simple working examples" {
            "(step t1 (cl (= (and (and p q) (and r s)) (and p q r s))) :rule ac_simp)": true,
            "(step t1 (cl (= (or (or (or p q) r) s) (or p q r s))) :rule ac_simp)": true,
        }
        "Mixed operators" {
            "(step t1 (cl (= (or (and (and p q) r) s (or p q)) (or (and p q r) s p q)))
                :rule ac_simp)": true,

            "(step t1 (cl (= (or (= (and (and p q) r) s) (or p q)) (or (= (and p q r) s) p q)))
                :rule ac_simp)": true,

            "(step t1 (cl (= (or (= (and (and p q) r) s) (or p q))
                (or (= (and (and p q) r) s) p q))) :rule ac_simp)": false,

            "(step t1 (cl (= (xor (xor (xor p q) r) s) (xor p q r s))) :rule ac_simp)": false,

            "(step t1 (cl (= (forall ((p Bool) (q Bool)) (and (and p q) p))
                (forall ((p Bool) (q Bool)) (and p q)))) :rule ac_simp)": true,
        }
        "Removing duplicates" {
            "(step t1 (cl (= (or p p q r s) (or p q r s))) :rule ac_simp)": true,
            "(step t1 (cl (= (and (and p q) (and q r)) (and p q r))) :rule ac_simp)": true,
            "(step t1 (cl (= (and (and p q) (and q r)) (and p q q r))) :rule ac_simp)": false,
        }
    }
}
