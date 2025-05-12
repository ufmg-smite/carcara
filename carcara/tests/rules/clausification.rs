#[test]
fn distinct_elim() {
    test_cases! {
        definitions = "
            (declare-sort T 0)
            (declare-fun a () T)
            (declare-fun b () T)
            (declare-fun c () T)
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun r () Bool)
        ",
        "Simple working examples" {
            "(step t1 (cl (= (distinct a b) (not (= a b)))) :rule distinct_elim)": true,

            "(step t1 (cl (= (distinct a b c) (and
                (not (= a b))
                (not (= a c))
                (not (= b c))
            ))) :rule distinct_elim)": true,
        }
        "Inequality terms in different orders" {
            "(step t1 (cl (= (distinct a b) (not (= b a)))) :rule distinct_elim)": true,

            "(step t1 (cl (= (distinct a b c) (and
                (not (= b a))
                (not (= a c))
                (not (= c b))
            ))) :rule distinct_elim)": true,
        }
        "Conjunction terms in wrong order" {
            "(step t1 (cl (= (distinct a b c) (and
                (not (= b c))
                (not (= a b))
                (not (= a c))
            ))) :rule distinct_elim)": false,
        }
        "\"distinct\" on more than two booleans should be \"false\"" {
            "(step t1 (cl (= (distinct p q r) false)) :rule distinct_elim)": true,

            "(step t1 (cl (= (distinct p q r) (and
                (not (= p q))
                (not (= p r))
                (not (= q r))
            ))) :rule distinct_elim)": false,
        }
    }
}

#[test]
fn and() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun r () Bool)
            (declare-fun s () Bool)
        ",
        "Simple working examples" {
            "(assume h1 (and p q))
            (step t2 (cl q) :rule and :premises (h1) :args (1))": true,

            "(assume h1 (and p q r s))
            (step t2 (cl p) :rule and :premises (h1) :args (0))": true,

            "(assume h1 (and p q r s))
            (step t2 (cl s) :rule and :premises (h1) :args (3))": true,
        }
        "Number of premises != 1" {
            "(step t1 (cl p) :rule and)": false,

            "(assume h1 (and p q))
            (assume h2 (and r s))
            (step t2 (cl r) :rule and :premises (h1 h2))": false,
        }
        "Premise clause has more than one term" {
            "(step t1 (cl (and p q) (and r s)) :rule hole)
            (step t2 (cl p) :rule and :premises (t1) :args (0))": false,
        }
        "Conclusion clause does not have exactly one term" {
            "(assume h1 (and p q r s))
            (step t2 (cl q s) :rule and :premises (h1) :args (1))": false,

            "(assume h1 (and p q))
            (step t2 (cl) :rule and :premises (h1) :args (0))": false,
        }
        "Premise is not an \"and\" operation" {
            "(assume h1 (or p q r s))
            (step t2 (cl r) :rule and :premises (h1) :args (0))": false,
        }
        "Conclusion term is not in premise" {
            "(assume h1 (and p q r))
            (step t2 (cl s) :rule and :premises (h1) :args (0))": false,
        }
    }
}

#[test]
fn not_or() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun r () Bool)
            (declare-fun s () Bool)
        ",
        "Simple working examples" {
            "(assume h1 (not (or p q)))
            (step t2 (cl (not q)) :rule not_or :premises (h1) :args (1))": true,

            "(assume h1 (not (or p q r s)))
            (step t2 (cl (not p)) :rule not_or :premises (h1) :args (0))": true,
        }
        "Conclusion clause is of the wrong form" {
            "(assume h1 (not (or p q r s)))
            (step t2 (cl (not q) (not s)) :rule not_or :premises (h1) :args (1))": false,

            "(assume h1 (not (or p q)))
            (step t2 (cl q) :rule not_or :premises (h1) :args (1))": false,
        }
        "Premise is of the wrong form" {
            "(assume h1 (not (and p q r s)))
            (step t2 (cl (not r)) :rule not_or :premises (h1) :args (2))": false,

            "(assume h1 (or p q r s))
            (step t2 (cl (not r)) :rule not_or :premises (h1) :args (2))": false,
        }
        "Conclusion term is not in premise" {
            "(assume h1 (not (or p q r)))
            (step t2 (cl (not s)) :rule not_or :premises (h1) :args (0))": false,
        }
    }
}

#[test]
fn or() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun r () Bool)
            (declare-fun s () Bool)
        ",
        "Simple working examples" {
            "(assume h1 (or p q))
            (step t2 (cl p q) :rule or :premises (h1))": true,

            "(assume h1 (or p q r s))
            (step t2 (cl p q r s) :rule or :premises (h1))": true,
        }
        "Number of premises != 1" {
            "(step t1 (cl p q r) :rule or)": false,

            "(assume h1 (or p q))
            (assume h2 (or q r))
            (step t3 (cl p q r) :rule or :premises (h1 h2))": false,
        }
        "Premise clause has more than one term" {
            "(assume h1 (or p (or q r)))
            (step t2 (cl p (or q r)) :rule or :premises (h1))
            (step t3 (cl p q) :rule or :premises (t2))": false,
        }
        "Premise is not an \"or\" operation" {
            "(assume h1 (and p q))
            (step t2 (cl p q) :rule or :premises (h1))": false,
        }
        "Premise and clause contents are different" {
            "(assume h1 (or p q))
            (step t2 (cl r s) :rule or :premises (h1))": false,

            "(assume h1 (or p q r))
            (step t2 (cl p q) :rule or :premises (h1))": false,

            "(assume h1 (or q p))
            (step t2 (cl p q) :rule or :premises (h1))": false,
        }
    }
}

#[test]
fn not_and() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun r () Bool)
            (declare-fun s () Bool)
        ",
        "Simple working examples" {
            "(assume h1 (not (and p q)))
            (step t2 (cl (not p) (not q)) :rule not_and :premises (h1))": true,

            "(assume h1 (not (and p q r s)))
            (step t2 (cl (not p) (not q) (not r) (not s)) :rule not_and :premises (h1))": true,
        }
        "Premise is of the wrong form" {
            "(assume h1 (and p q))
            (step t2 (cl (not p) (not q)) :rule not_and :premises (h1))": false,

            "(assume h1 (not (or p q)))
            (step t2 (cl (not p) (not q)) :rule not_and :premises (h1))": false,
        }
        "Premise and clause contents are different" {
            "(assume h1 (not (and p q)))
            (step t2 (cl (not r) (not s)) :rule not_and :premises (h1))": false,

            "(assume h1 (not (and p q r)))
            (step t2 (cl (not p) (not q)) :rule not_and :premises (h1))": false,

            "(assume h1 (not (and q p)))
            (step t2 (cl (not p) (not q)) :rule not_and :premises (h1))": false,
        }
    }
}

#[test]
fn xor1() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
        ",
        "Simple working examples" {
            "(assume h1 (xor p q))
            (step t2 (cl p q) :rule xor1 :premises (h1))": true,
        }
        "Premise is of the wrong form" {
            "(assume h1 (and p q))
            (step t2 (cl p q) :rule xor1 :premises (h1))": false,
        }
        "Conclusion is of the wrong form" {
            "(assume h1 (xor p q))
            (step t2 (cl q p) :rule xor1 :premises (h1))": false,

            "(assume h1 (xor p q))
            (step t2 (cl (not p) (not q)) :rule xor1 :premises (h1))": false,
        }
    }
}

#[test]
fn xor2() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
        ",
        "Simple working examples" {
            "(assume h1 (xor p q))
            (step t2 (cl (not p) (not q)) :rule xor2 :premises (h1))": true,

            "(assume h1 (xor (not p) (not q)))
            (step t2 (cl (not (not p)) (not (not q))) :rule xor2 :premises (h1))": true,
        }
        "Premise is of the wrong form" {
            "(assume h1 (and p q))
            (step t2 (cl (not p) (not q)) :rule xor2 :premises (h1))": false,
        }
        "Conclusion is of the wrong form" {
            "(assume h1 (xor p q))
            (step t2 (cl (not q) (not p)) :rule xor2 :premises (h1))": false,

            "(assume h1 (xor (not p) (not q)))
            (step t2 (cl p q) :rule xor2 :premises (h1))": false,
        }
    }
}

#[test]
fn not_xor1() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
        ",
        "Simple working examples" {
            "(assume h1 (not (xor p q)))
            (step t2 (cl p (not q)) :rule not_xor1 :premises (h1))": true,

            "(assume h1 (not (xor p (not q))))
            (step t2 (cl p (not (not q))) :rule not_xor1 :premises (h1))": true,
        }
        "Premise is of the wrong form" {
            "(assume h1 (xor p q))
            (step t2 (cl p (not q)) :rule not_xor1 :premises (h1))": false,
        }
        "Conclusion is of the wrong form" {
            "(assume h1 (not (xor p q)))
            (step t2 (cl (not q) p) :rule not_xor1 :premises (h1))": false,

            "(assume h1 (not (xor p q)))
            (step t2 (cl (not p) q) :rule not_xor1 :premises (h1))": false,

            "(assume h1 (not (xor p (not q))))
            (step t2 (cl p q) :rule not_xor1 :premises (h1))": false,
        }
    }
}

#[test]
fn not_xor2() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
        ",
        "Simple working examples" {
            "(assume h1 (not (xor p q)))
            (step t2 (cl (not p) q) :rule not_xor2 :premises (h1))": true,

            "(assume h1 (not (xor (not p) q)))
            (step t2 (cl (not (not p)) q) :rule not_xor2 :premises (h1))": true,
        }
        "Premise is of the wrong form" {
            "(assume h1 (xor p q))
            (step t2 (cl (not p) q) :rule not_xor2 :premises (h1))": false,
        }
        "Conclusion is of the wrong form" {
            "(assume h1 (not (xor p q)))
            (step t2 (cl p (not q)) :rule not_xor2 :premises (h1))": false,

            "(assume h1 (not (xor p q)))
            (step t2 (cl (not q) p) :rule not_xor2 :premises (h1))": false,

            "(assume h1 (not (xor (not p) q)))
            (step t2 (cl p q) :rule not_xor2 :premises (h1))": false,
        }
    }
}

#[test]
fn implies() {
    test_cases! {
        definitions = "
            (declare-fun a () Bool)
            (declare-fun b () Bool)
        ",
        "Simple working examples" {
            "(assume h1 (=> a b))
            (step t2 (cl (not a) b) :rule implies :premises (h1))": true,

            "(assume h1 (=> (not a) b))
            (step t2 (cl (not (not a)) b) :rule implies :premises (h1))": true,
        }
        "Premise term is not an \"implies\" term" {
            "(assume h1 (= a b))
            (step t2 (cl (not a) b) :rule implies :premises (h1))": false,
        }
        "Conclusion clause is of the wrong form" {
            "(assume h1 (=> a b))
            (step t2 (cl b (not a)) :rule implies :premises (h1))": false,

            "(assume h1 (=> a b))
            (step t2 (cl a (not b)) :rule implies :premises (h1))": false,

            "(assume h1 (=> (not a) b))
            (step t2 (cl a b) :rule implies :premises (h1))": false,
        }
    }
}

#[test]
fn not_implies1() {
    test_cases! {
        definitions = "
            (declare-fun a () Bool)
            (declare-fun b () Bool)
        ",
        "Simple working examples" {
            "(assume h1 (not (=> a b)))
            (step t2 (cl a) :rule not_implies1 :premises (h1))": true,

            "(assume h1 (not (=> (not a) b)))
            (step t2 (cl (not a)) :rule not_implies1 :premises (h1))": true,
        }
        "Premise term is of the wrong form" {
            "(assume h1 (=> a b))
            (step t2 (cl a) :rule not_implies1 :premises (h1))": false,

            "(assume h1 (not (= a b)))
            (step t2 (cl a) :rule not_implies1 :premises (h1))": false,
        }
        "Conclusion clause is of the wrong form" {
            "(assume h1 (not (=> a b)))
            (step t2 (cl (not a)) :rule not_implies1 :premises (h1))": false,

            "(assume h1 (not (=> a b)))
            (step t2 (cl b) :rule not_implies1 :premises (h1))": false,
        }
    }
}

#[test]
fn not_implies2() {
    test_cases! {
        definitions = "
            (declare-fun a () Bool)
            (declare-fun b () Bool)
        ",
        "Simple working examples" {
            "(assume h1 (not (=> a b)))
            (step t2 (cl (not b)) :rule not_implies2 :premises (h1))": true,

            "(assume h1 (not (=> a (not b))))
            (step t2 (cl (not (not b))) :rule not_implies2 :premises (h1))": true,
        }
        "Premise term is of the wrong form" {
            "(assume h1 (=> a b))
            (step t2 (cl (not b)) :rule not_implies2 :premises (h1))": false,

            "(assume h1 (not (= a b)))
            (step t2 (cl (not b)) :rule not_implies2 :premises (h1))": false,
        }
        "Conclusion clause is of the wrong form" {
            "(assume h1 (not (=> a b)))
            (step t2 (cl b) :rule not_implies2 :premises (h1))": false,

            "(assume h1 (not (=> a b)))
            (step t2 (cl (not a)) :rule not_implies2 :premises (h1))": false,
        }
    }
}

#[test]
fn nary_elim() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun r () Bool)
            (declare-fun s () Bool)
            (declare-fun a () Int)
            (declare-fun b () Int)
            (declare-fun c () Int)
            (declare-fun d () Int)
        ",
        "Chainable operators" {
            "(step t1 (cl (= (= a b c d) (and (= a b) (= b c) (= c d)))) :rule nary_elim)": true,
            "(step t1 (cl (= (= a b) (and (= a b)))) :rule nary_elim)": true,
            "(step t1 (cl (= (= a b c) (and (= b c) (= a b)))) :rule nary_elim)": false,
            "(step t1 (cl (= (= a b c d) (and (= a b) (= c d)))) :rule nary_elim)": false,
        }
        "Left associative operators" {
            "(step t1 (cl (= (+ a b c d) (+ (+ (+ a b) c) d))) :rule nary_elim)": true,
            "(step t1 (cl (= (* a b) (* a b))) :rule nary_elim)": true,
            "(step t1 (cl (= (- a b c d) (- a (- b (- c d))))) :rule nary_elim)": false,
            "(step t1 (cl (= (+ a b c d) (+ (+ (+ d c) b) a))) :rule nary_elim)": false,
        }
        "Right associative operators" {
            "(step t1 (cl (= (=> p q r s) (=> p (=> q (=> r s))))) :rule nary_elim)": true,
            "(step t1 (cl (= (=> p q) (=> p q))) :rule nary_elim)": true,
            "(step t1 (cl (= (=> p q r s) (=> (=> (=> p q) r) s))) :rule nary_elim)": false,
        }
        "Clause term is not of the correct form" {
            "(step t1 (cl (= (or p q r s) (or (or (or p q) r) s))) :rule nary_elim)": false,
            "(step t1 (cl (= (- a) (- a))) :rule nary_elim)": false,
            "(step t1 (cl (= (=> p (=> q (=> r s))) (=> p q r s))) :rule nary_elim)": false,
        }
    }
}

#[test]
fn bfun_elim() {
    test_cases! {
        definitions = "
            (declare-fun f (Bool) Bool)
            (declare-fun g (Bool Bool Bool) Bool)
            (declare-fun h (Int Bool Real) Bool)
            (declare-fun a () Bool)
            (declare-fun b () Bool)
            (declare-fun c () Bool)
        ",
        "First step" {
            "(assume h1 (forall ((x Bool)) (f x)))
            (step t1 (cl (and (f false) (f true))) :rule bfun_elim :premises (h1))": true,

            "(assume h1 (exists ((x Int) (y Bool)) (f y)))
            (step t1 (cl (exists ((x Int)) (or (f false) (f true))))
                :rule bfun_elim :premises (h1))": true,

            "(assume h1 (exists ((x Bool) (y Bool) (z Bool)) (g x y z)))
            (step t1 (cl (or
                (g false false false)
                (g true false false)
                (g false true false)
                (g true true false)
                (g false false true)
                (g true false true)
                (g false true true)
                (g true true true)
            )) :rule bfun_elim :premises (h1))": true,
        }
        "Second step" {
            "(assume h1 (f a))
            (step t1 (cl (ite a (f true) (f false))) :rule bfun_elim :premises (h1))": true,

            "(assume h1 (h 1 a 0.0))
            (step t1 (cl (ite a (h 1 true 0.0) (h 1 false 0.0)))
                :rule bfun_elim :premises (h1))": true,

            "(assume h1 (g a b c))
            (step t1 (cl (ite a
                (ite b
                    (ite c (g true true true) (g true true false))
                    (ite c (g true false true) (g true false false)))
                (ite b
                    (ite c (g false true true) (g false true false))
                    (ite c (g false false true) (g false false false)))
            )) :rule bfun_elim :premises (h1))": true,
        }
        "Both steps" {
            "(assume h1 (exists ((x Bool)) (and x (f a))))
            (step t1 (cl (or
                (and false (ite a (f true) (f false)))
                (and true (ite a (f true) (f false)))
            )) :rule bfun_elim :premises (h1))": true,

            "(assume h1 (forall ((x Bool) (y Bool)) (g x a y)))
            (step t1 (cl (and
                (ite a (g false true false) (g false false false))
                (ite a (g true true false) (g true false false))
                (ite a (g false true true) (g false false true))
                (ite a (g true true true) (g true false true))
            )) :rule bfun_elim :premises (h1))": true,
        }
    }
}
