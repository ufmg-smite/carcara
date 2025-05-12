#[test]
fn eq_congruent() {
    test_cases! {
        definitions = "
            (declare-fun a () Int)
            (declare-fun b () Int)
            (declare-fun c () Int)
            (declare-fun x () Int)
            (declare-fun y () Int)
            (declare-fun z () Int)
            (declare-fun f (Int Int) Int)
            (declare-fun g (Int Int) Int)
            (declare-fun f-1 (Int) Int)
            (declare-fun f-3 (Int Int Int) Int)
        ",
        "Simple working examples" {
            "(step t1 (cl (not (= a b)) (= (f-1 a) (f-1 b))) :rule eq_congruent)": true,

            "(step t1 (cl (not (= a x)) (not (= b y)) (not (= c z))
                      (= (f-3 a b c) (f-3 x y z))) :rule eq_congruent)": true,

            "(step t1 (cl (not (= a x)) (not (= b y)) (not (= c z))
                      (= (* a b c) (* x y z))) :rule eq_congruent)": true,
        }
        "t_i and u_i are possibly flipped" {
            "(step t1 (cl (not (= b a)) (= (f-1 a) (f-1 b))) :rule eq_congruent)": true,

            "(step t1 (cl (not (= x a)) (not (= b y)) (not (= z c))
                      (= (f-3 a b c) (f-3 x y z))) :rule eq_congruent)": true,

            "(step t1 (cl (not (= a x)) (not (= b y)) (= (f x y) (f a b)))
                :rule eq_congruent)": true,
        }
        "Clause term is not an inequality" {
            "(step t1 (cl (not (= a x)) (= b y) (= (f a b) (f x y))) :rule eq_congruent)": false,
        }
        "Final term is not an equality of applications" {
            "(step t1 (cl (not (= a x)) (not (= b y)) (= (+ a b) (f x y)))
                :rule eq_congruent)": false,
        }
        "Functions are not the same" {
            "(step t1 (cl (not (= a x)) (not (= b y)) (= (f a b) (g x y)))
                :rule eq_congruent)": false,

            "(step t1 (cl (not (= a x)) (not (= b y)) (not (= c z))
                      (= (* a b c) (+ x y z))) :rule eq_congruent)": false,
        }
        "Number of function arguments is not the same as the number of inequalities" {
            "(step t1 (cl (not (= a x)) (not (= b y)) (= (f-3 a b c) (f-3 x y z)))
                :rule eq_congruent)": false,

            "(step t1 (cl (not (= a x)) (not (= b y)) (= (+ a b) (+ x y z)))
                :rule eq_congruent)": false,
        }
        "Terms don't match" {
            "(step t1 (cl (not (= a x)) (not (= b y)) (= (f b a) (f x y)))
                :rule eq_congruent)": false,

            "(step t1 (cl (not (= a x)) (not (= b y)) (= (f a b) (f c z)))
                :rule eq_congruent)": false,
        }
    }
}

#[test]
fn eq_congruent_pred() {
    test_cases! {
        definitions = "
            (declare-fun a () Bool)
            (declare-fun b () Bool)
            (declare-fun c () Bool)
            (declare-fun x () Bool)
            (declare-fun y () Bool)
            (declare-fun z () Bool)
            (declare-fun p (Bool Bool) Bool)
            (declare-fun q (Bool Bool) Bool)
            (declare-fun p-1 (Bool) Bool)
            (declare-fun p-3 (Bool Bool Bool) Bool)
        ",
        "Simple working examples" {
            "(step t1 (cl (not (= a b)) (not (p-1 a)) (p-1 b)) :rule eq_congruent_pred)": true,

            "(step t1 (cl (not (= a x)) (not (= b y)) (not (= c z))
                      (not (p-3 a b c)) (p-3 x y z)) :rule eq_congruent_pred)": true,

            "(step t1 (cl (not (= a x)) (not (= b y)) (not (= c z))
                      (not (and a b c)) (and x y z)) :rule eq_congruent_pred)": true,
        }
        "t_i and u_i are possibly flipped" {
            "(step t1 (cl (not (= b a)) (not (p-1 a)) (p-1 b)) :rule eq_congruent_pred)": true,

            "(step t1 (cl (not (= x a)) (not (= b y)) (not (= z c))
                      (not (p-3 a b c)) (p-3 x y z)) :rule eq_congruent_pred)": true,

            "(step t1 (cl (not (= a x)) (not (= b y)) (not (p x y)) (p a b))
                :rule eq_congruent_pred)": true,
        }
        "Clause term is not an inequality" {
            "(step t1 (cl (not (= a x)) (= b y) (not (p a b)) (p x y))
                :rule eq_congruent_pred)": false,
        }
        "Final two terms' order may be flipped" {
            "(step t1 (cl (not (= a x)) (not (= b y)) (p a b) (not (p x y)))
                :rule eq_congruent_pred)": true,
        }
        "Functions are not the same" {
            "(step t1 (cl (not (= a x)) (not (= b y)) (not (p a b)) (q x y))
                :rule eq_congruent_pred)": false,

            "(step t1 (cl (not (= a x)) (not (= b y)) (not (= c z))
                      (not (or a b c)) (and x y z)) :rule eq_congruent_pred)": false,
        }
        "Number of function arguments is not the same as the number of inequalities" {
            "(step t1 (cl (not (= a x)) (not (= b y)) (not (p-3 a b c)) (p-3 x y z))
                :rule eq_congruent_pred)": false,

            "(step t1 (cl (not (= a x)) (not (= b y)) (not (and a b)) (and x y z))
                :rule eq_congruent_pred)": false,
        }
        "Terms don't match" {
            "(step t1 (cl (not (= a x)) (not (= b y)) (not (p b a)) (p x y))
                :rule eq_congruent_pred)": false,

            "(step t1 (cl (not (= a x)) (not (= b y)) (not (p a b)) (p c z))
                :rule eq_congruent_pred)": false,
        }
    }
}

#[test]
fn cong() {
    test_cases! {
        definitions = "
            (declare-sort T 0)
            (declare-fun a () T)
            (declare-fun b () T)
            (declare-fun c () T)
            (declare-fun d () T)
            (declare-fun f (T Bool T) T)
            (declare-fun g (T Bool T) T)
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun r () Bool)
            (declare-fun s () Bool)
            (declare-fun x () Real)
            (declare-fun y () Real)
        ",
        "Simple working examples" {
            "(assume h1 (= a b))
            (assume h2 (= c d))
            (step t3 (cl (= (f b false c) (f a false d))) :rule cong :premises (h1 h2))": true,

            "(assume h1 (= p q))
            (assume h2 (= r s))
            (step t3 (cl (= (and p false s) (and q false r)))
                :rule cong :premises (h1 h2))": true,
        }
        "Functions or operators don't match" {
            "(assume h1 (= a b))
            (assume h2 (= c d))
            (step t3 (cl (= (f b false c) (g a false d))) :rule cong :premises (h1 h2))": false,

            "(assume h1 (= p q))
            (assume h2 (= r s))
            (step t3 (cl (= (and p false s) (or q false r)))
                :rule cong :premises (h1 h2))": false,
        }
        "No premises were given" {
            "(step t1 (cl (= (f a true c) (f a true c))) :rule cong)": false,
        }
        "Wrong number of premises" {
            "(assume h1 (= a b))
            (assume h2 (= p q))
            (step t3 (cl (= (f a p c) (f b q d))) :rule cong :premises (h1 h2))": false,

            "(assume h1 (= a b))
            (assume h2 (= p q))
            (assume h3 (= c d))
            (assume h4 (= r s))
            (step t5 (cl (= (f a p c) (f b q d))) :rule cong :premises (h1 h2 h3 h4))": false,
        }
        "Premise doesn't match expected terms" {
            "(assume h1 (= a b))
            (assume h2 (= r s))
            (assume h3 (= c d))
            (step t4 (cl (= (f a p c) (f b q d))) :rule cong :premises (h1 h2 h3))": false,

            "(assume h1 (= a b))
            (assume h2 (= c d))
            (assume h3 (= p q))
            (step t4 (cl (= (f a p c) (f b q d))) :rule cong :premises (h1 h2 h3))": false,
        }
        "Should prefer consuming premise than relying on reflexivity" {
            "(assume h1 (= false false))
            (assume h2 (= r s))
            (step t3 (cl (= (and false false s) (and false false r)))
                :rule cong :premises (h1 h2))": true,

            "(assume h1 (= (- 1.0) (- 1.0)))
            (step t2 (cl (= (< x (- 1.0)) (< x (- 1.0)))) :rule cong :premises (h1))": true,
        }
        "Argument order may be flipped if operator is \"=\"" {
            "(assume h1 (= x y))
            (step t2 (cl (= (= 0.0 x) (= y 0.0))) :rule cong :premises (h1))": true,

            "(assume h1 (= x y))
            (step t2 (cl (= (= x 0.0) (= 0.0 y))) :rule cong :premises (h1))": true,

            "(assume h1 (= a b)) (assume h2 (= c d))
            (step t3 (cl (= (= c a) (= b d))) :rule cong :premises (h1 h2))": true,

            "(assume h1 (= a b)) (assume h2 (= c d))
            (step t3 (cl (= (= a c) (= d b))) :rule cong :premises (h1 h2))": true,

            "(assume h1 (= a b)) (assume h2 (= c d))
            (step t3 (cl (= (= c a) (= d b))) :rule cong :premises (h1 h2))": true,
        }
    }
}

#[test]
fn ho_cong() {
    test_cases! {
        definitions = "
            (declare-sort T 0)
            (declare-fun a () T)
            (declare-fun b () T)
            (declare-fun f (T Int) T)
            (declare-fun g (T Int) T)
            (declare-fun p () Bool)
            (declare-fun q () Bool)
        ",
        "Simple working examples" {
            "(assume h1 (= f g))
            (assume h2 (= a b))
            (step t3 (cl (= (f a 0) (g b 0))) :rule ho_cong :premises (h1 h2))": true,

            "(assume h1 (= f (lambda ((a T) (x Int)) a)))
            (assume h2 (= 0 1))
            (step t3 (cl (= (f b 0) ((lambda ((a T) (x Int)) a) b 1)))
                :rule ho_cong :premises (h1 h2))": true,
        }
        "Can't be used with operators" {
            "(assume h1 (= p q))
            (step t3 (cl (= (and p true) (and q true))) :rule ho_cong :premises (h1))": false,
        }
    }
}
