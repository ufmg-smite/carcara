#[test]
fn eq_transitive() {
    test_cases! {
        definitions = "
            (declare-sort T 0)
            (declare-fun a () T)
            (declare-fun b () T)
            (declare-fun c () T)
            (declare-fun d () T)
            (declare-fun e () T)
        ",
        "Simple working examples" {
            "(step t1 (cl (not (= a b)) (not (= b c)) (= a c)) :rule eq_transitive)": true,

            "(step t1 (cl (not (= a b)) (not (= b c)) (not (= c d)) (= a d))
                :rule eq_transitive)": true,

            "(step t1 (cl (not (= a a)) (not (= a a)) (= a a)) :rule eq_transitive)": true,
        }
        "Inequality terms in different orders" {
            "(step t1 (cl (not (= a b)) (not (= c b)) (not (= c d)) (= d a))
                :rule eq_transitive)": true,

            "(step t1 (cl (not (= b a)) (not (= c b)) (not (= d c)) (= a d))
                :rule eq_transitive)": true,
        }
        "Clause term is not an inequality" {
            "(step t1 (cl (= a b) (not (= b c)) (= a c)) :rule eq_transitive)": false,

            "(step t1 (cl (not (= a b)) (= b c) (= a c)) :rule eq_transitive)": false,
        }
        "Final term is not an equality" {
            "(step t1 (cl (not (= a b)) (not (= b c)) (not (= a c)))
                :rule eq_transitive)": false,
        }
        "Clause is too small" {
            "(step t1 (cl (not (= a b)) (= a b)) :rule eq_transitive)": false,
        }
        "Clause terms in different orders" {
            "(step t1 (cl (not (= a b)) (not (= c d)) (not (= b c)) (= a d))
                :rule eq_transitive)": true,

            "(step t1 (cl (not (= c d)) (not (= b c)) (not (= a b)) (= a d))
                :rule eq_transitive)": true,
        }
        "Clause doesn't form transitive chain" {
            "(step t1 (cl (not (= a b)) (not (= c d)) (= a d)) :rule eq_transitive)": false,

            "(step t1 (cl (not (= a b)) (not (= b b)) (not (= c d)) (= a d))
                :rule eq_transitive)": false,

            "(step t1 (cl (not (= a b)) (not (= b c)) (not (= c d)) (= a e))
                :rule eq_transitive)": false,

            "(step t1 (cl (not (= a b)) (not (= b e)) (not (= b c)) (= a c))
                :rule eq_transitive)": false,
        }
    }
}

#[test]
fn trans() {
    test_cases! {
        definitions = "
            (declare-sort T 0)
            (declare-fun a () T)
            (declare-fun b () T)
            (declare-fun c () T)
            (declare-fun d () T)
            (declare-fun e () T)
        ",
        "Simple working examples" {
            "(assume h1 (= a b)) (assume h2 (= b c))
            (step t3 (cl (= a c)) :rule trans :premises (h1 h2))": true,

            "(assume h1 (= a b)) (assume h2 (= b c)) (assume h3 (= c d))
            (step t4 (cl (= a d)) :rule trans :premises (h1 h2 h3))": true,

            "(assume h1 (= a a))
            (step t2 (cl (= a a)) :rule trans :premises (h1))": true,
        }
        "Premises in different orders" {
            "(assume h1 (= a b)) (assume h2 (= c d)) (assume h3 (= b c))
            (step t4 (cl (= a d)) :rule trans :premises (h1 h2 h3))": true,

            "(assume h1 (= c d)) (assume h2 (= b c)) (assume h3 (= a b))
            (step t4 (cl (= a d)) :rule trans :premises (h1 h2 h3))": true,
        }
        "Prmise term is not an equality" {
            "(assume h1 (= a b)) (assume h2 (not (= b c))) (assume h3 (= c d))
            (step t4 (cl (= a d)) :rule trans :premises (h1 h2 h3))": false,
        }
        "Conclusion clause is of the wrong form" {
            "(assume h1 (= a b)) (assume h2 (= b c))
            (step t3 (cl (not (= a c))) :rule trans :premises (h1 h2))": false,

            "(assume h1 (= a b)) (assume h2 (= b c))
            (step t3 (cl (= a c) (= c a)) :rule trans :premises (h1 h2))": false,
        }
    }
}
