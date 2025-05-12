#[test]
fn resolution() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun r () Bool)
            (declare-fun s () Bool)
            (declare-fun t () Bool)
            (declare-fun u () Bool)
        ",
        "Simple working examples" {
            "(assume h1 (not p))
            (step t2 (cl p q) :rule hole)
            (step t3 (cl q) :rule resolution :premises (h1 t2))": true,

            "(step t1 (cl (not p) (not q) (not r)) :rule hole)
            (step t2 (cl p) :rule hole)
            (step t3 (cl q) :rule hole)
            (step t4 (cl r) :rule hole)
            (step t5 (cl) :rule resolution :premises (t1 t2 t3 t4))": true,
        }
        "Missing term in final clause" {
            "(assume h1 (not p))
            (step t2 (cl p q r) :rule hole)
            (step t3 (cl q) :rule resolution :premises (h1 t2))": false,
        }
        "Term appears in final clause with wrong polarity" {
            "(assume h1 (not p))
            (step t2 (cl p q r) :rule hole)
            (step t3 (cl (not q) r) :rule resolution :premises (h1 t2))": false,
        }
        "Duplicate term in final clause" {
            "(step t1 (cl q (not p)) :rule hole)
            (step t2 (cl p q r) :rule hole)
            (step t3 (cl q q r) :rule resolution :premises (t1 t2))": true,
        }
        "Terms with leading negations" {
            "(assume h1 (not p))
            (assume h2 (not (not p)))
            (assume h3 (not (not (not p))))
            (assume h4 (not (not (not (not p)))))
            (step t5 (cl) :rule resolution :premises (h1 h2))
            (step t6 (cl) :rule resolution :premises (h2 h3))
            (step t7 (cl (not p) (not (not (not p)))) :rule resolution :premises (h1 h3))
            (step t8 (cl (not p) (not (not (not (not p)))))
                :rule resolution :premises (h1 h4))": true,
        }
        "Must use correct pivots" {
            "(step t1 (cl (not q) (not (not p)) (not p)) :rule hole)
            (step t2 (cl (not (not (not p))) p) :rule hole)
            (step t3 (cl (not q) p (not p)) :rule resolution :premises (t1 t2))": true,

            "(step t1 (cl (not q) (not (not p)) (not p)) :rule hole)
            (step t2 (cl (not (not (not p))) p) :rule hole)
            (step t3 (cl (not q) (not (not (not p))) (not (not p)))
                :rule resolution :premises (t1 t2))": true,

            "(step t1 (cl (not q) (not (not p)) (not p)) :rule hole)
            (step t2 (cl (not (not (not p))) p) :rule hole)
            (step t3 (cl (not q) p (not p) (not (not (not p))) (not (not p)))
                :rule resolution :premises (t1 t2))": true,
        }
        "Weird behaviour where leading negations sometimes are added to conclusion" {
            "(assume h1 (not p))
            (step t2 (cl p q) :rule hole)
            (step t3 (cl (not (not q))) :rule resolution :premises (h1 t2))": true,
        }
        "Premise is \"(not true)\" and leads to empty conclusion clause" {
            "(step t1 (cl (not true)) :rule hole)
            (step t2 (cl) :rule th_resolution :premises (t1))": true,
        }
        "Repeated premises" {
            "(step t1 (cl (not r)) :rule hole)
            (step t2 (cl p q r s) :rule hole)
            (step t3 (cl p q s) :rule th_resolution :premises (t1 t2 t2))": true,
        }
        "Implicit elimination of \"(cl false)\"" {
            "(step t1 (cl p q false) :rule hole)
            (step t2 (cl (not p)) :rule hole)
            (step t3 (cl (not q)) :rule hole)
            (step t4 (cl) :rule resolution :premises (t1 t2 t3))": true,

            // This implicit elimination is allowed, but not required
            "(step t1 (cl p q false) :rule hole)
            (step t2 (cl (not p)) :rule hole)
            (step t3 (cl (not q)) :rule hole)
            (step t4 (cl false) :rule resolution :premises (t1 t2 t3))": true,
        }
        "Pivots given in arguments" {
            "(step t1 (cl p q r) :rule hole)
            (step t2 (cl (not q) s) :rule hole)
            (step t3 (cl p r s) :rule resolution :premises (t1 t2) :args (q true))": true,

            "(step t1 (cl p (not q) r) :rule hole)
            (step t2 (cl (not r) s q) :rule hole)
            (step t3 (cl p r (not r) s)
                :rule resolution :premises (t1 t2) :args (q false))": true,

            "(step t1 (cl p q) :rule hole)
            (step t2 (cl (not q) (not r)) :rule hole)
            (step t3 (cl (not s) (not (not r)) t) :rule hole)
            (step t4 (cl s (not t) u) :rule hole)
            (step t5 (cl p t (not t) u)
                :rule resolution
                :premises (t1 t2 t3 t4)
                :args (q true (not r) true s false))": true,
        }
        "Only one pivot eliminated per clause" {
            "(step t1 (cl p q r) :rule hole)
            (step t2 (cl (not q) (not r)) :rule hole)
            (step t3 (cl p) :rule resolution :premises (t1 t2))": false,
        }
        "`th_resolution` may receive premises in wrong order" {
            "(step t1 (cl (not p) (not q) (not r)) :rule hole)
            (step t2 (cl p) :rule hole)
            (step t3 (cl q) :rule hole)
            (step t4 (cl r) :rule hole)
            (step t5 (cl) :rule th_resolution :premises (t4 t3 t2 t1))": true,

            "(step t1 (cl (not p) (not q) (not r)) :rule hole)
            (step t2 (cl p) :rule hole)
            (step t3 (cl q) :rule hole)
            (step t4 (cl r) :rule hole)
            (step t5 (cl) :rule th_resolution :premises (t1 t2 t3 t4))": true,
        }
        "Number of premises must be at least two" {
            "(step t1 (cl) :rule resolution)": false,

            "(assume h1 true)
            (step t2 (cl true) :rule resolution :premises (h1))": false,
        }
    }
}

#[test]
fn strict_resolution() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun r () Bool)
            (declare-fun s () Bool)
            (declare-fun t () Bool)
        ",
        "Simple working examples" {
            "(step t1 (cl p q r) :rule hole)
            (step t2 (cl s (not r) t) :rule hole)
            (step t3 (cl p q s t)
                :rule strict_resolution
                :premises (t1 t2)
                :args (r true))": true,
        }
        "No implicit reordering" {
            "(step t1 (cl p q r) :rule hole)
            (step t2 (cl s (not r) t) :rule hole)
            (step t3 (cl t s q p)
                :rule strict_resolution
                :premises (t1 t2)
                :args (r true))": false,

            "(step t1 (cl p q) :rule hole)
            (step t2 (cl r (not q) s) :rule hole)
            (step t3 (cl (not r) t) :rule hole)
            (step t4 (cl p t s)
                :rule strict_resolution
                :premises (t1 t2 t3)
                :args (q true r true))": false,
        }
        "No implicit removal of duplicates" {
            "(step t1 (cl p q r) :rule hole)
            (step t2 (cl (not q) s) :rule hole)
            (step t3 (cl (not r) s) :rule hole)
            (step t4 (cl p s s)
                :rule strict_resolution
                :premises (t1 t2 t3)
                :args (q true r true))": true,

            "(step t1 (cl p q r) :rule hole)
            (step t2 (cl (not q) s) :rule hole)
            (step t3 (cl (not r) s) :rule hole)
            (step t4 (cl p s)
                :rule strict_resolution
                :premises (t1 t2 t3)
                :args (q true r true))": false,

            // Duplicates also can't be implicitly introduced
            "(step t1 (cl p q r) :rule hole)
            (step t2 (cl s (not r) t) :rule hole)
            (step t3 (cl p q s t s)
                :rule strict_resolution
                :premises (t1 t2)
                :args (r true))": false,
        }
    }
}

#[test]
fn tautology() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun r () Bool)
            (declare-fun s () Bool)
        ",
        "Simple working examples" {
            "(step t1 (cl (not p) p) :rule hole)
            (step t2 (cl true) :rule tautology :premises (t1))": true,

            "(step t1 (cl p q (not q) r s) :rule hole)
            (step t2 (cl true) :rule tautology :premises (t1))": true,

            "(step t1 (cl p (not (not s)) q r (not (not (not s)))) :rule hole)
            (step t2 (cl true) :rule tautology  :premises (t1))": true,
        }
        "Conclusion is not \"true\"" {
            "(step t1 (cl p q (not q) r s) :rule hole)
            (step t2 (cl false) :rule tautology :premises (t1))": false,

            "(step t1 (cl p q (not q) r s) :rule hole)
            (step t2 (cl) :rule tautology :premises (t1))": false,
        }
        "Premise is not a tautology" {
            "(step t1 (cl p) :rule hole)
            (step t2 (cl true) :rule tautology :premises (t1))": false,

            "(step t1 (cl p (not (not s)) q r s) :rule hole)
            (step t2 (cl true) :rule tautology :premises (t1))": false,
        }
    }
}

#[test]
fn contraction() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun r () Bool)
            (declare-fun s () Bool)
        ",
        "Simple working examples" {
            "(step t1 (cl p q q r s s) :rule hole)
            (step t2 (cl p q r s) :rule contraction :premises (t1))": true,

            "(step t1 (cl p p p q q r s s s) :rule hole)
            (step t2 (cl p q r s) :rule contraction :premises (t1))": true,

            "(step t1 (cl p q r s) :rule hole)
            (step t2 (cl p q r s) :rule contraction :premises (t1))": true,
        }
        "Number of premises != 1" {
            "(step t1 (cl p q) :rule contraction)": false,

            "(assume h1 q)
            (assume h2 p)
            (step t3 (cl p q) :rule contraction :premises (h1 h2))": false,
        }
        "Premise is not a \"step\" command" {
            "(assume h1 q)
            (step t2 (cl q) :rule contraction :premises (h1))": true,
        }
        "Not all terms removed" {
            "(step t1 (cl p p q q) :rule hole)
            (step t2 (cl p p q) :rule contraction :premises (t1))": true,

            "(step t1 (cl q p p q q) :rule hole)
            (step t2 (cl q p q) :rule contraction :premises (t1))": true,
        }
        "Terms are not in correct order" {
            "(step t1 (cl p q q r) :rule hole)
            (step t2 (cl p r q) :rule contraction :premises (t1))": true,
        }
        "Conclusion is missing terms" {
            "(step t1 (cl p q q r) :rule hole)
            (step t2 (cl p r) :rule contraction :premises (t1))": false,

            "(step t1 (cl p p q r) :rule hole)
            (step t2 (cl p q) :rule contraction :premises (t1))": false,
        }
        "Conclusion has extra term at the end" {
            "(step t1 (cl p p q) :rule hole)
            (step t2 (cl p q r s) :rule contraction :premises (t1))": false,
        }
    }
}
