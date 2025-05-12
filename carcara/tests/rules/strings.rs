#[test]
fn concat_eq() {
    test_cases! {
        definitions = "
            (declare-fun a () String)
            (declare-fun b () String)
            (declare-fun c () String)
        ",
        "Simple working examples" {
            r#"(assume h1 (= "0A" (str.++ "0" (str.from_code (str.len a)))))
               (step t1 (cl (= "A" (str.from_code (str.len a)))) :rule concat_eq :premises (h1) :args (false))"#: true,
            r#"(assume h1 (= (str.++ "0" "A") (str.++ "0" (str.from_code (str.len a)))))
               (step t1 (cl (= "A" (str.from_code (str.len a)))) :rule concat_eq :premises (h1) :args (false))"#: true,
            r#"(assume h1 (= (str.++ "A" (str.++ b "A")) (str.++ "AA" (str.at c (str.len c)))))
               (step t1 (cl (= (str.++ b "A") (str.++ "A" (str.at c (str.len c))))) :rule concat_eq :premises (h1) :args (false))"#: true,
        }
        "Term are not a str.++ application" {
            r#"(assume h1 (= (str.++ "0" (str.from_int (str.len c))) ""))
               (step t1 (cl (= (str.from_int (str.len c)) "")) :rule concat_eq :premises (h1) :args (false))"#: false,
            r#"(assume h1 (= "0" (str.++ "" (str.from_int (str.len b)))))
               (step t1 (cl (= "" (str.from_int (str.len b)))) :rule concat_eq :premises (h1) :args (false))"#: false,
        }
        "Terms with no common prefixes" {
            r#"(assume h1 (= "yxzw" (str.++ "xy" "z" a)))
               (step t1 (cl (= "yxzw" (str.++ "xy" "z" a))) :rule concat_eq :premises (h1) :args (false))"#: true,
            r#"(assume h1 (= (str.++ a (str.from_int (str.len b))) (str.++ "0" (str.++ "A" c))))
               (step t1 (cl (= (str.++ a (str.from_int (str.len b))) (str.++ "0" (str.++ "A" c)))) :rule concat_eq :premises (h1) :args (false))"#: true,
        }
        "Concatenation with more than 2 arguments" {
            r#"(assume h1 (= "xyzw" (str.++ "xy" "z" a)))
               (step t1 (cl (= "w" a)) :rule concat_eq :premises (h1) :args (false))"#: true,
            r#"(assume h1 (= "xyzw" (str.++ "x" (str.++ "y" "z") a)))
               (step t1 (cl (= "w" a)) :rule concat_eq :premises (h1) :args (false))"#: true,
        }
        "Reverse argument set to true" {
            r#"(assume h1 (= "wzyx" (str.++ a "z" "yx")))
               (step t1 (cl (= "w" a)) :rule concat_eq :premises (h1) :args (true))"#: true,
            r#"(assume h1 (= (str.++ "A" (str.++ b "A")) (str.++ (str.at c (str.len c)) "AA")))
               (step t1 (cl (= (str.++ "A" b) (str.++ (str.at c (str.len c)) "A"))) :rule concat_eq :premises (h1) :args (true))"#: true,
            r#"(assume h1 (= (str.++ (str.from_int (str.len c)) "0") "0"))
               (step t1 (cl (= (str.from_int (str.len c)) "")) :rule concat_eq :premises (h1) :args (true))"#: true,
            r#"(assume h1 (= "0" (str.++ (str.from_int (str.len b)) "0")))
               (step t1 (cl (= "" (str.from_int (str.len b)))) :rule concat_eq :premises (h1) :args (true))"#: true,
        }
        "Invalid argument type" {
            r#"(assume h1 (not (= "xyzw" (str.++ "xy" (str.++ "z" a)))))
               (step t1 (cl (= "w" a)) :rule concat_eq :premises (h1) :args (1))"#: false,
            r#"(assume h1 (not (= "xyzw" (str.++ "xy" (str.++ "z" a)))))
               (step t1 (cl (= "w" a)) :rule concat_eq :premises (h1) :args (1.5))"#: false,
            r#"(assume h1 (not (= "xyzw" (str.++ "xy" (str.++ "z" a)))))
               (step t1 (cl (= "w" a)) :rule concat_eq :premises (h1) :args ((- 1)))"#: false,
            r#"(assume h1 (not (= "xyzw" (str.++ "xy" (str.++ "z" a)))))
               (step t1 (cl (= "w" a)) :rule concat_eq :premises (h1) :args ("test"))"#: false,
        }
        "Premise term is not an equality" {
            r#"(assume h1 (not (= "xyzw" (str.++ "xy" (str.++ "z" a)))))
               (step t1 (cl (= "w" a)) :rule concat_eq :premises (h1) :args (false))"#: false,
        }
        "Conclusion term is not an equality" {
            r#"(assume h1 (= "xyzw" (str.++ "xy" "z" a)))
               (step t1 (cl (not (= "w" a))) :rule concat_eq :premises (h1) :args (false))"#: false,
        }
        "Switched conclusion terms" {
            r#"(assume h1 (= "xyzw" (str.++ "xy" (str.++ "z" a))))
               (step t1 (cl (= a "w")) :rule concat_eq :premises (h1) :args (false))"#: false,
            r#"(assume h1 (= (str.++ "xy" (str.++ "z" a)) (str.++ "x" "yzw")))
               (step t1 (cl (= "w" a)) :rule concat_eq :premises (h1) :args (false))"#: false,
            r#"(assume h1 (= (str.++ "A" (str.++ b "A")) (str.++ "AA" (str.at c (str.len c)))))
               (step t1 (cl (= (str.++ "A" (str.at c (str.len c))) (str.++ b "A"))) :rule concat_eq :premises (h1) :args (false))"#: false,
        }
        "Prefix was not fully consumed" {
            r#"(assume h1 (= (str.++ "a" "b" b (str.++ "c" "d")) (str.++ "a" "b" (str.++ b c))))
               (step t1 (cl (= (str.++ b "cd") (str.++ b c))) :rule concat_eq :premises (h1) :args (false))"#: false,
            r#"(assume h1 (= (str.++ "A" (str.++ b "AA")) (str.++ (str.at c (str.len c)) "AA")))
               (step t1 (cl (= (str.++ "A" (str.++ b "A")) (str.++ (str.at c (str.len c)) "A"))) :rule concat_eq :premises (h1) :args (true))"#: false,
        }
        "Inverted argument value" {
            r#"(assume h1 (= (str.++ "w" (str.++ "z" "y" "x")) (str.++ a "z" "yx")))
               (step t1 (cl (= "w" a)) :rule concat_eq :premises (h1) :args (false))"#: false,
            r#"(assume h1 (= (str.++ "A" (str.++ b "A")) (str.++ (str.at c (str.len c)) "AA")))
               (step t1 (cl (= (str.++ "A" b) (str.++ (str.at c (str.len c)) "A"))) :rule concat_eq :premises (h1) :args (false))"#: false,
        }
    }
}

#[test]
fn concat_unify() {
    test_cases! {
        definitions = "
            (declare-fun a () String)
            (declare-fun b () String)
            (declare-fun c () String)
            (declare-fun d () String)
        ",
        "Simple working examples" {
            r#"(assume h1 (= "abcd" "abcd"))
               (assume h2 (= (str.len "abc") (str.len "abc")))
               (step t1 (cl (= "abc" "abc")) :rule concat_unify :premises (h1 h2) :args (false))"#: true,
            r#"(assume h1 (= (str.++ "a" b "c" (str.++ d "e")) (str.++ "a" c "de")))
               (assume h2 (= (str.len (str.++ "a" b)) (str.len "a")))
               (step t1 (cl (= (str.++ "a" b) "a")) :rule concat_unify :premises (h1 h2) :args (false))"#: true,
            r#"(assume h1 (= (str.++ a b c) d))
               (assume h2 (= (str.len (str.++ a b)) (str.len "")))
               (step t1 (cl (= (str.++ a b) "")) :rule concat_unify :premises (h1 h2) :args (false))"#: true,
        }
        "Reverse argument set to true" {
            r#"(assume h1 (= "abcd" "abcd"))
               (assume h2 (= (str.len "cd") (str.len "cd")))
               (step t1 (cl (= "cd" "cd")) :rule concat_unify :premises (h1 h2) :args (true))"#: true,
            r#"(assume h1 (= (str.++ "a" b "c" (str.++ d "e")) (str.++ "a" c "de")))
               (assume h2 (= (str.len (str.++ d "e")) (str.len (str.++ "d" "e"))))
               (step t1 (cl (= (str.++ d "e") "de")) :rule concat_unify :premises (h1 h2) :args (true))"#: true,
        }
        "Failing examples" {
            r#"(assume h1 (= (str.++ "a" b "c" (str.++ d "e")) (str.++ a c "de")))
               (assume h2 (= (str.len (str.++ "a" "b")) (str.len a)))
               (step t1 (cl (= (str.++ "a" b) a)) :rule concat_unify :premises (h1 h2) :args (false))"#: false,
            r#"(assume h1 (= (str.++ "a" b "c" (str.++ d "e")) (str.++ a c "de")))
               (assume h2 (= (str.len (str.++ "a" "b")) (str.len a)))
               (step t1 (cl (= (str.++ a b) "")) :rule concat_unify :premises (h1 h2) :args (false))"#: false,
        }
        "Invalid argument type" {
            r#"(assume h1 (= (str.++ a "b" c) (str.++ a d "e")))
               (assume h2 (= (str.len a) (str.len "")))
               (step t1 (cl (= a "")) :rule concat_unify :premises (h1 h2) :args (1))"#: false,
            r#"(assume h1 (= (str.++ a "b" c) (str.++ a d "e")))
               (assume h2 (= (str.len a) (str.len "")))
               (step t1 (cl (= a "")) :rule concat_unify :premises (h1 h2) :args ((- 1)))"#: false,
            r#"(assume h1 (= (str.++ a "b" c) (str.++ a d "e")))
               (assume h2 (= (str.len a) (str.len "")))
               (step t1 (cl (= a "")) :rule concat_unify :premises (h1 h2) :args ("test"))"#: false,
        }
        "Premise term is not an equality" {
            r#"(assume h1 (not (= (str.++ a "b" c) (str.++ a d "e"))))
               (assume h2 (= (str.len a) (str.len "")))
               (step t1 (cl (= a "")) :rule concat_unify :premises (h1 h2) :args (false))"#: false,
            r#"(assume h1 (= (str.++ a "b" c) (str.++ a d "e")))
               (assume h2 (not (= (str.len a) (str.len ""))))
               (step t1 (cl (= a "")) :rule concat_unify :premises (h1 h2) :args (false))"#: false,
        }
        "Conclusion term is not an equality" {
            r#"(assume h1 (= (str.++ a "b" c) (str.++ a d "e")))
               (assume h2 (= (str.len a) (str.len "")))
               (step t1 (cl (not (= a ""))) :rule concat_unify :premises (h1 h2) :args (false))"#: false,
        }
        "Switched conclusion terms" {
            r#"(assume h1 (= (str.++ "a" b "c" (str.++ d "e")) (str.++ "a" c "de")))
               (assume h2 (= (str.len (str.++ "a" b)) (str.len "a")))
               (step t1 (cl (= "a" (str.++ "a" b))) :rule concat_unify :premises (h1 h2) :args (false))"#: false,
            r#"(assume h1 (= (str.++ "a" c "de") (str.++ "a" b "c" (str.++ d "e"))))
               (assume h2 (= (str.len "a") (str.len (str.++ "a" b))))
               (step t1 (cl (= (str.++ "a" b) "a")) :rule concat_unify :premises (h1 h2) :args (false))"#: false,
        }
        "Inverted argument value" {
            r#"(assume h1 (= (str.++ "x" (str.++ a "y") b) (str.++ "x" c "de")))
               (assume h2 (= (str.len (str.++ "y" b)) (str.len (str.++ c "d"))))
               (step t1 (cl (= (str.++ "y" b) (str.++ c "d"))) :rule concat_unify :premises (h1 h2) :args (false))"#: false,
            r#"(assume h1 (= (str.++ "a" b "c" (str.++ d "e")) (str.++ "a" c "de")))
               (assume h2 (= (str.len (str.++ d "e")) (str.len (str.++ c "de"))))
               (step t1 (cl (= (str.++ d "e") (str.++ c "de"))) :rule concat_unify :premises (h1 h2) :args (false))"#: false,
        }
        "Invalid prefixes" {
            r#"(assume h1 (= (str.++ "a" b "c" (str.++ d "e")) (str.++ "a" c "de")))
               (assume h2 (= (str.len (str.++ "a" "b")) (str.len "a")))
               (step t1 (cl (= (str.++ "a" "b") "a")) :rule concat_unify :premises (h1 h2) :args (false))"#: false,
            r#"(assume h1 (= (str.++ "a" b "c" (str.++ d "e")) (str.++ "a" c "de")))
               (assume h2 (= (str.len (str.++ "a" b)) (str.len "b")))
               (step t1 (cl (= (str.++ "a" b) "b")) :rule concat_unify :premises (h1 h2) :args (false))"#: false,
        }
        "Prefix is bigger than the term" {
            r#"(assume h1 (= (str.++ "a" b "c") (str.++ "a" c "de")))
               (assume h2 (= (str.len (str.++ "a" b "c" "d")) (str.len (str.++ "a" c))))
               (step t1 (cl (= (str.++ "a" b "c" "d") (str.++ "a" c))) :rule concat_unify :premises (h1 h2) :args (false))"#: false,
            r#"(assume h1 (= (str.++ "a" b "c") (str.++ "a" c "de")))
               (assume h2 (= (str.len (str.++ "a" b)) (str.len (str.++ "a" c "de" "f"))))
               (step t1 (cl (= (str.++ "a" b) (str.++ "a" c (str.++ "de" "f")))) :rule concat_unify :premises (h1 h2) :args (false))"#: false,
        }
    }
}

#[test]
fn concat_conflict() {
    test_cases! {
        definitions = "
            (declare-fun a () String)
            (declare-fun b () String)
            (declare-fun c () String)
            (declare-fun d () String)
            (declare-fun e () String)
        ",
        "Simple working examples" {
            r#"(assume h1 (= (str.++ "ab" c) (str.++ "c" e)))
               (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: true,
            r#"(assume h1 (= (str.++ "abc" d) (str.++ "abd" (str.++ c e))))
               (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: true,
            r#"(assume h1 (= (str.++ "ac" (str.++ b d)) (str.++ "abd" (str.++ a b))))
               (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: true,
        }
        "Reverse argument set to true" {
            r#"(assume h1 (= (str.++ d "cba") (str.++ (str.++ e c) "dba")))
               (step t1 (cl false) :rule concat_conflict :premises (h1) :args (true))"#: true,
            r#"(assume h1 (= (str.++ (str.++ d b) "ac") (str.++ (str.++ b a) "dba")))
               (step t1 (cl false) :rule concat_conflict :premises (h1) :args (true))"#: true,
        }
        "All possible constants are prefixes of each other" {
            r#"(assume h1 (= (str.++ "ac" "bd" c e) (str.++ "acb" b c)))
               (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: false,
            r#"(assume h1 (= (str.++ "d" a b) (str.++ "de" c d)))
               (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: false,
            r#"(assume h1 (= (str.++ "ab" a b) (str.++ "ab" c d)))
               (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: false,
        }
        "Remaining suffix is empty" {
            r#"(assume h1 (= "ab" (str.++ "ab" c d)))
               (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: false,
            r#"(assume h1 (= "ab" (str.++ "ab" (str.++ "" c d))))
               (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: false,
            r#"(assume h1 (= "cbd" (str.++ "c" "bd")))
               (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: false,
            r#"(assume h1 (= (str.++ "cbd" a) (str.++ "c" (str.++ "bd" a))))
               (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: false,
            r#"(assume h1 (= (str.++ "ab" c d) "ab"))
               (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: false,
            r#"(assume h1 (= (str.++ "ab" (str.++ "" c d)) "ab"))
               (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: false,
        }
        "Term does not have a constant prefix" {
            r#"(assume h1 (= (str.++ a "bc" d) (str.++ "ab" c)))
               (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: false,
            r#"(assume h1 (= (str.++ "b" "cd" e) (str.++ b "cb" e)))
               (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: false,
        }
        "Term are not a str.++ application" {
            r#"(assume h1 (= (str.++ "ac" "bd" c e) ""))
               (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: false,
            r#"(assume h1 (= "" (str.++ "ab" c)))
               (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: false,
        }
        "Invalid argument type" {
            r#"(assume h1 (= (str.++ "ab" c) (str.++ "c" e)))
               (step t1 (cl false) :rule concat_conflict :premises (h1) :args (1))"#: false,
            r#"(assume h1 (= (str.++ "ab" c) (str.++ "c" e)))
               (step t1 (cl false) :rule concat_conflict :premises (h1) :args (1.5))"#: false,
            r#"(assume h1 (= (str.++ "ab" c) (str.++ "c" e)))
               (step t1 (cl false) :rule concat_conflict :premises (h1) :args ((- 1)))"#: false,
            r#"(assume h1 (= (str.++ "ab" c) (str.++ "c" e)))
               (step t1 (cl false) :rule concat_conflict :premises (h1) :args ("test"))"#: false,
        }
        "Premise term is not an equality" {
            r#"(assume h1 (not (= (str.++ "ab" c) (str.++ "c" e))))
               (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: false,
        }
        "Conclusion term is not the false bool constant" {
            r#"(assume h1 (= (str.++ "ab" c) (str.++ "c" e)))
               (step t1 (cl true) :rule concat_conflict :premises (h1) :args (false))"#: false,
            r#"(assume h1 (= (str.++ "ab" c) (str.++ "c" e)))
               (step t1 (cl (= "a" b)) :rule concat_conflict :premises (h1) :args (false))"#: false,
            r#"(assume h1 (= (str.++ "ab" c) (str.++ "c" e)))
               (step t1 (cl (= "a" "b")) :rule concat_conflict :premises (h1) :args (false))"#: false,
            r#"(assume h1 (= (str.++ "ab" c) (str.++ "c" e)))
               (step t1 (cl (not (= "a" "b"))) :rule concat_conflict :premises (h1) :args (false))"#: false,
        }
        "Inverted argument value" {
            r#"(assume h1 (= (str.++ "ab" c) (str.++ "c" e)))
               (step t1 (cl false) :rule concat_conflict :premises (h1) :args (true))"#: false,
            r#"(assume h1 (= (str.++ "abc" d) (str.++ "abd" (str.++ c e))))
               (step t1 (cl false) :rule concat_conflict :premises (h1) :args (true))"#: false,
            r#"(assume h1 (= (str.++ d "cba") (str.++ (str.++ e c) "dba")))
               (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: false,
            r#"(assume h1 (= (str.++ (str.++ d b) "ac") (str.++ (str.++ b a) "dba")))
               (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: false,
        }
    }
}

#[test]
fn concat_csplit_prefix() {
    test_cases! {
        definitions = "
            (declare-fun a () String)
            (declare-fun b () String)
            (declare-fun c () String)
            (declare-fun d () String)
        ",
        "Simple working examples" {
            r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
               (assume h2 (not (= (str.len "a") 0)))
               (step t1 (cl (= "a" (str.++ "a" (str.substr "a" 1 (- (str.len "a") 1))))) :rule concat_csplit_prefix :premises (h1 h2))"#: true,
            r#"(assume h1 (= (str.++ a "b" c) (str.++ "ab" c)))
               (assume h2 (not (= (str.len (str.++ a "b")) 0)))
               (step t1 (cl (= (str.++ a "b") (str.++ "a" (str.substr (str.++ a "b") 1 (- (str.len (str.++ a "b")) 1))))) :rule concat_csplit_prefix :premises (h1 h2))"#: true,
            r#"(assume h1 (= (str.++ d (str.++ c (str.++ b "a"))) (str.++ "b" (str.++ "c" d))))
               (assume h2 (not (= (str.len (str.++ d c)) 0)))
               (step t1 (cl (= (str.++ d c) (str.++ "b" (str.substr (str.++ d c) 1 (- (str.len (str.++ d c)) 1))))) :rule concat_csplit_prefix :premises (h1 h2))"#: true,
        }
        "Term does not have a constant prefix" {
            r#"(assume h1 (= (str.++ d (str.++ c (str.++ b "a"))) (str.++ b (str.++ "c" d))))
               (assume h2 (not (= (str.len (str.++ d c)) 0)))
               (step t1 (cl (= (str.++ d c) (str.++ b (str.substr (str.++ d c) 1 (- (str.len (str.++ d c)) 1))))) :rule concat_csplit_prefix :premises (h1 h2))"#: false,
        }
        "The term of the second premise is not a prefix of the first one" {
            r#"(assume h1 (= (str.++ a "b" c) (str.++ "ab" c)))
               (assume h2 (not (= (str.len (str.++ "b" a)) 0)))
               (step t1 (cl (= (str.++ a "b") (str.++ "a" (str.substr (str.++ a "b") 1 (- (str.len (str.++ a "b")) 1))))) :rule concat_csplit_prefix :premises (h1 h2))"#: false,
        }
        "Term are not a str.++ application" {
            r#"(assume h1 (= (str.++ "a" "b" b) ""))
               (assume h2 (not (= (str.len "a") 0)))
               (step t1 (cl (= "a" (str.++ "a" (str.substr "a" 1 (- (str.len "a") 1))))) :rule concat_csplit_prefix :premises (h1 h2))"#: false,
            r#"(assume h1 (= "" (str.++ "a" c)))
               (assume h2 (not (= (str.len "a") 0)))
               (step t1 (cl (= "a" (str.++ "a" (str.substr "a" 1 (- (str.len "a") 1))))) :rule concat_csplit_prefix :premises (h1 h2))"#: false,
        }
        "Premise term is not an equality" {
            r#"(assume h1 (not (= (str.++ d (str.++ c (str.++ b "a"))) (str.++ "b" (str.++ "c" d)))))
               (assume h2 (not (= (str.len (str.++ d c)) 0)))
               (step t1 (cl (= (str.++ d c) (str.++ "b" (str.substr (str.++ d c) 1 (- (str.len (str.++ d c)) 1))))) :rule concat_csplit_prefix :premises (h1 h2))"#: false,
        }
        "Premise term is not an inequality of the form (not (= (str.len str) 0))" {
            r#"(assume h1 (= (str.++ d (str.++ c (str.++ b "a"))) (str.++ "b" (str.++ "c" d))))
               (assume h2 (= (str.len (str.++ d c)) 0))
               (step t1 (cl (= (str.++ d c) (str.++ "b" (str.substr (str.++ d c) 1 (- (str.len (str.++ d c)) 1))))) :rule concat_csplit_prefix :premises (h1 h2))"#: false,
            r#"(assume h1 (= (str.++ d (str.++ c (str.++ b "a"))) (str.++ "b" (str.++ "c" d))))
               (assume h2 (not (= (str.to_code (str.++ d c)) 0)))
               (step t1 (cl (= (str.++ d c) (str.++ "b" (str.substr (str.++ d c) 1 (- (str.len (str.++ d c)) 1))))) :rule concat_csplit_prefix :premises (h1 h2))"#: false,
            r#"(assume h1 (= (str.++ d (str.++ c (str.++ b "a"))) (str.++ "b" (str.++ "c" d))))
               (assume h2 (not (= (str.len (str.++ d c)) 1)))
               (step t1 (cl (= (str.++ d c) (str.++ "b" (str.substr (str.++ d c) 1 (- (str.len (str.++ d c)) 1))))) :rule concat_csplit_prefix :premises (h1 h2))"#: false,
        }
        "Conclusion term is not an equality" {
            r#"(assume h1 (= (str.++ d (str.++ c (str.++ b "a"))) (str.++ "b" (str.++ "c" d))))
               (assume h2 (not (= (str.len (str.++ d c)) 0)))
               (step t1 (cl (not (= (str.++ d c) (str.++ "b" (str.substr (str.++ d c) 1 (- (str.len (str.++ d c)) 1)))))) :rule concat_csplit_prefix :premises (h1 h2))"#: false,
        }
        "Switched conclusion terms" {
            r#"(assume h1 (= (str.++ d (str.++ c (str.++ b "a"))) (str.++ "b" (str.++ "c" d))))
               (assume h2 (not (= (str.len (str.++ d c)) 0)))
               (step t1 (cl (= (str.++ "b" (str.substr (str.++ d c) 1 (- (str.len (str.++ d c)) 1))) (str.++ d c))) :rule concat_csplit_prefix :premises (h1 h2))"#: false,
        }
    }
}

#[test]
fn concat_csplit_suffix() {
    test_cases! {
        definitions = "
            (declare-fun a () String)
            (declare-fun b () String)
            (declare-fun c () String)
            (declare-fun d () String)
        ",
        "Simple working examples" {
            r#"(assume h1 (= (str.++ "c" "b" a) (str.++ a (str.++ c "b"))))
               (assume h2 (not (= (str.len (str.++ "b" a)) 0)))
               (step t1 (cl (= (str.++ "b" a) (str.++ (str.substr (str.++ "b" a) 0 (- (str.len (str.++ "b" a)) 1)) "b"))) :rule concat_csplit_suffix :premises (h1 h2))"#: true,
            r#"(assume h1 (= (str.++ d (str.++ c (str.++ "b" a))) (str.++ "b" (str.++ "c" "de"))))
               (assume h2 (not (= (str.len (str.++ c (str.++ "b" a))) 0)))
               (step t1 (cl (= (str.++ c (str.++ "b" a)) (str.++ (str.substr (str.++ c (str.++ "b" a)) 0 (- (str.len (str.++ c (str.++ "b" a))) 1)) "e"))) :rule concat_csplit_suffix :premises (h1 h2))"#: true,
            r#"(assume h1 (= (str.++ d (str.++ "c" (str.++ "b" a))) (str.++ "b" (str.++ c "d"))))
               (assume h2 (not (= (str.len (str.++ "c" (str.++ "b" a))) 0)))
               (step t1 (cl (= (str.++ "c" (str.++ "b" a)) (str.++ (str.substr (str.++ "c" (str.++ "b" a)) 0 (- (str.len (str.++ "c" (str.++ "b" a))) 1)) "d"))) :rule concat_csplit_suffix :premises (h1 h2))"#: true,
        }
        "Term does not have a constant suffix" {
            r#"(assume h1 (= (str.++ "c" "b" a) (str.++ a (str.++ c b))))
               (assume h2 (not (= (str.len (str.++ "b" a)) 0)))
               (step t1 (cl (= (str.++ "b" a) (str.++ (str.substr (str.++ "b" a) 0 (- (str.len (str.++ "b" a)) 1)) "b"))) :rule concat_csplit_suffix :premises (h1 h2))"#: false,
        }
        "The term of the second premise is not a suffix of the first one" {
            r#"(assume h1 (= (str.++ d (str.++ c (str.++ "b" a))) (str.++ "b" (str.++ "c" "de"))))
               (assume h2 (not (= (str.len (str.++ c (str.++ a "b"))) 0)))
               (step t1 (cl (= (str.++ c (str.++ "b" a)) (str.++ (str.substr (str.++ c (str.++ "b" a)) 0 (- (str.len (str.++ c (str.++ "b" a))) 1)) "e"))) :rule concat_csplit_suffix :premises (h1 h2))"#: false,
        }
        "Term are not a str.++ application" {
            r#"(assume h1 (= "" (str.++ "b" (str.++ "c" "de"))))
               (assume h2 (not (= (str.len (str.++ c (str.++ "b" a))) 0)))
               (step t1 (cl (= (str.++ c (str.++ "b" a)) (str.++ (str.substr (str.++ c (str.++ "b" a)) 0 (- (str.len (str.++ c (str.++ "b" a))) 1)) "e"))) :rule concat_csplit_suffix :premises (h1 h2))"#: false,
            r#"(assume h1 (= (str.++ d (str.++ c (str.++ "b" a))) ""))
               (assume h2 (not (= (str.len (str.++ c (str.++ "b" a))) 0)))
               (step t1 (cl (= (str.++ c (str.++ "b" a)) (str.++ (str.substr (str.++ c (str.++ "b" a)) 0 (- (str.len (str.++ c (str.++ "b" a))) 1)) "e"))) :rule concat_csplit_suffix :premises (h1 h2))"#: false,
        }
        "Premise term is not an equality" {
            r#"(assume h1 (not (= (str.++ d (str.++ "c" (str.++ "b" a))) (str.++ "b" (str.++ c "d")))))
               (assume h2 (not (= (str.len (str.++ "c" (str.++ "b" a))) 0)))
               (step t1 (cl (= (str.++ "c" (str.++ "b" a)) (str.++ (str.substr (str.++ "c" (str.++ "b" a)) 0 (- (str.len (str.++ "c" (str.++ "b" a))) 1)) "d"))) :rule concat_csplit_suffix :premises (h1 h2))"#: false,
        }
        "Premise term is not an inequality of the form (not (= (str.len str) 0))" {
            r#"(assume h1 (= (str.++ "c" "b" a) (str.++ a (str.++ c "b"))))
               (assume h2 (= (str.len (str.++ "b" a)) 0))
               (step t1 (cl (= (str.++ "b" a) (str.++ (str.substr (str.++ "b" a) 0 (- (str.len (str.++ "b" a)) 1)) "b"))) :rule concat_csplit_suffix :premises (h1 h2))"#: false,
            r#"(assume h1 (= (str.++ "c" "b" a) (str.++ a (str.++ c "b"))))
               (assume h2 (not (= (str.to_code (str.++ "b" a)) 0)))
               (step t1 (cl (= (str.++ "b" a) (str.++ (str.substr (str.++ "b" a) 0 (- (str.len (str.++ "b" a)) 1)) "b"))) :rule concat_csplit_suffix :premises (h1 h2))"#: false,
            r#"(assume h1 (= (str.++ "c" "b" a) (str.++ a (str.++ c "b"))))
               (assume h2 (not (= (str.len (str.++ "b" a)) 1)))
               (step t1 (cl (= (str.++ "b" a) (str.++ (str.substr (str.++ "b" a) 0 (- (str.len (str.++ "b" a)) 1)) "b"))) :rule concat_csplit_suffix :premises (h1 h2))"#: false,
        }
        "Conclusion term is not an equality" {
            r#"(assume h1 (= (str.++ d (str.++ c (str.++ "b" a))) (str.++ "b" (str.++ "c" "de"))))
               (assume h2 (not (= (str.len (str.++ c (str.++ "b" a))) 0)))
               (step t1 (cl (not (= (str.++ c (str.++ "b" a)) (str.++ (str.substr (str.++ c (str.++ "b" a)) 0 (- (str.len (str.++ c (str.++ "b" a))) 1)) "e")))) :rule concat_csplit_suffix :premises (h1 h2))"#: false,
        }
        "Switched conclusion terms" {
            r#"(assume h1 (= (str.++ d (str.++ "c" (str.++ "b" a))) (str.++ "b" (str.++ c "d"))))
               (assume h2 (not (= (str.len (str.++ "c" (str.++ "b" a))) 0)))
               (step t1 (cl (= (str.++ (str.substr (str.++ "c" (str.++ "b" a)) 0 (- (str.len (str.++ "c" (str.++ "b" a))) 1)) "d") (str.++ "c" (str.++ "b" a)))) :rule concat_csplit_suffix :premises (h1 h2))"#: false,
        }
    }
}

#[test]
fn concat_split_prefix() {
    test_cases! {
        definitions = "
            (declare-fun a () String)
            (declare-fun b () String)
            (declare-fun c () String)
            (declare-fun d () String)
            (declare-fun e () String)
        ",
        "Simple working examples" {
            r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
               (assume h2 (not (= (str.len "a") (str.len (str.++ "a" c)))))
               (define-fun r_skolem () String (ite (>= (str.len "a") (str.len (str.++ "a" c))) (str.substr "a" (str.len (str.++ "a" c)) (- (str.len "a") (str.len (str.++ "a" c)))) (str.substr (str.++ "a" c) (str.len "a") (- (str.len (str.++ "a" c)) (str.len "a")))))
               (step t1 (cl (and (or (= "a" (str.++ "a" c r_skolem)) (= (str.++ "a" c) (str.++ "a" r_skolem))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_prefix :premises (h1 h2))"#: true,
            r#"(assume h1 (= (str.++ a b c) (str.++ c d e)))
               (assume h2 (not (= (str.len (str.++ a b)) (str.len c))))
               (define-fun r_skolem () String (ite (>= (str.len (str.++ a b)) (str.len c)) (str.substr (str.++ a b) (str.len c) (- (str.len (str.++ a b)) (str.len c))) (str.substr c (str.len (str.++ a b)) (- (str.len c) (str.len (str.++ a b))))))
               (step t1 (cl (and (or (= (str.++ a b) (str.++ c r_skolem)) (= c (str.++ a b r_skolem))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_prefix :premises (h1 h2))"#: true,
        }
        "The term of the second premise is not a prefix of the first one" {
            r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
               (assume h2 (not (= (str.len a) (str.len (str.++ "a" c)))))
               (define-fun r_skolem () String (ite (>= (str.len "a") (str.len (str.++ "a" c))) (str.substr "a" (str.len (str.++ "a" c)) (- (str.len "a") (str.len (str.++ "a" c)))) (str.substr (str.++ "a" c) (str.len "a") (- (str.len (str.++ "a" c)) (str.len "a")))))
               (step t1 (cl (and (or (= "a" (str.++ "a" c r_skolem)) (= (str.++ "a" c) (str.++ "a" r_skolem))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_prefix :premises (h1 h2))"#: false,
            r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
               (assume h2 (not (= (str.len "a") (str.len (str.++ c "a")))))
               (define-fun r_skolem () String (ite (>= (str.len "a") (str.len (str.++ "a" c))) (str.substr "a" (str.len (str.++ "a" c)) (- (str.len "a") (str.len (str.++ "a" c)))) (str.substr (str.++ "a" c) (str.len "a") (- (str.len (str.++ "a" c)) (str.len "a")))))
               (step t1 (cl (and (or (= "a" (str.++ "a" c r_skolem)) (= (str.++ "a" c) (str.++ "a" r_skolem))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_prefix :premises (h1 h2))"#: false,
        }
        "Terms are not str.++ applications" {
            r#"(assume h1 (= "" (str.++ "a" c)))
               (assume h2 (not (= (str.len "a") (str.len (str.++ "a" c)))))
               (define-fun r_skolem () String (ite (>= (str.len "a") (str.len (str.++ "a" c))) (str.substr "a" (str.len (str.++ "a" c)) (- (str.len "a") (str.len (str.++ "a" c)))) (str.substr (str.++ "a" c) (str.len "a") (- (str.len (str.++ "a" c)) (str.len "a")))))
               (step t1 (cl (and (or (= "a" (str.++ "a" c r_skolem)) (= (str.++ "a" c) (str.++ "a" r_skolem))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_prefix :premises (h1 h2))"#: false,
            r#"(assume h1 (= (str.++ "a" "b" b) ""))
               (assume h2 (not (= (str.len "a") (str.len (str.++ "a" c)))))
               (define-fun r_skolem () String (ite (>= (str.len "a") (str.len (str.++ "a" c))) (str.substr "a" (str.len (str.++ "a" c)) (- (str.len "a") (str.len (str.++ "a" c)))) (str.substr (str.++ "a" c) (str.len "a") (- (str.len (str.++ "a" c)) (str.len "a")))))
               (step t1 (cl (and (or (= "a" (str.++ "a" c r_skolem)) (= (str.++ "a" c) (str.++ "a" r_skolem))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_prefix :premises (h1 h2))"#: false,
        }
        "Premise term is not an equality" {
            r#"(assume h1 (not (= (str.++ a b c) (str.++ c d e))))
               (assume h2 (not (= (str.len (str.++ a b)) (str.len c))))
               (define-fun r_skolem () String (ite (>= (str.len (str.++ a b)) (str.len c)) (str.substr (str.++ a b) (str.len c) (- (str.len (str.++ a b)) (str.len c))) (str.substr c (str.len (str.++ a b)) (- (str.len c) (str.len (str.++ a b))))))
               (step t1 (cl (and (or (= (str.++ a b) (str.++ c r_skolem)) (= c (str.++ a b r_skolem))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_prefix :premises (h1 h2))"#: false,
        }
        "Premise term is not an inequality of the form (not (= (str.len t_1) (str.len s_1)))" {
            r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
               (assume h2 (= (str.len "a") (str.len (str.++ "a" c))))
               (define-fun r_skolem () String (ite (>= (str.len "a") (str.len (str.++ "a" c))) (str.substr "a" (str.len (str.++ "a" c)) (- (str.len "a") (str.len (str.++ "a" c)))) (str.substr (str.++ "a" c) (str.len "a") (- (str.len (str.++ "a" c)) (str.len "a")))))
               (step t1 (cl (and (or (= "a" (str.++ "a" c r_skolem)) (= (str.++ "a" c) (str.++ "a" r_skolem))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_prefix :premises (h1 h2))"#: false,
            r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
               (assume h2 (not (= (str.to_code "a") (str.to_code (str.++ "a" c)))))
               (define-fun r_skolem () String (ite (>= (str.len "a") (str.len (str.++ "a" c))) (str.substr "a" (str.len (str.++ "a" c)) (- (str.len "a") (str.len (str.++ "a" c)))) (str.substr (str.++ "a" c) (str.len "a") (- (str.len (str.++ "a" c)) (str.len "a")))))
               (step t1 (cl (and (or (= "a" (str.++ "a" c r_skolem)) (= (str.++ "a" c) (str.++ "a" r_skolem))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_prefix :premises (h1 h2))"#: false,
        }
        "Conclusion term is not of the form (and (or (= x y) (= z w)) (not (= r \"\")) (> (str.len r) 0))" {
            r#"(assume h1 (= (str.++ a b c) (str.++ c d e)))
               (assume h2 (not (= (str.len (str.++ a b)) (str.len c))))
               (define-fun r_skolem () String (ite (>= (str.len (str.++ a b)) (str.len c)) (str.substr (str.++ a b) (str.len c) (- (str.len (str.++ a b)) (str.len c))) (str.substr c (str.len (str.++ a b)) (- (str.len c) (str.len (str.++ a b))))))
               (step t1 (cl (or (or (= (str.++ a b) (str.++ c r_skolem)) (= c (str.++ a b r_skolem))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_prefix :premises (h1 h2))"#: false,
            r#"(assume h1 (= (str.++ a b c) (str.++ c d e)))
               (assume h2 (not (= (str.len (str.++ a b)) (str.len c))))
               (define-fun r_skolem () String (ite (>= (str.len (str.++ a b)) (str.len c)) (str.substr (str.++ a b) (str.len c) (- (str.len (str.++ a b)) (str.len c))) (str.substr c (str.len (str.++ a b)) (- (str.len c) (str.len (str.++ a b))))))
               (step t1 (cl (and (and (= (str.++ a b) (str.++ c r_skolem)) (= c (str.++ a b r_skolem))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_prefix :premises (h1 h2))"#: false,
            r#"(assume h1 (= (str.++ a b c) (str.++ c d e)))
               (assume h2 (not (= (str.len (str.++ a b)) (str.len c))))
               (define-fun r_skolem () String (ite (>= (str.len (str.++ a b)) (str.len c)) (str.substr (str.++ a b) (str.len c) (- (str.len (str.++ a b)) (str.len c))) (str.substr c (str.len (str.++ a b)) (- (str.len c) (str.len (str.++ a b))))))
               (step t1 (cl (and (or (not (= (str.++ a b) (str.++ c r_skolem))) (not (= c (str.++ a b r_skolem)))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_prefix :premises (h1 h2))"#: false,
            r#"(assume h1 (= (str.++ a b c) (str.++ c d e)))
               (assume h2 (not (= (str.len (str.++ a b)) (str.len c))))
               (define-fun r_skolem () String (ite (>= (str.len (str.++ a b)) (str.len c)) (str.substr (str.++ a b) (str.len c) (- (str.len (str.++ a b)) (str.len c))) (str.substr c (str.len (str.++ a b)) (- (str.len c) (str.len (str.++ a b))))))
               (step t1 (cl (and (or (= (str.++ a b) (str.++ c r_skolem)) (= c (str.++ a b r_skolem))) (= r_skolem "") (> (str.len r_skolem) 0))) :rule concat_split_prefix :premises (h1 h2))"#: false,
            r#"(assume h1 (= (str.++ a b c) (str.++ c d e)))
               (assume h2 (not (= (str.len (str.++ a b)) (str.len c))))
               (define-fun r_skolem () String (ite (>= (str.len (str.++ a b)) (str.len c)) (str.substr (str.++ a b) (str.len c) (- (str.len (str.++ a b)) (str.len c))) (str.substr c (str.len (str.++ a b)) (- (str.len c) (str.len (str.++ a b))))))
               (step t1 (cl (and (or (= (str.++ a b) (str.++ c r_skolem)) (= c (str.++ a b r_skolem))) (not (= r_skolem "")) (> (str.len r_skolem) 1))) :rule concat_split_prefix :premises (h1 h2))"#: false,
            r#"(assume h1 (= (str.++ a b c) (str.++ c d e)))
               (assume h2 (not (= (str.len (str.++ a b)) (str.len c))))
               (define-fun r_skolem () String (ite (>= (str.len (str.++ a b)) (str.len c)) (str.substr (str.++ a b) (str.len c) (- (str.len (str.++ a b)) (str.len c))) (str.substr c (str.len (str.++ a b)) (- (str.len c) (str.len (str.++ a b))))))
               (step t1 (cl (and (or (= (str.++ a b) (str.++ c r_skolem)) (= c (str.++ a b r_skolem))) (not (= r_skolem "")) (< (str.len r_skolem) 0))) :rule concat_split_prefix :premises (h1 h2))"#: false,
        }
    }
}

#[test]
fn concat_split_suffix() {
    test_cases! {
        definitions = "
            (declare-fun a () String)
            (declare-fun b () String)
            (declare-fun c () String)
            (declare-fun d () String)
            (declare-fun e () String)
        ",
        "Simple working examples" {
            r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
               (assume h2 (not (= (str.len (str.++ "b" b)) (str.len c))))
               (define-fun r_skolem () String (ite (>= (str.len (str.++ "b" b)) (str.len c)) (str.substr (str.++ "b" b) 0 (- (str.len (str.++ "b" b)) (str.len c))) (str.substr c 0 (- (str.len c) (str.len (str.++ "b" b))))))
               (step t1 (cl (and (or (= (str.++ "b" b) (str.++ r_skolem c)) (= c (str.++ r_skolem (str.++ "b" b)))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_suffix :premises (h1 h2))"#: true,
            r#"(assume h1 (= (str.++ a b c d) (str.++ b c d e)))
               (assume h2 (not (= (str.len (str.++ c d)) (str.len (str.++ c d e)))))
               (define-fun r_skolem () String (ite (>= (str.len (str.++ c d)) (str.len (str.++ c d e))) (str.substr (str.++ c d) 0 (- (str.len (str.++ c d)) (str.len (str.++ c d e)))) (str.substr (str.++ c d e) 0 (- (str.len (str.++ c d e)) (str.len (str.++ c d))))))
               (step t1 (cl (and (or (= (str.++ c d) (str.++ r_skolem (str.++ c d e))) (= (str.++ c d e) (str.++ r_skolem (str.++ c d)))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_suffix :premises (h1 h2))"#: true,
        }
        "The term of the second premise is not a suffix of the first one" {
            r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
               (assume h2 (not (= (str.len (str.++ b "b")) (str.len c))))
               (define-fun r_skolem () String (ite (>= (str.len (str.++ "b" b)) (str.len c)) (str.substr (str.++ "b" b) 0 (- (str.len (str.++ "b" b)) (str.len c))) (str.substr c 0 (- (str.len c) (str.len (str.++ "b" b))))))
               (step t1 (cl (and (or (= (str.++ "b" b) (str.++ r_skolem c)) (= c (str.++ r_skolem (str.++ "b" b)))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_suffix :premises (h1 h2))"#: false,
            r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
               (assume h2 (not (= (str.len (str.++ "b" b)) (str.len "a"))))
               (define-fun r_skolem () String (ite (>= (str.len (str.++ "b" b)) (str.len c)) (str.substr (str.++ "b" b) 0 (- (str.len (str.++ "b" b)) (str.len c))) (str.substr c 0 (- (str.len c) (str.len (str.++ "b" b))))))
               (step t1 (cl (and (or (= (str.++ "b" b) (str.++ r_skolem c)) (= c (str.++ r_skolem (str.++ "b" b)))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_suffix :premises (h1 h2))"#: false,
        }
        "Terms are not str.++ applications" {
            r#"(assume h1 (= "" (str.++ "a" c)))
               (assume h2 (not (= (str.len (str.++ "b" b)) (str.len c))))
               (define-fun r_skolem () String (ite (>= (str.len (str.++ "b" b)) (str.len c)) (str.substr (str.++ "b" b) 0 (- (str.len (str.++ "b" b)) (str.len c))) (str.substr c 0 (- (str.len c) (str.len (str.++ "b" b))))))
               (step t1 (cl (and (or (= (str.++ "b" b) (str.++ r_skolem c)) (= c (str.++ r_skolem (str.++ "b" b)))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_suffix :premises (h1 h2))"#: false,
            r#"(assume h1 (= (str.++ "a" "b" b) ""))
               (assume h2 (not (= (str.len (str.++ "b" b)) (str.len c))))
               (define-fun r_skolem () String (ite (>= (str.len (str.++ "b" b)) (str.len c)) (str.substr (str.++ "b" b) 0 (- (str.len (str.++ "b" b)) (str.len c))) (str.substr c 0 (- (str.len c) (str.len (str.++ "b" b))))))
               (step t1 (cl (and (or (= (str.++ "b" b) (str.++ r_skolem c)) (= c (str.++ r_skolem (str.++ "b" b)))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_suffix :premises (h1 h2))"#: false,
        }
        "Premise term is not an equality" {
            r#"(assume h1 (not (= (str.++ a b c d) (str.++ b c d e))))
               (assume h2 (not (= (str.len (str.++ c d)) (str.len (str.++ c d e)))))
               (define-fun r_skolem () String (ite (>= (str.len (str.++ c d)) (str.len (str.++ c d e))) (str.substr (str.++ c d) 0 (- (str.len (str.++ c d)) (str.len (str.++ c d e)))) (str.substr (str.++ c d e) 0 (- (str.len (str.++ c d e)) (str.len (str.++ c d))))))
               (step t1 (cl (and (or (= (str.++ c d) (str.++ r_skolem (str.++ c d e))) (= (str.++ c d e) (str.++ r_skolem (str.++ c d)))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_suffix :premises (h1 h2))"#: false,
        }
        "Premise term is not an inequality of the form (not (= (str.len t_2) (str.len s_2)))" {
            r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
               (assume h2 (= (str.len (str.++ "b" b)) (str.len c)))
               (define-fun r_skolem () String (ite (>= (str.len (str.++ "b" b)) (str.len c)) (str.substr (str.++ "b" b) 0 (- (str.len (str.++ "b" b)) (str.len c))) (str.substr c 0 (- (str.len c) (str.len (str.++ "b" b))))))
               (step t1 (cl (and (or (= (str.++ "b" b) (str.++ r_skolem c)) (= c (str.++ r_skolem (str.++ "b" b)))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_suffix :premises (h1 h2))"#: false,
            r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
               (assume h2 (not (= (str.to_code (str.++ "b" b)) (str.to_code c))))
               (define-fun r_skolem () String (ite (>= (str.len (str.++ "b" b)) (str.len c)) (str.substr (str.++ "b" b) 0 (- (str.len (str.++ "b" b)) (str.len c))) (str.substr c 0 (- (str.len c) (str.len (str.++ "b" b))))))
               (step t1 (cl (and (or (= (str.++ "b" b) (str.++ r_skolem c)) (= c (str.++ r_skolem (str.++ "b" b)))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_suffix :premises (h1 h2))"#: false,
        }
        "Conclusion term is not of the form (and (or (= x y) (= z w)) (not (= r \"\")) (> (str.len r) 0))" {
            r#"(assume h1 (= (str.++ a b c d) (str.++ b c d e)))
               (assume h2 (not (= (str.len (str.++ c d)) (str.len (str.++ c d e)))))
               (define-fun r_skolem () String (ite (>= (str.len (str.++ c d)) (str.len (str.++ c d e))) (str.substr (str.++ c d) 0 (- (str.len (str.++ c d)) (str.len (str.++ c d e)))) (str.substr (str.++ c d e) 0 (- (str.len (str.++ c d e)) (str.len (str.++ c d))))))
               (step t1 (cl (or (or (= (str.++ c d) (str.++ r_skolem (str.++ c d e))) (= (str.++ c d e) (str.++ r_skolem (str.++ c d)))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_suffix :premises (h1 h2))"#: false,
            r#"(assume h1 (= (str.++ a b c d) (str.++ b c d e)))
               (assume h2 (not (= (str.len (str.++ c d)) (str.len (str.++ c d e)))))
               (define-fun r_skolem () String (ite (>= (str.len (str.++ c d)) (str.len (str.++ c d e))) (str.substr (str.++ c d) 0 (- (str.len (str.++ c d)) (str.len (str.++ c d e)))) (str.substr (str.++ c d e) 0 (- (str.len (str.++ c d e)) (str.len (str.++ c d))))))
               (step t1 (cl (and (and (= (str.++ c d) (str.++ r_skolem (str.++ c d e))) (= (str.++ c d e) (str.++ r_skolem (str.++ c d)))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_suffix :premises (h1 h2))"#: false,
            r#"(assume h1 (= (str.++ a b c d) (str.++ b c d e)))
               (assume h2 (not (= (str.len (str.++ c d)) (str.len (str.++ c d e)))))
               (define-fun r_skolem () String (ite (>= (str.len (str.++ c d)) (str.len (str.++ c d e))) (str.substr (str.++ c d) 0 (- (str.len (str.++ c d)) (str.len (str.++ c d e)))) (str.substr (str.++ c d e) 0 (- (str.len (str.++ c d e)) (str.len (str.++ c d))))))
               (step t1 (cl (and (or (= (str.++ c d) (str.++ r_skolem (str.++ c d e))) (not (= (str.++ c d e) (str.++ r_skolem (str.++ c d))))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_suffix :premises (h1 h2))"#: false,
            r#"(assume h1 (= (str.++ a b c d) (str.++ b c d e)))
               (assume h2 (not (= (str.len (str.++ c d)) (str.len (str.++ c d e)))))
               (define-fun r_skolem () String (ite (>= (str.len (str.++ c d)) (str.len (str.++ c d e))) (str.substr (str.++ c d) 0 (- (str.len (str.++ c d)) (str.len (str.++ c d e)))) (str.substr (str.++ c d e) 0 (- (str.len (str.++ c d e)) (str.len (str.++ c d))))))
               (step t1 (cl (and (or (= (str.++ c d) (str.++ r_skolem (str.++ c d e))) (= (str.++ c d e) (str.++ r_skolem (str.++ c d)))) (= r_skolem "") (> (str.len r_skolem) 0))) :rule concat_split_suffix :premises (h1 h2))"#: false,
            r#"(assume h1 (= (str.++ a b c d) (str.++ b c d e)))
               (assume h2 (not (= (str.len (str.++ c d)) (str.len (str.++ c d e)))))
               (define-fun r_skolem () String (ite (>= (str.len (str.++ c d)) (str.len (str.++ c d e))) (str.substr (str.++ c d) 0 (- (str.len (str.++ c d)) (str.len (str.++ c d e)))) (str.substr (str.++ c d e) 0 (- (str.len (str.++ c d e)) (str.len (str.++ c d))))))
               (step t1 (cl (and (or (= (str.++ c d) (str.++ r_skolem (str.++ c d e))) (= (str.++ c d e) (str.++ r_skolem (str.++ c d)))) (not (= r_skolem "")) (> (str.len r_skolem) 1))) :rule concat_split_suffix :premises (h1 h2))"#: false,
            r#"(assume h1 (= (str.++ a b c d) (str.++ b c d e)))
               (assume h2 (not (= (str.len (str.++ c d)) (str.len (str.++ c d e)))))
               (define-fun r_skolem () String (ite (>= (str.len (str.++ c d)) (str.len (str.++ c d e))) (str.substr (str.++ c d) 0 (- (str.len (str.++ c d)) (str.len (str.++ c d e)))) (str.substr (str.++ c d e) 0 (- (str.len (str.++ c d e)) (str.len (str.++ c d))))))
               (step t1 (cl (and (or (= (str.++ c d) (str.++ r_skolem (str.++ c d e))) (= (str.++ c d e) (str.++ r_skolem (str.++ c d)))) (not (= r_skolem "")) (< (str.len r_skolem) 0))) :rule concat_split_suffix :premises (h1 h2))"#: false,
        }
    }
}

#[test]
fn concat_lprop_prefix() {
    test_cases! {
        definitions = "
            (declare-fun a () String)
            (declare-fun b () String)
            (declare-fun c () String)
            (declare-fun d () String)
        ",
        "Simple working examples" {
            r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
               (assume h2 (> (str.len (str.++ "a" "b")) (str.len "a")))
               (define-fun r_skolem () String (ite (>= (str.len (str.++ "a" "b")) (str.len "a")) (str.substr (str.++ "a" "b") (str.len "a") (- (str.len (str.++ "a" "b")) (str.len "a"))) (str.substr "a" (str.len (str.++ "a" "b")) (- (str.len "a") (str.len (str.++ "a" "b"))))))
               (step t1 (cl (and (= (str.++ "a" "b") (str.++ "a" r_skolem)) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_lprop_prefix :premises (h1 h2))"#: true,
            r#"(assume h1 (= (str.++ d c b a) (str.++ "d" b (str.++ c "a"))))
               (assume h2 (> (str.len (str.++ d c b)) (str.len (str.++ "d" b))))
               (define-fun r_skolem () String (ite (>= (str.len (str.++ d c b)) (str.len (str.++ "d" b))) (str.substr (str.++ d c b) (str.len (str.++ "d" b)) (- (str.len (str.++ d c b)) (str.len (str.++ "d" b)))) (str.substr (str.++ "d" b) (str.len (str.++ d c b)) (- (str.len (str.++ "d" b)) (str.len (str.++ d c b))))))
               (step t1 (cl (and (= (str.++ d c b) (str.++ "d" b r_skolem)) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_lprop_prefix :premises (h1 h2))"#: true,
        }
        "The term of the second premise is not a prefix of the first one" {
            r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
               (assume h2 (> (str.len (str.++ "a" b)) (str.len "a")))
               (define-fun r_skolem () String (ite (>= (str.len (str.++ "a" "b")) (str.len "a")) (str.substr (str.++ "a" "b") (str.len "a") (- (str.len (str.++ "a" "b")) (str.len "a"))) (str.substr "a" (str.len (str.++ "a" "b")) (- (str.len "a") (str.len (str.++ "a" "b"))))))
               (step t1 (cl (and (= (str.++ "a" "b") (str.++ "a" r_skolem)) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_lprop_prefix :premises (h1 h2))"#: false,
            r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
               (assume h2 (> (str.len (str.++ "a" "b")) (str.len c)))
               (define-fun r_skolem () String (ite (>= (str.len (str.++ "a" "b")) (str.len "a")) (str.substr (str.++ "a" "b") (str.len "a") (- (str.len (str.++ "a" "b")) (str.len "a"))) (str.substr "a" (str.len (str.++ "a" "b")) (- (str.len "a") (str.len (str.++ "a" "b"))))))
               (step t1 (cl (and (= (str.++ "a" "b") (str.++ "a" r_skolem)) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_lprop_prefix :premises (h1 h2))"#: false,
        }
        "Term are not a str.++ application" {
            r#"(assume h1 (= "" (str.++ "d" b (str.++ c "a"))))
               (assume h2 (> (str.len (str.++ d c b)) (str.len (str.++ "d" b))))
               (define-fun r_skolem () String (ite (>= (str.len (str.++ d c b)) (str.len (str.++ "d" b))) (str.substr (str.++ d c b) (str.len (str.++ "d" b)) (- (str.len (str.++ d c b)) (str.len (str.++ "d" b)))) (str.substr (str.++ "d" b) (str.len (str.++ d c b)) (- (str.len (str.++ "d" b)) (str.len (str.++ d c b))))))
               (step t1 (cl (and (= (str.++ d c b) (str.++ "d" b r_skolem)) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_lprop_prefix :premises (h1 h2))"#: false,
            r#"(assume h1 (= (str.++ d c b a) ""))
               (assume h2 (> (str.len (str.++ d c b)) (str.len (str.++ "d" b))))
               (define-fun r_skolem () String (ite (>= (str.len (str.++ d c b)) (str.len (str.++ "d" b))) (str.substr (str.++ d c b) (str.len (str.++ "d" b)) (- (str.len (str.++ d c b)) (str.len (str.++ "d" b)))) (str.substr (str.++ "d" b) (str.len (str.++ d c b)) (- (str.len (str.++ "d" b)) (str.len (str.++ d c b))))))
               (step t1 (cl (and (= (str.++ d c b) (str.++ "d" b r_skolem)) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_lprop_prefix :premises (h1 h2))"#: false,
        }
        "Premise term is not an equality" {
            r#"(assume h1 (not (= (str.++ "a" "b" b) (str.++ "a" c))))
               (assume h2 (> (str.len (str.++ "a" "b")) (str.len "a")))
               (define-fun r_skolem () String (ite (>= (str.len (str.++ "a" "b")) (str.len "a")) (str.substr (str.++ "a" "b") (str.len "a") (- (str.len (str.++ "a" "b")) (str.len "a"))) (str.substr "a" (str.len (str.++ "a" "b")) (- (str.len "a") (str.len (str.++ "a" "b"))))))
               (step t1 (cl (and (= (str.++ "a" "b") (str.++ "a" r_skolem)) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_lprop_prefix :premises (h1 h2))"#: false,
        }
        "Premise term is not of the form (> (strlen t_1) (strlen s_1))" {
            r#"(assume h1 (= (str.++ d c b a) (str.++ "d" b (str.++ c "a"))))
               (assume h2 (< (str.len (str.++ d c b)) (str.len (str.++ "d" b))))
               (define-fun r_skolem () String (ite (>= (str.len (str.++ d c b)) (str.len (str.++ "d" b))) (str.substr (str.++ d c b) (str.len (str.++ "d" b)) (- (str.len (str.++ d c b)) (str.len (str.++ "d" b)))) (str.substr (str.++ "d" b) (str.len (str.++ d c b)) (- (str.len (str.++ "d" b)) (str.len (str.++ d c b))))))
               (step t1 (cl (and (= (str.++ d c b) (str.++ "d" b r_skolem)) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_lprop_prefix :premises (h1 h2))"#: false,
            r#"(assume h1 (= (str.++ d c b a) (str.++ "d" b (str.++ c "a"))))
               (assume h2 (> (str.to_code (str.++ d c b)) (str.to_code (str.++ "d" b))))
               (define-fun r_skolem () String (ite (>= (str.len (str.++ d c b)) (str.len (str.++ "d" b))) (str.substr (str.++ d c b) (str.len (str.++ "d" b)) (- (str.len (str.++ d c b)) (str.len (str.++ "d" b)))) (str.substr (str.++ "d" b) (str.len (str.++ d c b)) (- (str.len (str.++ "d" b)) (str.len (str.++ d c b))))))
               (step t1 (cl (and (= (str.++ d c b) (str.++ "d" b r_skolem)) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_lprop_prefix :premises (h1 h2))"#: false,
        }
        r#"Conclusion term is not of the form (and (= t_1 x) (not (= r "")) (> (str.len r) 0))"# {
            r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
               (assume h2 (> (str.len (str.++ "a" "b")) (str.len "a")))
               (define-fun r_skolem () String (ite (>= (str.len (str.++ "a" "b")) (str.len "a")) (str.substr (str.++ "a" "b") (str.len "a") (- (str.len (str.++ "a" "b")) (str.len "a"))) (str.substr "a" (str.len (str.++ "a" "b")) (- (str.len "a") (str.len (str.++ "a" "b"))))))
               (step t1 (cl (or (= (str.++ "a" "b") (str.++ "a" r_skolem)) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_lprop_prefix :premises (h1 h2))"#: false,
            r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
               (assume h2 (> (str.len (str.++ "a" "b")) (str.len "a")))
               (define-fun r_skolem () String (ite (>= (str.len (str.++ "a" "b")) (str.len "a")) (str.substr (str.++ "a" "b") (str.len "a") (- (str.len (str.++ "a" "b")) (str.len "a"))) (str.substr "a" (str.len (str.++ "a" "b")) (- (str.len "a") (str.len (str.++ "a" "b"))))))
               (step t1 (cl (and (not (= (str.++ "a" "b") (str.++ "a" r_skolem))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_lprop_prefix :premises (h1 h2))"#: false,
            r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
               (assume h2 (> (str.len (str.++ "a" "b")) (str.len "a")))
               (define-fun r_skolem () String (ite (>= (str.len (str.++ "a" "b")) (str.len "a")) (str.substr (str.++ "a" "b") (str.len "a") (- (str.len (str.++ "a" "b")) (str.len "a"))) (str.substr "a" (str.len (str.++ "a" "b")) (- (str.len "a") (str.len (str.++ "a" "b"))))))
               (step t1 (cl (and (= (str.++ "a" "b") (str.++ "a" r_skolem)) (= r_skolem "") (> (str.len r_skolem) 0))) :rule concat_lprop_prefix :premises (h1 h2))"#: false,
            r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
               (assume h2 (> (str.len (str.++ "a" "b")) (str.len "a")))
               (define-fun r_skolem () String (ite (>= (str.len (str.++ "a" "b")) (str.len "a")) (str.substr (str.++ "a" "b") (str.len "a") (- (str.len (str.++ "a" "b")) (str.len "a"))) (str.substr "a" (str.len (str.++ "a" "b")) (- (str.len "a") (str.len (str.++ "a" "b"))))))
               (step t1 (cl (and (= (str.++ "a" "b") (str.++ "a" r_skolem)) (not (= r_skolem "")) (< (str.len r_skolem) 0))) :rule concat_lprop_prefix :premises (h1 h2))"#: false,
            r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
               (assume h2 (> (str.len (str.++ "a" "b")) (str.len "a")))
               (define-fun r_skolem () String (ite (>= (str.len (str.++ "a" "b")) (str.len "a")) (str.substr (str.++ "a" "b") (str.len "a") (- (str.len (str.++ "a" "b")) (str.len "a"))) (str.substr "a" (str.len (str.++ "a" "b")) (- (str.len "a") (str.len (str.++ "a" "b"))))))
               (step t1 (cl (and (= (str.++ "a" "b") (str.++ "a" r_skolem)) (not (= r_skolem "")) (> (str.len r_skolem) 1))) :rule concat_lprop_prefix :premises (h1 h2))"#: false,
        }
    }
}

#[test]
fn concat_lprop_suffix() {
    test_cases! {
        definitions = "
            (declare-fun a () String)
            (declare-fun b () String)
            (declare-fun c () String)
            (declare-fun d () String)
        ",
        "Simple working examples" {
            r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
               (assume h2 (> (str.len (str.++ "b" b)) (str.len c)))
               (define-fun r_skolem () String (ite (>= (str.len (str.++ "b" b)) (str.len c)) (str.substr (str.++ "b" b) 0 (- (str.len (str.++ "b" b)) (str.len c))) (str.substr c 0 (- (str.len c) (str.len (str.++ "b" b))))))
               (step t1 (cl (and (= (str.++ "b" b) (str.++ r_skolem c)) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_lprop_suffix :premises (h1 h2))"#: true,
            r#"(assume h1 (= (str.++ d c b a) (str.++ "d" b (str.++ c "a"))))
               (assume h2 (> (str.len (str.++ c (str.++ b a))) (str.len (str.++ c "a"))))
               (define-fun r_skolem () String (ite (>= (str.len (str.++ c b a)) (str.len (str.++ c "a"))) (str.substr (str.++ c b a) 0 (- (str.len (str.++ c b a)) (str.len (str.++ c "a")))) (str.substr (str.++ c "a") 0 (- (str.len (str.++ c "a")) (str.len (str.++ c b a))))))
               (step t1 (cl (and (= (str.++ c (str.++ b a)) (str.++ r_skolem c "a")) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_lprop_suffix :premises (h1 h2))"#: true,
        }
        "The term of the second premise is not a suffix of the first one" {
            r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
               (assume h2 (> (str.len (str.++ b "b")) (str.len c)))
               (define-fun r_skolem () String (ite (>= (str.len (str.++ "b" b)) (str.len c)) (str.substr (str.++ "b" b) 0 (- (str.len (str.++ "b" b)) (str.len c))) (str.substr c 0 (- (str.len c) (str.len (str.++ "b" b))))))
               (step t1 (cl (and (= (str.++ "b" b) (str.++ r_skolem c)) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_lprop_suffix :premises (h1 h2))"#: false,
            r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
               (assume h2 (> (str.len (str.++ "b" b)) (str.len "a")))
               (define-fun r_skolem () String (ite (>= (str.len (str.++ "b" b)) (str.len c)) (str.substr (str.++ "b" b) 0 (- (str.len (str.++ "b" b)) (str.len c))) (str.substr c 0 (- (str.len c) (str.len (str.++ "b" b))))))
               (step t1 (cl (and (= (str.++ "b" b) (str.++ r_skolem c)) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_lprop_suffix :premises (h1 h2))"#: false,
        }
        "Term are not a str.++ application" {
            r#"(assume h1 (= "" (str.++ "d" b (str.++ c "a"))))
               (assume h2 (> (str.len (str.++ c (str.++ b a))) (str.len (str.++ c "a"))))
               (define-fun r_skolem () String (ite (>= (str.len (str.++ c b a)) (str.len (str.++ c "a"))) (str.substr (str.++ c b a) 0 (- (str.len (str.++ c b a)) (str.len (str.++ c "a")))) (str.substr (str.++ c "a") 0 (- (str.len (str.++ c "a")) (str.len (str.++ c b a))))))
               (step t1 (cl (and (= (str.++ c (str.++ b a)) (str.++ r_skolem c "a")) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_lprop_suffix :premises (h1 h2))"#: false,
            r#"(assume h1 (= (str.++ d c b a) ""))
               (assume h2 (> (str.len (str.++ c (str.++ b a))) (str.len (str.++ c "a"))))
               (define-fun r_skolem () String (ite (>= (str.len (str.++ c b a)) (str.len (str.++ c "a"))) (str.substr (str.++ c b a) 0 (- (str.len (str.++ c b a)) (str.len (str.++ c "a")))) (str.substr (str.++ c "a") 0 (- (str.len (str.++ c "a")) (str.len (str.++ c b a))))))
               (step t1 (cl (and (= (str.++ c (str.++ b a)) (str.++ r_skolem c "a")) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_lprop_suffix :premises (h1 h2))"#: false,
        }
        "Premise term is not an equality" {
            r#"(assume h1 (not (= (str.++ "a" "b" b) (str.++ "a" c))))
               (assume h2 (> (str.len (str.++ "b" b)) (str.len c)))
               (define-fun r_skolem () String (ite (>= (str.len (str.++ "b" b)) (str.len c)) (str.substr (str.++ "b" b) 0 (- (str.len (str.++ "b" b)) (str.len c))) (str.substr c 0 (- (str.len c) (str.len (str.++ "b" b))))))
               (step t1 (cl (and (= (str.++ "b" b) (str.++ r_skolem c)) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_lprop_suffix :premises (h1 h2))"#: false,
        }
        "Premise term is not of the form (> (strlen t_2) (strlen s_2))" {
            r#"(assume h1 (= (str.++ d c b a) (str.++ "d" b (str.++ c "a"))))
               (assume h2 (< (str.len (str.++ c (str.++ b a))) (str.len (str.++ c "a"))))
               (define-fun r_skolem () String (ite (>= (str.len (str.++ c b a)) (str.len (str.++ c "a"))) (str.substr (str.++ c b a) 0 (- (str.len (str.++ c b a)) (str.len (str.++ c "a")))) (str.substr (str.++ c "a") 0 (- (str.len (str.++ c "a")) (str.len (str.++ c b a))))))
               (step t1 (cl (and (= (str.++ c (str.++ b a)) (str.++ r_skolem c "a")) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_lprop_suffix :premises (h1 h2))"#: false,
            r#"(assume h1 (= (str.++ d c b a) (str.++ "d" b (str.++ c "a"))))
               (assume h2 (> (str.to_code (str.++ c (str.++ b a))) (str.to_code (str.++ c "a"))))
               (define-fun r_skolem () String (ite (>= (str.len (str.++ c b a)) (str.len (str.++ c "a"))) (str.substr (str.++ c b a) 0 (- (str.len (str.++ c b a)) (str.len (str.++ c "a")))) (str.substr (str.++ c "a") 0 (- (str.len (str.++ c "a")) (str.len (str.++ c b a))))))
               (step t1 (cl (and (= (str.++ c (str.++ b a)) (str.++ r_skolem c "a")) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_lprop_suffix :premises (h1 h2))"#: false,
        }
        r#"Conclusion term is not of the form (and (= t_2 x) (not (= r "")) (> (str.len r) 0))"# {
            r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
               (assume h2 (> (str.len (str.++ "b" b)) (str.len c)))
               (define-fun r_skolem () String (ite (>= (str.len (str.++ "b" b)) (str.len c)) (str.substr (str.++ "b" b) 0 (- (str.len (str.++ "b" b)) (str.len c))) (str.substr c 0 (- (str.len c) (str.len (str.++ "b" b))))))
               (step t1 (cl (or (= (str.++ "b" b) (str.++ r_skolem c)) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_lprop_suffix :premises (h1 h2))"#: false,
            r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
               (assume h2 (> (str.len (str.++ "b" b)) (str.len c)))
               (define-fun r_skolem () String (ite (>= (str.len (str.++ "b" b)) (str.len c)) (str.substr (str.++ "b" b) 0 (- (str.len (str.++ "b" b)) (str.len c))) (str.substr c 0 (- (str.len c) (str.len (str.++ "b" b))))))
               (step t1 (cl (and (not (= (str.++ "b" b) (str.++ r_skolem c))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_lprop_suffix :premises (h1 h2))"#: false,
            r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
               (assume h2 (> (str.len (str.++ "b" b)) (str.len c)))
               (define-fun r_skolem () String (ite (>= (str.len (str.++ "b" b)) (str.len c)) (str.substr (str.++ "b" b) 0 (- (str.len (str.++ "b" b)) (str.len c))) (str.substr c 0 (- (str.len c) (str.len (str.++ "b" b))))))
               (step t1 (cl (and (= (str.++ "b" b) (str.++ r_skolem c)) (= r_skolem "") (> (str.len r_skolem) 0))) :rule concat_lprop_suffix :premises (h1 h2))"#: false,
            r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
               (assume h2 (> (str.len (str.++ "b" b)) (str.len c)))
               (define-fun r_skolem () String (ite (>= (str.len (str.++ "b" b)) (str.len c)) (str.substr (str.++ "b" b) 0 (- (str.len (str.++ "b" b)) (str.len c))) (str.substr c 0 (- (str.len c) (str.len (str.++ "b" b))))))
               (step t1 (cl (and (= (str.++ "b" b) (str.++ r_skolem c)) (not (= r_skolem "")) (< (str.len r_skolem) 0))) :rule concat_lprop_suffix :premises (h1 h2))"#: false,
            r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
               (assume h2 (> (str.len (str.++ "b" b)) (str.len c)))
               (define-fun r_skolem () String (ite (>= (str.len (str.++ "b" b)) (str.len c)) (str.substr (str.++ "b" b) 0 (- (str.len (str.++ "b" b)) (str.len c))) (str.substr c 0 (- (str.len c) (str.len (str.++ "b" b))))))
               (step t1 (cl (and (= (str.++ "b" b) (str.++ r_skolem c)) (not (= r_skolem "")) (> (str.len r_skolem) 1))) :rule concat_lprop_suffix :premises (h1 h2))"#: false,
        }
    }
}

#[test]
fn concat_cprop_prefix() {
    test_cases! {
        definitions = "
            (declare-fun a () String)
            (declare-fun b () String)
            (declare-fun c () String)
            (declare-fun d () String)
            (declare-fun e () String)
        ",
        "Simple working examples" {
            r#"(assume h1 (= (str.++ a "bc" d) (str.++ "aabc" e)))
               (assume h2 (not (= (str.len a) 0)))
               (step t1 (cl (= a (str.++ (str.substr "aabc" 0 2) (str.substr a (str.len (str.substr "aabc" 0 2)) (- (str.len a) (str.len (str.substr "aabc" 0 2))))))) :rule concat_cprop_prefix :premises (h1 h2))"#: true,
            r#"(assume h1 (= (str.++ d "dcba" e) "acda"))
               (assume h2 (not (= (str.len d) 0)))
               (step t1 (cl (= d (str.++ (str.substr "acda" 0 3) (str.substr d (str.len (str.substr "acda" 0 3)) (- (str.len d) (str.len (str.substr "acda" 0 3))))))) :rule concat_cprop_prefix :premises (h1 h2))"#: true,
        }
        "Term is not a str.++ application" {
            r#"(assume h1 (= a (str.++ "aabc" e)))
               (assume h2 (not (= (str.len a) 0)))
               (step t1 (cl (= a (str.++ (str.substr "aabc" 0 2) (str.substr a (str.len (str.substr "aabc" 0 2)) (- (str.len a) (str.len (str.substr "aabc" 0 2))))))) :rule concat_cprop_prefix :premises (h1 h2))"#: false,
            r#"(assume h1 (= "abc" (str.++ "aabc" e)))
               (assume h2 (not (= (str.len a) 0)))
               (step t1 (cl (= a (str.++ (str.substr "aabc" 0 2) (str.substr a (str.len (str.substr "aabc" 0 2)) (- (str.len a) (str.len (str.substr "aabc" 0 2))))))) :rule concat_cprop_prefix :premises (h1 h2))"#: false,
        }
        "Term is not a str.++ application with 3 arguments" {
            r#"(assume h1 (= (str.++ "dcba" e) "acda"))
               (assume h2 (not (= (str.len d) 0)))
               (step t1 (cl (= d (str.++ (str.substr "acda" 0 3) (str.substr d (str.len (str.substr "acda" 0 3)) (- (str.len d) (str.len (str.substr "acda" 0 3))))))) :rule concat_cprop_prefix :premises (h1 h2))"#: false,
            r#"(assume h1 (= (str.++ a b "dcba" e) "acda"))
               (assume h2 (not (= (str.len d) 0)))
               (step t1 (cl (= d (str.++ (str.substr "acda" 0 3) (str.substr d (str.len (str.substr "acda" 0 3)) (- (str.len d) (str.len (str.substr "acda" 0 3))))))) :rule concat_cprop_prefix :premises (h1 h2))"#: false,
        }
        "Term is not a String constant or a str.++ application" {
            r#"(assume h1 (= (str.++ a "bc" d) a))
               (assume h2 (not (= (str.len a) 0)))
               (step t1 (cl (= a (str.++ (str.substr "aabc" 0 2) (str.substr a (str.len (str.substr "aabc" 0 2)) (- (str.len a) (str.len (str.substr "aabc" 0 2))))))) :rule concat_cprop_prefix :premises (h1 h2))"#: false,
            r#"(assume h1 (= (str.++ a "bc" d) ""))
               (assume h2 (not (= (str.len a) 0)))
               (step t1 (cl (= a (str.++ (str.substr "aabc" 0 2) (str.substr a (str.len (str.substr "aabc" 0 2)) (- (str.len a) (str.len (str.substr "aabc" 0 2))))))) :rule concat_cprop_prefix :premises (h1 h2))"#: false,
        }
        "Premise term is not an equality" {
            r#"(assume h1 (not(= (str.++ d "dcba" e) "acda")))
               (assume h2 (not (= (str.len d) 0)))
               (step t1 (cl (= d (str.++ (str.substr "acda" 0 3) (str.substr d (str.len (str.substr "acda" 0 3)) (- (str.len d) (str.len (str.substr "acda" 0 3))))))) :rule concat_cprop_prefix :premises (h1 h2))"#: false,
        }
        "Premise term is not of the form (not (= (str.len t_1) 0))" {
            r#"(assume h1 (= (str.++ d "dcba" e) "acda"))
               (assume h2 (= (str.len d) 0))
               (step t1 (cl (= d (str.++ (str.substr "acda" 0 3) (str.substr d (str.len (str.substr "acda" 0 3)) (- (str.len d) (str.len (str.substr "acda" 0 3))))))) :rule concat_cprop_prefix :premises (h1 h2))"#: false,
            r#"(assume h1 (= (str.++ d "dcba" e) "acda"))
               (assume h2 (not (> (str.len d) 0)))
               (step t1 (cl (= d (str.++ (str.substr "acda" 0 3) (str.substr d (str.len (str.substr "acda" 0 3)) (- (str.len d) (str.len (str.substr "acda" 0 3))))))) :rule concat_cprop_prefix :premises (h1 h2))"#: false,
            r#"(assume h1 (= (str.++ d "dcba" e) "acda"))
               (assume h2 (not (= (str.to_code d) 0)))
               (step t1 (cl (= d (str.++ (str.substr "acda" 0 3) (str.substr d (str.len (str.substr "acda" 0 3)) (- (str.len d) (str.len (str.substr "acda" 0 3))))))) :rule concat_cprop_prefix :premises (h1 h2))"#: false,
            r#"(assume h1 (= (str.++ d "dcba" e) "acda"))
               (assume h2 (not (> (str.len d) 1)))
               (step t1 (cl (= d (str.++ (str.substr "acda" 0 3) (str.substr d (str.len (str.substr "acda" 0 3)) (- (str.len d) (str.len (str.substr "acda" 0 3))))))) :rule concat_cprop_prefix :premises (h1 h2))"#: false,
        }
        "Term shared between the premises is not the same" {
            r#"(assume h1 (= (str.++ a "bc" d) (str.++ "aabc" e)))
               (assume h2 (not (= (str.len b) 0)))
               (step t1 (cl (= a (str.++ (str.substr "aabc" 0 2) (str.substr a (str.len (str.substr "aabc" 0 2)) (- (str.len a) (str.len (str.substr "aabc" 0 2))))))) :rule concat_cprop_prefix :premises (h1 h2))"#: false,
            r#"(assume h1 (= (str.++ (str.++ "ab" "c") "bc" d) (str.++ "aabc" e)))
               (assume h2 (not (= (str.len "abc") 0)))
               (step t1 (cl (= a (str.++ (str.substr "aabc" 0 2) (str.substr a (str.len (str.substr "aabc" 0 2)) (- (str.len a) (str.len (str.substr "aabc" 0 2))))))) :rule concat_cprop_prefix :premises (h1 h2))"#: false,
        }
        "Conclusion term is not of the form (= t_1 (str.++ t_3 r))" {
            r#"(assume h1 (= (str.++ d "dcba" e) "acda"))
               (assume h2 (not (= (str.len d) 0)))
               (step t1 (cl (= a (str.++ (str.substr "acda" 0 3) (str.substr d (str.len (str.substr "acda" 0 3)) (- (str.len d) (str.len (str.substr "acda" 0 3))))))) :rule concat_cprop_prefix :premises (h1 h2))"#: false,
            r#"(assume h1 (= (str.++ d "dcba" e) "acda"))
               (assume h2 (not (= (str.len d) 0)))
               (step t1 (cl (not (= d (str.++ (str.substr "acda" 0 3) (str.substr d (str.len (str.substr "acda" 0 3)) (- (str.len d) (str.len (str.substr "acda" 0 3)))))))) :rule concat_cprop_prefix :premises (h1 h2))"#: false,
            r#"(assume h1 (= (str.++ d "dcba" e) "acda"))
               (assume h2 (not (= (str.len d) 0)))
               (step t1 (cl (= a (str.++ a (str.substr "acda" 0 3) (str.substr d (str.len (str.substr "acda" 0 3)) (- (str.len d) (str.len (str.substr "acda" 0 3))))))) :rule concat_cprop_prefix :premises (h1 h2))"#: false,
            r#"(assume h1 (= (str.++ d "dcba" e) "acda"))
               (assume h2 (not (= (str.len d) 0)))
               (step t1 (cl (= a (str.substr d (str.len (str.substr "acda" 0 3)) (- (str.len d) (str.len (str.substr "acda" 0 3)))))) :rule concat_cprop_prefix :premises (h1 h2))"#: false,
        }
    }
}

#[test]
fn concat_cprop_suffix() {
    test_cases! {
        definitions = "
            (declare-fun a () String)
            (declare-fun b () String)
            (declare-fun c () String)
            (declare-fun d () String)
            (declare-fun e () String)
        ",
        "Simple working examples" {
            r#"(assume h1 (= (str.++ a "bc" d) (str.++ e "aabc")))
               (assume h2 (not (= (str.len d) 0)))
               (step t1 (cl (= d (str.++ (str.substr d 0 (- (str.len d) (str.len (str.substr "aabc" (- (str.len "aabc") 3) 3)))) (str.substr "aabc" (- (str.len "aabc") 3) 3)))) :rule concat_cprop_suffix :premises (h1 h2))"#: true,
            r#"(assume h1 (= (str.++ d "dcba" (str.++ a b)) "acda"))
               (assume h2 (not (= (str.len (str.++ a b)) 0)))
               (step t1 (cl (= (str.++ a b) (str.++ (str.substr (str.++ a b) 0 (- (str.len (str.++ a b)) (str.len (str.substr "acda" (- (str.len "acda") 3) 3)))) (str.substr "acda" (- (str.len "acda") 3) 3)))) :rule concat_cprop_suffix :premises (h1 h2))"#: true,
        }
        "Term is not a str.++ application" {
            r#"(assume h1 (= b (str.++ e "aabc")))
               (assume h2 (not (= (str.len d) 0)))
               (step t1 (cl (= d (str.++ (str.substr d 0 (- (str.len d) (str.len (str.substr "aabc" (- (str.len "aabc") 3) 3)))) (str.substr "aabc" (- (str.len "aabc") 3) 3)))) :rule concat_cprop_suffix :premises (h1 h2))"#: false,
            r#"(assume h1 (= "abcd" (str.++ e "aabc")))
               (assume h2 (not (= (str.len d) 0)))
               (step t1 (cl (= d (str.++ (str.substr d 0 (- (str.len d) (str.len (str.substr "aabc" (- (str.len "aabc") 3) 3)))) (str.substr "aabc" (- (str.len "aabc") 3) 3)))) :rule concat_cprop_suffix :premises (h1 h2))"#: false,
        }
        "Term is not a str.++ application with 3 arguments" {
            r#"(assume h1 (= (str.++ "dcba" (str.++ a b)) "acda"))
               (assume h2 (not (= (str.len (str.++ a b)) 0)))
               (step t1 (cl (= (str.++ a b) (str.++ (str.substr (str.++ a b) 0 (- (str.len (str.++ a b)) (str.len (str.substr "acda" (- (str.len "acda") 3) 3)))) (str.substr "acda" (- (str.len "acda") 3) 3)))) :rule concat_cprop_suffix :premises (h1 h2))"#: false,
            r#"(assume h1 (= (str.++ "abc" d "dcba" (str.++ a b)) "acda"))
               (assume h2 (not (= (str.len (str.++ a b)) 0)))
               (step t1 (cl (= (str.++ a b) (str.++ (str.substr (str.++ a b) 0 (- (str.len (str.++ a b)) (str.len (str.substr "acda" (- (str.len "acda") 3) 3)))) (str.substr "acda" (- (str.len "acda") 3) 3)))) :rule concat_cprop_suffix :premises (h1 h2))"#: false,
        }
        "Term is not a String constant or a str.++ application" {
            r#"(assume h1 (= (str.++ a "bc" d) b))
               (assume h2 (not (= (str.len d) 0)))
               (step t1 (cl (= d (str.++ (str.substr d 0 (- (str.len d) (str.len (str.substr "aabc" (- (str.len "aabc") 3) 3)))) (str.substr "aabc" (- (str.len "aabc") 3) 3)))) :rule concat_cprop_suffix :premises (h1 h2))"#: false,
            r#"(assume h1 (= (str.++ a "bc" d) ""))
               (assume h2 (not (= (str.len d) 0)))
               (step t1 (cl (= d (str.++ (str.substr d 0 (- (str.len d) (str.len (str.substr "aabc" (- (str.len "aabc") 3) 3)))) (str.substr "aabc" (- (str.len "aabc") 3) 3)))) :rule concat_cprop_suffix :premises (h1 h2))"#: false,
        }
        "Premise term is not an equality" {
            r#"(assume h1 (not (= (str.++ d "dcba" (str.++ a b)) "acda")))
               (assume h2 (not (= (str.len (str.++ a b)) 0)))
               (step t1 (cl (= (str.++ a b) (str.++ (str.substr (str.++ a b) 0 (- (str.len (str.++ a b)) (str.len (str.substr "acda" (- (str.len "acda") 3) 3)))) (str.substr "acda" (- (str.len "acda") 3) 3)))) :rule concat_cprop_suffix :premises (h1 h2))"#: false,
        }
        "Premise term is not of the form (not (= (str.len t_2) 0))" {
            r#"(assume h1 (= (str.++ a "bc" d) (str.++ e "aabc")))
               (assume h2 (= (str.len d) 0))
               (step t1 (cl (= d (str.++ (str.substr d 0 (- (str.len d) (str.len (str.substr "aabc" (- (str.len "aabc") 3) 3)))) (str.substr "aabc" (- (str.len "aabc") 3) 3)))) :rule concat_cprop_suffix :premises (h1 h2))"#: false,
            r#"(assume h1 (= (str.++ a "bc" d) (str.++ e "aabc")))
               (assume h2 (not (> (str.len d) 0)))
               (step t1 (cl (= d (str.++ (str.substr d 0 (- (str.len d) (str.len (str.substr "aabc" (- (str.len "aabc") 3) 3)))) (str.substr "aabc" (- (str.len "aabc") 3) 3)))) :rule concat_cprop_suffix :premises (h1 h2))"#: false,
            r#"(assume h1 (= (str.++ a "bc" d) (str.++ e "aabc")))
               (assume h2 (not (= (str.to_code d) 0)))
               (step t1 (cl (= d (str.++ (str.substr d 0 (- (str.len d) (str.len (str.substr "aabc" (- (str.len "aabc") 3) 3)))) (str.substr "aabc" (- (str.len "aabc") 3) 3)))) :rule concat_cprop_suffix :premises (h1 h2))"#: false,
            r#"(assume h1 (= (str.++ a "bc" d) (str.++ e "aabc")))
               (assume h2 (not (= (str.len d) 1)))
               (step t1 (cl (= d (str.++ (str.substr d 0 (- (str.len d) (str.len (str.substr "aabc" (- (str.len "aabc") 3) 3)))) (str.substr "aabc" (- (str.len "aabc") 3) 3)))) :rule concat_cprop_suffix :premises (h1 h2))"#: false,
        }
        "Term shared between the premises is not the same" {
            r#"(assume h1 (= (str.++ d "dcba" (str.++ a b)) "acda"))
               (assume h2 (not (= (str.len c) 0)))
               (step t1 (cl (= (str.++ a b) (str.++ (str.substr (str.++ a b) 0 (- (str.len (str.++ a b)) (str.len (str.substr "acda" (- (str.len "acda") 3) 3)))) (str.substr "acda" (- (str.len "acda") 3) 3)))) :rule concat_cprop_suffix :premises (h1 h2))"#: false,
            r#"(assume h1 (= (str.++ d "dcba" (str.++ "a" "b")) "acda"))
               (assume h2 (not (= (str.len "ab") 0)))
               (step t1 (cl (= (str.++ a b) (str.++ (str.substr (str.++ a b) 0 (- (str.len (str.++ a b)) (str.len (str.substr "acda" (- (str.len "acda") 3) 3)))) (str.substr "acda" (- (str.len "acda") 3) 3)))) :rule concat_cprop_suffix :premises (h1 h2))"#: false,
        }
        "Conclusion term is not of the form (= t_2 (str.++ r t_3))" {
            r#"(assume h1 (= (str.++ a "bc" d) (str.++ e "aabc")))
               (assume h2 (not (= (str.len d) 0)))
               (step t1 (cl (= a (str.++ (str.substr d 0 (- (str.len d) (str.len (str.substr "aabc" (- (str.len "aabc") 3) 3)))) (str.substr "aabc" (- (str.len "aabc") 3) 3)))) :rule concat_cprop_suffix :premises (h1 h2))"#: false,
            r#"(assume h1 (= (str.++ a "bc" d) (str.++ e "aabc")))
               (assume h2 (not (= (str.len d) 0)))
               (step t1 (cl (not (= d (str.++ (str.substr d 0 (- (str.len d) (str.len (str.substr "aabc" (- (str.len "aabc") 3) 3)))) (str.substr "aabc" (- (str.len "aabc") 3) 3))))) :rule concat_cprop_suffix :premises (h1 h2))"#: false,
            r#"(assume h1 (= (str.++ a "bc" d) (str.++ e "aabc")))
               (assume h2 (not (= (str.len d) 0)))
               (step t1 (cl (= d (str.++ a (str.substr d 0 (- (str.len d) (str.len (str.substr "aabc" (- (str.len "aabc") 3) 3)))) (str.substr "aabc" (- (str.len "aabc") 3) 3)))) :rule concat_cprop_suffix :premises (h1 h2))"#: false,
            r#"(assume h1 (= (str.++ a "bc" d) (str.++ e "aabc")))
               (assume h2 (not (= (str.len d) 0)))
               (step t1 (cl (= d (str.substr "aabc" (- (str.len "aabc") 3) 3))) :rule concat_cprop_suffix :premises (h1 h2))"#: false,
        }
    }
}

#[test]
fn string_decompose() {
    test_cases! {
        definitions = "
            (declare-fun a () String)
            (declare-fun b () String)
            (declare-fun c () String)
            (declare-fun d () String)
        ",
        "Simple working examples" {
            r#"(assume h1 (>= (str.len "ab") 2))
               (define-fun w_1 () String (str.substr "ab" 0 2))
               (define-fun w_2 () String (str.substr "ab" 2 (- (str.len "ab") 2)))
               (step t1 (cl (and (= "ab" (str.++ w_1 w_2)) (= (str.len w_1) 2))) :rule string_decompose :premises (h1) :args (false))"#: true,
            r#"(assume h1 (>= (str.len (str.++ "d" "c")) 1))
               (define-fun w_1 () String (str.substr (str.++ "d" "c") 0 1))
               (define-fun w_2 () String (str.substr (str.++ "d" "c") 1 (- (str.len (str.++ "d" "c")) 1)))
               (step t1 (cl (and (= (str.++ "d" "c") (str.++ w_1 w_2)) (= (str.len w_1) 1))) :rule string_decompose :premises (h1) :args (false))"#: true,
            r#"(assume h1 (>= (str.len (str.++ a (str.++ "b" c))) 0))
               (define-fun w_1 () String (str.substr (str.++ a (str.++ "b" c)) 0 0))
               (define-fun w_2 () String (str.substr (str.++ a (str.++ "b" c)) 0 (- (str.len (str.++ a (str.++ "b" c))) 0)))
               (step t1 (cl (and (= (str.++ a (str.++ "b" c)) (str.++ w_1 w_2)) (= (str.len w_1) 0))) :rule string_decompose :premises (h1) :args (false))"#: true,
        }
        "Reverse argument set to true" {
            r#"(assume h1 (>= (str.len "ab") 2))
               (define-fun w_1 () String (str.substr "ab" 0 2))
               (define-fun w_2 () String (str.substr "ab" 2 (- (str.len "ab") 2)))
               (step t1 (cl (and (= "ab" (str.++ w_1 w_2)) (= (str.len w_2) 2))) :rule string_decompose :premises (h1) :args (true))"#: true,
            r#"(assume h1 (>= (str.len (str.++ "d" "c")) 1))
               (define-fun w_1 () String (str.substr (str.++ "d" "c") 0 1))
               (define-fun w_2 () String (str.substr (str.++ "d" "c") 1 (- (str.len (str.++ "d" "c")) 1)))
               (step t1 (cl (and (= (str.++ "d" "c") (str.++ w_1 w_2)) (= (str.len w_2) 1))) :rule string_decompose :premises (h1) :args (true))"#: true,
        }
        "Invalid argument type" {
            r#"(assume h1 (>= (str.len "ab") 2))
               (define-fun w_1 () String (str.substr "ab" 0 2))
               (define-fun w_2 () String (str.substr "ab" 2 (- (str.len "ab") 2)))
               (step t1 (cl (and (= "ab" (str.++ w_1 w_2)) (= (str.len w_1) 2))) :rule string_decompose :premises (h1) :args (1))"#: false,
            r#"(assume h1 (>= (str.len "ab") 2))
               (define-fun w_1 () String (str.substr "ab" 0 2))
               (define-fun w_2 () String (str.substr "ab" 2 (- (str.len "ab") 2)))
               (step t1 (cl (and (= "ab" (str.++ w_1 w_2)) (= (str.len w_1) 2))) :rule string_decompose :premises (h1) :args (1.5))"#: false,
            r#"(assume h1 (>= (str.len "ab") 2))
               (define-fun w_1 () String (str.substr "ab" 0 2))
               (define-fun w_2 () String (str.substr "ab" 2 (- (str.len "ab") 2)))
               (step t1 (cl (and (= "ab" (str.++ w_1 w_2)) (= (str.len w_1) 2))) :rule string_decompose :premises (h1) :args ((- 1)))"#: false,
            r#"(assume h1 (>= (str.len "ab") 2))
               (define-fun w_1 () String (str.substr "ab" 0 2))
               (define-fun w_2 () String (str.substr "ab" 2 (- (str.len "ab") 2)))
               (step t1 (cl (and (= "ab" (str.++ w_1 w_2)) (= (str.len w_1) 2))) :rule string_decompose :premises (h1) :args ("teste"))"#: false,
            r#"(assume h1 (>= (str.len "ab") 2))
               (define-fun w_1 () String (str.substr "ab" 0 2))
               (define-fun w_2 () String (str.substr "ab" 2 (- (str.len "ab") 2)))
               (step t1 (cl (and (= "ab" (str.++ w_1 w_2)) (= (str.len w_1) 2))) :rule string_decompose :premises (h1) :args (d))"#: false,
        }
        "Premise term \"t\" is not the same in the conclusion" {
            r#"(assume h1 (>= (str.len "ab") 2))
               (define-fun w_1 () String (str.substr "ab" 0 2))
               (define-fun w_2 () String (str.substr "ab" 2 (- (str.len "ab") 2)))
               (step t1 (cl (and (= "ba" (str.++ w_1 w_2)) (= (str.len w_2) 2))) :rule string_decompose :premises (h1) :args (true))"#: false,
            r#"(assume h1 (>= (str.len "ba") 2))
               (define-fun w_1 () String (str.substr "ba" 0 2))
               (define-fun w_2 () String (str.substr "ba" 2 (- (str.len "ba") 2)))
               (step t1 (cl (and (= "ab" (str.++ w_1 w_2)) (= (str.len w_2) 2))) :rule string_decompose :premises (h1) :args (true))"#: false,
            r#"(assume h1 (>= (str.len (str.++ "a" (str.++ b "c"))) 2))
               (define-fun w_1 () String (str.substr (str.++ "a" (str.++ b "c")) 0 2))
               (define-fun w_2 () String (str.substr (str.++ "a" (str.++ b "c")) 2 (- (str.len (str.++ "a" (str.++ b "c"))) 2)))
               (step t1 (cl (and (= (str.++ a (str.++ b "c")) (str.++ w_1 w_2)) (= (str.len w_2) 2))) :rule string_decompose :premises (h1) :args (true))"#: false,
        }
        "Switched skolems in the conclusion" {
            r#"(assume h1 (>= (str.len (str.++ "d" "c")) 1))
               (define-fun w_1 () String (str.substr (str.++ "d" "c") 0 1))
               (define-fun w_2 () String (str.substr (str.++ "d" "c") 1 (- (str.len (str.++ "d" "c")) 1)))
               (step t1 (cl (and (= (str.++ "d" "c") (str.++ w_2 w_1)) (= (str.len w_1) 1))) :rule string_decompose :premises (h1) :args (false))"#: false,
        }
        "" {}
        "Premise is not of the form (>= (str.len t) n)" {
            r#"(assume h1 (< (str.len (str.++ "d" "c")) 1))
               (define-fun w_1 () String (str.substr (str.++ "d" "c") 0 1))
               (define-fun w_2 () String (str.substr (str.++ "d" "c") 1 (- (str.len (str.++ "d" "c")) 1)))
               (step t1 (cl (and (= (str.++ "d" "c") (str.++ w_1 w_2)) (= (str.len w_2) 1))) :rule string_decompose :premises (h1) :args (true))"#: false,
            r#"(assume h1 (>= (str.to_code (str.++ "d" "c")) 1))
               (define-fun w_1 () String (str.substr (str.++ "d" "c") 0 1))
               (define-fun w_2 () String (str.substr (str.++ "d" "c") 1 (- (str.len (str.++ "d" "c")) 1)))
               (step t1 (cl (and (= (str.++ "d" "c") (str.++ w_1 w_2)) (= (str.len w_2) 1))) :rule string_decompose :premises (h1) :args (true))"#: false,
        }
        "Conclusion term is not of the form (and (= t x) (= (str.len y) 0))" {
            r#"(assume h1 (>= (str.len (str.++ a (str.++ "b" c))) 0))
               (define-fun w_1 () String (str.substr (str.++ a (str.++ "b" c)) 0 0))
               (define-fun w_2 () String (str.substr (str.++ a (str.++ "b" c)) 0 (- (str.len (str.++ a (str.++ "b" c))) 0)))
               (step t1 (cl (or (= (str.++ a (str.++ "b" c)) (str.++ w_1 w_2)) (= (str.len w_1) 0))) :rule string_decompose :premises (h1) :args (false))"#: false,
            r#"(assume h1 (>= (str.len (str.++ a (str.++ "b" c))) 0))
               (define-fun w_1 () String (str.substr (str.++ a (str.++ "b" c)) 0 0))
               (define-fun w_2 () String (str.substr (str.++ a (str.++ "b" c)) 0 (- (str.len (str.++ a (str.++ "b" c))) 0)))
               (step t1 (cl (and (not (= (str.++ a (str.++ "b" c)) (str.++ w_1 w_2))) (= (str.len w_1) 0))) :rule string_decompose :premises (h1) :args (false))"#: false,
            r#"(assume h1 (>= (str.len (str.++ a (str.++ "b" c))) 0))
               (define-fun w_1 () String (str.substr (str.++ a (str.++ "b" c)) 0 0))
               (define-fun w_2 () String (str.substr (str.++ a (str.++ "b" c)) 0 (- (str.len (str.++ a (str.++ "b" c))) 0)))
               (step t1 (cl (and (= (str.++ a (str.++ "b" c)) (str.++ w_1 w_2)) (not (= (str.len w_1) 0)))) :rule string_decompose :premises (h1) :args (false))"#: false,
            r#"(assume h1 (>= (str.len (str.++ a (str.++ "b" c))) 0))
               (define-fun w_1 () String (str.substr (str.++ a (str.++ "b" c)) 0 0))
               (define-fun w_2 () String (str.substr (str.++ a (str.++ "b" c)) 0 (- (str.len (str.++ a (str.++ "b" c))) 0)))
               (step t1 (cl (and (= (str.++ a (str.++ "b" c)) (str.++ w_1 w_2)) (= (str.to_code w_1) 0))) :rule string_decompose :premises (h1) :args (false))"#: false,
        }
        "Inverted argument value" {
            r#"(assume h1 (>= (str.len "ab") 2))
               (define-fun w_1 () String (str.substr "ab" 0 2))
               (define-fun w_2 () String (str.substr "ab" 2 (- (str.len "ab") 2)))
               (step t1 (cl (and (= "ab" (str.++ w_1 w_2)) (= (str.len w_1) 2))) :rule string_decompose :premises (h1) :args (true))"#: false,
            r#"(assume h1 (>= (str.len (str.++ "d" "c")) 1))
               (define-fun w_1 () String (str.substr (str.++ "d" "c") 0 1))
               (define-fun w_2 () String (str.substr (str.++ "d" "c") 1 (- (str.len (str.++ "d" "c")) 1)))
               (step t1 (cl (and (= (str.++ "d" "c") (str.++ w_1 w_2)) (= (str.len w_2) 1))) :rule string_decompose :premises (h1) :args (false))"#: false,
        }
    }
}

#[test]
fn string_length_pos() {
    test_cases! {
        definitions = "
            (declare-fun a () String)
            (declare-fun b () String)
            (declare-fun c () String)
            (declare-fun d () String)
        ",
        "Simple working examples" {
            r#"(step t1 (cl (or (and (= (str.len "ab") 0) (= "ab" "")) (> (str.len "ab") 0))) :rule string_length_pos :args ("ab"))"#: true,
            r#"(step t1 (cl (or (and (= (str.len (str.++ "a" (str.++ b "c"))) 0) (= (str.++ "a" (str.++ b "c")) "")) (> (str.len (str.++ "a" (str.++ b "c"))) 0))) :rule string_length_pos :args ((str.++ "a" (str.++ b "c"))))"#: true,
            r#"(step t1 (cl (or (and (= (str.len a) 0) (= a "")) (> (str.len a) 0))) :rule string_length_pos :args (a))"#: true,
            r#"(step t1 (cl (or (and (= (str.len (str.++ a "b")) 0) (= (str.++ a "b") "")) (> (str.len (str.++ a "b")) 0))) :rule string_length_pos :args ((str.++ a "b")))"#: true,
        }
        "Argument term \"t\" and the conclusion term \"t\" is not the same" {
            r#"(step t1 (cl (or (and (= (str.len (str.++ a "b")) 0) (= (str.++ a "b") "")) (> (str.len (str.++ a "b")) 0))) :rule string_length_pos :args ((str.++ "a" b)))"#: false,
            r#"(step t1 (cl (or (and (= (str.len (str.++ "a" b)) 0) (= (str.++ "a" b) "")) (> (str.len (str.++ "a" b)) 0))) :rule string_length_pos :args ((str.++ a "b")))"#: false,
            r#"(step t1 (cl (or (and (= (str.len (str.++ "b" a)) 0) (= (str.++ a "b") "")) (> (str.len (str.++ a "b")) 0))) :rule string_length_pos :args ((str.++ a "b")))"#: false,
            r#"(step t1 (cl (or (and (= (str.len (str.++ a "b")) 0) (= a "")) (> (str.len (str.++ a "b")) 0))) :rule string_length_pos :args ((str.++ a "b")))"#: false,
            r#"(step t1 (cl (or (and (= (str.len (str.++ a "b")) 0) (= (str.++ a "b") "")) (> (str.len (str.++ b d)) 0))) :rule string_length_pos :args ((str.++ a "b")))"#: false,
        }
        "Conclusion is not of the form (or (and (= (str.len t) 0) (= t \"\")) (> (str.len t) 0))" {
            r#"(step t1 (cl (and (and (= (str.len "ab") 0) (= "ab" "")) (> (str.len "ab") 0))) :rule string_length_pos :args ("ab"))"#: false,
            r#"(step t1 (cl (or (or (= (str.len "ab") 0) (= "ab" "")) (> (str.len "ab") 0))) :rule string_length_pos :args ("ab"))"#: false,
            r#"(step t1 (cl (or (and (not (= (str.len "ab") 0)) (= "ab" "")) (> (str.len "ab") 0))) :rule string_length_pos :args ("ab"))"#: false,
            r#"(step t1 (cl (or (and (= (str.to_code "ab") 0) (= "ab" "")) (> (str.len "ab") 0))) :rule string_length_pos :args ("ab"))"#: false,
            r#"(step t1 (cl (or (and (= (str.len "ab") 1) (= "ab" "")) (> (str.len "ab") 0))) :rule string_length_pos :args ("ab"))"#: false,
            r#"(step t1 (cl (or (and (= (str.len "ab") 0) (not (= "ab" ""))) (> (str.len "ab") 0))) :rule string_length_pos :args ("ab"))"#: false,
            r#"(step t1 (cl (or (and (= (str.len "ab") 0) (= "ab" "a")) (> (str.len "ab") 0))) :rule string_length_pos :args ("ab"))"#: false,
            r#"(step t1 (cl (or (and (= (str.len "ab") 0) (= "ab" "")) (< (str.len "ab") 0))) :rule string_length_pos :args ("ab"))"#: false,
            r#"(step t1 (cl (or (and (= (str.len "ab") 0) (= "ab" "")) (> (str.to_code "ab") 0))) :rule string_length_pos :args ("ab"))"#: false,
            r#"(step t1 (cl (or (and (= (str.len "ab") 0) (= "ab" "")) (> (str.len "ab") 1))) :rule string_length_pos :args ("ab"))"#: false,
        }
    }
}

#[test]
fn string_length_non_empty() {
    test_cases! {
        definitions = "
            (declare-fun a () String)
            (declare-fun b () String)
            (declare-fun c () String)
            (declare-fun d () String)
        ",
        "Simple working examples" {
            r#"(assume h1 (not (= "ab" "")))
               (step t1 (cl (not (= (str.len "ab") 0))) :rule string_length_non_empty :premises (h1))"#: true,
            r#"(assume h1 (not (= (str.++ "a" (str.++ "b" "c")) "")))
               (step t1 (cl (not (= (str.len (str.++ "a" (str.++ "b" "c"))) 0))) :rule string_length_non_empty :premises (h1))"#: true,
            r#"(assume h1 (not (= d "")))
               (step t1 (cl (not (= (str.len d) 0))) :rule string_length_non_empty :premises (h1))"#: true,
            r#"(assume h1 (not (= (str.++ b c) "")))
               (step t1 (cl (not (= (str.len (str.++ b c)) 0))) :rule string_length_non_empty :premises (h1))"#: true,
        }
        "Premise term is not an inequality of the form (not (= t \"\"))" {
            r#"(assume h1 (= (str.++ "a" (str.++ "b" "c")) ""))
               (step t1 (cl (not (= (str.len (str.++ "a" (str.++ "b" "c"))) 0))) :rule string_length_non_empty :premises (h1))"#: false,
            r#"(assume h1 (not (= (str.++ "a" (str.++ "b" "c")) "ab")))
               (step t1 (cl (not (= (str.len (str.++ "a" (str.++ "b" "c"))) 0))) :rule string_length_non_empty :premises (h1))"#: false,
            r#"(assume h1 (not (= (str.++ "a" (str.++ "b" "c")) a)))
               (step t1 (cl (not (= (str.len (str.++ "a" (str.++ "b" "c"))) 0))) :rule string_length_non_empty :premises (h1))"#: false,
            r#"(assume h1 (not (= (str.++ "a" (str.++ "b" "c")) (str.++ a b))))
               (step t1 (cl (not (= (str.len (str.++ "a" (str.++ "b" "c"))) 0))) :rule string_length_non_empty :premises (h1))"#: false,
        }
        "Shared term \"t\" between the premise and the conclusion is not the same" {
            r#"(assume h1 (not (= (str.++ b c) "")))
               (step t1 (cl (not (= (str.len (str.++ c b)) 0))) :rule string_length_non_empty :premises (h1))"#: false,
            r#"(assume h1 (not (= (str.++ b c) "")))
               (step t1 (cl (not (= (str.len (str.++ "b" "c")) 0))) :rule string_length_non_empty :premises (h1))"#: false,
            r#"(assume h1 (not (= (str.++ "b" c) "")))
               (step t1 (cl (not (= (str.len (str.++ b c)) 0))) :rule string_length_non_empty :premises (h1))"#: false,
        }
        "Conclusion term is not an inequality of the form (not (= (str.len t) 0))" {
            r#"(assume h1 (not (= "ab" "")))
               (step t1 (cl (= (str.len "ab") 0)) :rule string_length_non_empty :premises (h1))"#: false,
            r#"(assume h1 (not (= "ab" "")))
               (step t1 (cl (not (= (str.to_code "ab") 0))) :rule string_length_non_empty :premises (h1))"#: false,
            r#"(assume h1 (not (= "ab" "")))
               (step t1 (cl (not (> (str.len "ab") 0))) :rule string_length_non_empty :premises (h1))"#: false,
            r#"(assume h1 (not (= "ab" "")))
               (step t1 (cl (not (= (str.len "ab") 1))) :rule string_length_non_empty :premises (h1))"#: false,
        }
    }
}

#[test]
fn re_inter() {
    test_cases! {
        definitions = "
            (declare-fun x () String)
            (declare-fun y () String)
            (declare-fun z () String)
            (declare-fun a () RegLan)
            (declare-fun b () RegLan)
            (declare-fun c () RegLan)
            (declare-fun d () RegLan)
        ",
        "Simple working examples" {
            r#"(assume h1 (str.in_re x a))
               (assume h2 (str.in_re x b))
               (step t1 (cl (str.in_re x (re.inter a b))) :rule re_inter :premises (h1 h2))"#: true,
            r#"(assume h1 (str.in_re "xyz" c))
               (assume h2 (str.in_re "xyz" d))
               (step t1 (cl (str.in_re "xyz" (re.inter c d))) :rule re_inter :premises (h1 h2))"#: true,
        }
        "Premise terms are not str.in_re applications" {
            r#"(assume h1 (and (str.in_re x a) true))
               (assume h2 (str.in_re x b))
               (step t1 (cl (str.in_re x (re.inter a b))) :rule re_inter :premises (h1 h2))"#: false,
            r#"(assume h1 (str.in_re x a))
               (assume h2 (or false (str.in_re x b)))
               (step t1 (cl (str.in_re x (re.inter a b))) :rule re_inter :premises (h1 h2))"#: false,
        }
        "Conclusion term is not of the form (str.in_re t (re.inter r_1 r_2))" {
            r#"(assume h1 (str.in_re "xyz" c))
               (assume h2 (str.in_re "xyz" d))
               (step t1 (cl (not (str.in_re "xyz" (re.inter c d)))) :rule re_inter :premises (h1 h2))"#: false,
            r#"(assume h1 (str.in_re "xyz" c))
               (assume h2 (str.in_re "xyz" d))
               (step t1 (cl (str.in_re "xyz" (re.union c d))) :rule re_inter :premises (h1 h2))"#: false,
        }
        "Different terms in the premise" {
            r#"(assume h1 (str.in_re x a))
               (assume h2 (str.in_re y b))
               (step t1 (cl (str.in_re x (re.inter a b))) :rule re_inter :premises (h1 h2))"#: false,
        }
        "Different terms in the premise and conclusion" {
            r#"(assume h1 (str.in_re x a))
               (assume h2 (str.in_re x b))
               (step t1 (cl (str.in_re y (re.inter a b))) :rule re_inter :premises (h1 h2))"#: false,
            r#"(assume h1 (str.in_re x a))
               (assume h2 (str.in_re y b))
               (step t1 (cl (str.in_re y (re.inter a b))) :rule re_inter :premises (h1 h2))"#: false,
            r#"(assume h1 (str.in_re y a))
               (assume h2 (str.in_re x b))
               (step t1 (cl (str.in_re y (re.inter a b))) :rule re_inter :premises (h1 h2))"#: false,
        }
        "Regular expressions in the premises differs from the ones in the conclusion" {
            r#"(assume h1 (str.in_re x a))
               (assume h2 (str.in_re x b))
               (step t1 (cl (str.in_re x (re.inter c d))) :rule re_inter :premises (h1 h2))"#: false,
            r#"(assume h1 (str.in_re x a))
               (assume h2 (str.in_re x b))
               (step t1 (cl (str.in_re x (re.inter a d))) :rule re_inter :premises (h1 h2))"#: false,
            r#"(assume h1 (str.in_re x a))
               (assume h2 (str.in_re x b))
               (step t1 (cl (str.in_re x (re.inter c b))) :rule re_inter :premises (h1 h2))"#: false,
        }
    }
}

#[test]
fn re_unfold_neg() {
    test_cases! {
        definitions = "
            (declare-fun x () String)
            (declare-fun y () String)
            (declare-fun z () String)
            (declare-fun a () RegLan)
            (declare-fun b () RegLan)
            (declare-fun c () RegLan)
            (declare-fun d () RegLan)
        ",
        "Simple working examples" {
            r#"(assume h1 (not (str.in_re x (re.* a))))
               (step t1 (cl (and (not (= x "")) (forall ((L Int)) (or (<= L 0) (< (str.len x) L) (not (str.in_re (str.substr x 0 L) a)) (not (str.in_re (str.substr x L (- (str.len x) L)) (re.* a))))))) :rule re_unfold_neg :premises (h1))"#: true,
            r#"(assume h1 (not (str.in_re y (re.++ a b c))))
               (step t1 (cl (forall ((L Int)) (or (< L 0) (< (str.len y) L) (not (str.in_re (str.substr y 0 L) a)) (not (str.in_re (str.substr y L (- (str.len y) L)) (re.++ b c)))))) :rule re_unfold_neg :premises (h1))"#: true,
            r#"(assume h1 (not (str.in_re y (re.++ c d))))
               (step t1 (cl (forall ((L Int)) (or (< L 0) (< (str.len y) L) (not (str.in_re (str.substr y 0 L) c)) (not (str.in_re (str.substr y L (- (str.len y) L)) d))))) :rule re_unfold_neg :premises (h1))"#: true,
        }
        "Premise term is not of the form (not (str.in_re t R))" {
            r#"(assume h1 (str.in_re x (re.* a)))
               (step t1 (cl (and (not (= x "")) (forall ((L Int)) (or (<= L 0) (< (str.len x) L) (not (str.in_re (str.substr x 0 L) a)) (not (str.in_re (str.substr x L (- (str.len x) L)) (re.* a))))))) :rule re_unfold_neg :premises (h1))"#: false,
        }
        "Regular expression in the premise is not a re.* or re.++ application" {
            r#"(assume h1 (not (str.in_re y (re.union a b c))))
               (step t1 (cl (forall ((L Int)) (or (< L 0) (< (str.len y) L) (not (str.in_re (str.substr y 0 L) a)) (not (str.in_re (str.substr y L (- (str.len y) L)) (re.++ b c)))))) :rule re_unfold_neg :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re y (re.inter a b c))))
               (step t1 (cl (forall ((L Int)) (or (< L 0) (< (str.len y) L) (not (str.in_re (str.substr y 0 L) a)) (not (str.in_re (str.substr y L (- (str.len y) L)) (re.++ b c)))))) :rule re_unfold_neg :premises (h1))"#: false,
        }
        "Conclusion is not of the form (forall ... (or (< l 0) (< (str.len t) l) (not (str.in_re pref r_1)) (not (str.in_re suff r))))" {
            r#"(assume h1 (not (str.in_re y (re.++ c d))))
               (step t1 (cl (exists ((L Int)) (or (< L 0) (< (str.len y) L) (not (str.in_re (str.substr y 0 L) c)) (not (str.in_re (str.substr y L (- (str.len y) L)) d))))) :rule re_unfold_neg :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re y (re.++ c d))))
               (step t1 (cl (forall ((L Int)) (and (< L 0) (< (str.len y) L) (not (str.in_re (str.substr y 0 L) c)) (not (str.in_re (str.substr y L (- (str.len y) L)) d))))) :rule re_unfold_neg :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re y (re.++ c d))))
               (step t1 (cl (forall ((L Int)) (or (> L 0) (< (str.len y) L) (not (str.in_re (str.substr y 0 L) c)) (not (str.in_re (str.substr y L (- (str.len y) L)) d))))) :rule re_unfold_neg :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re y (re.++ c d))))
               (step t1 (cl (forall ((L Int)) (or (< L 1) (< (str.len y) L) (not (str.in_re (str.substr y 0 L) c)) (not (str.in_re (str.substr y L (- (str.len y) L)) d))))) :rule re_unfold_neg :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re y (re.++ c d))))
               (step t1 (cl (forall ((L Int)) (or (< L 0) (>= (str.len y) L) (not (str.in_re (str.substr y 0 L) c)) (not (str.in_re (str.substr y L (- (str.len y) L)) d))))) :rule re_unfold_neg :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re y (re.++ c d))))
               (step t1 (cl (forall ((L Int)) (or (< L 0) (< (str.to_code y) L) (not (str.in_re (str.substr y 0 L) c)) (not (str.in_re (str.substr y L (- (str.len y) L)) d))))) :rule re_unfold_neg :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re y (re.++ c d))))
               (step t1 (cl (forall ((L Int)) (or (< L 0) (< (str.len y) L) (str.in_re (str.substr y 0 L) c) (not (str.in_re (str.substr y L (- (str.len y) L)) d))))) :rule re_unfold_neg :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re y (re.++ c d))))
               (step t1 (cl (forall ((L Int)) (or (< L 0) (< (str.len y) L) (not (and (str.in_re (str.substr y 0 L) c) true)) (not (str.in_re (str.substr y L (- (str.len y) L)) d))))) :rule re_unfold_neg :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re y (re.++ c d))))
               (step t1 (cl (forall ((L Int)) (or (< L 0) (< (str.len y) L) (not (str.in_re (str.substr y 0 L) c)) (str.in_re (str.substr y L (- (str.len y) L)) d)))) :rule re_unfold_neg :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re y (re.++ c d))))
               (step t1 (cl (forall ((L Int)) (or (< L 0) (< (str.len y) L) (not (str.in_re (str.substr y 0 L) c)) (not (or false (str.in_re (str.substr y L (- (str.len y) L)) d)))))) :rule re_unfold_neg :premises (h1))"#: false,
        }
        "Conclusion is not fo the form (and (not (= t \"\")) (forall ... (or (<= l 0) (< (str.len t) l) (not (str.in_re pref r_1)) (not (str.in_re suff r)))))))" {
            r#"(assume h1 (not (str.in_re x (re.* a))))
               (step t1 (cl (or (not (= x "")) (forall ((L Int)) (or (<= L 0) (< (str.len x) L) (not (str.in_re (str.substr x 0 L) a)) (not (str.in_re (str.substr x L (- (str.len x) L)) (re.* a))))))) :rule re_unfold_neg :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re x (re.* a))))
               (step t1 (cl (and (= x "") (forall ((L Int)) (or (<= L 0) (< (str.len x) L) (not (str.in_re (str.substr x 0 L) a)) (not (str.in_re (str.substr x L (- (str.len x) L)) (re.* a))))))) :rule re_unfold_neg :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re x (re.* a))))
               (step t1 (cl (and (not (= x "")) (exists ((L Int)) (or (<= L 0) (< (str.len x) L) (not (str.in_re (str.substr x 0 L) a)) (not (str.in_re (str.substr x L (- (str.len x) L)) (re.* a))))))) :rule re_unfold_neg :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re x (re.* a))))
               (step t1 (cl (and (not (= x "")) (forall ((L Int)) (and (<= L 0) (< (str.len x) L) (not (str.in_re (str.substr x 0 L) a)) (not (str.in_re (str.substr x L (- (str.len x) L)) (re.* a))))))) :rule re_unfold_neg :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re x (re.* a))))
               (step t1 (cl (and (not (= x "")) (forall ((L Int)) (or (< L 0) (< (str.len x) L) (not (str.in_re (str.substr x 0 L) a)) (not (str.in_re (str.substr x L (- (str.len x) L)) (re.* a))))))) :rule re_unfold_neg :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re x (re.* a))))
               (step t1 (cl (and (not (= x "")) (forall ((L Int)) (or (<= L 0) (> (str.len x) L) (not (str.in_re (str.substr x 0 L) a)) (not (str.in_re (str.substr x L (- (str.len x) L)) (re.* a))))))) :rule re_unfold_neg :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re x (re.* a))))
               (step t1 (cl (and (not (= x "")) (forall ((L Int)) (or (<= L 0) (< (str.to_code x) L) (not (str.in_re (str.substr x 0 L) a)) (not (str.in_re (str.substr x L (- (str.len x) L)) (re.* a))))))) :rule re_unfold_neg :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re x (re.* a))))
               (step t1 (cl (and (not (= x "")) (forall ((L Int)) (or (<= L 0) (< (str.len x) L) (str.in_re (str.substr x 0 L) a) (not (str.in_re (str.substr x L (- (str.len x) L)) (re.* a))))))) :rule re_unfold_neg :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re x (re.* a))))
               (step t1 (cl (and (not (= x "")) (forall ((L Int)) (or (<= L 0) (< (str.len x) L) (not (and (str.in_re (str.substr x 0 L) a) true)) (not (str.in_re (str.substr x L (- (str.len x) L)) (re.* a))))))) :rule re_unfold_neg :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re x (re.* a))))
               (step t1 (cl (and (not (= x "")) (forall ((L Int)) (or (<= L 0) (< (str.len x) L) (not (str.in_re (str.substr x 0 L) a)) (str.in_re (str.substr x L (- (str.len x) L)) (re.* a)))))) :rule re_unfold_neg :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re x (re.* a))))
               (step t1 (cl (and (not (= x "")) (forall ((L Int)) (or (<= L 0) (< (str.len x) L) (not (str.in_re (str.substr x 0 L) a)) (not (or false (str.in_re (str.substr x L (- (str.len x) L)) (re.* a)))))))) :rule re_unfold_neg :premises (h1))"#: false,
        }
        "Switched conclusion format" {
            r#"(assume h1 (not (str.in_re x (re.* a))))
               (step t1 (cl (forall ((L Int)) (or (< L 0) (< (str.len y) L) (not (str.in_re (str.substr y 0 L) a)) (not (str.in_re (str.substr y L (- (str.len y) L)) (re.* a)))))) :rule re_unfold_neg :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re y (re.++ a b c))))
               (step t1 (cl (and (not (= x "")) (forall ((L Int)) (or (<= L 0) (< (str.len x) L) (not (str.in_re (str.substr x 0 L) a)) (not (str.in_re (str.substr x L (- (str.len x) L)) (re.* a))))))) :rule re_unfold_neg :premises (h1))"#: false,
        }
        "Different terms in the premise and conclusion" {
            r#"(assume h1 (not (str.in_re x (re.* a))))
               (step t1 (cl (and (not (= y "")) (forall ((L Int)) (or (<= L 0) (< (str.len x) L) (not (str.in_re (str.substr x 0 L) a)) (not (str.in_re (str.substr x L (- (str.len x) L)) (re.* a))))))) :rule re_unfold_neg :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re x (re.* a))))
               (step t1 (cl (and (not (= x "")) (forall ((L Int)) (or (<= L 0) (< (str.len y) L) (not (str.in_re (str.substr x 0 L) a)) (not (str.in_re (str.substr x L (- (str.len x) L)) (re.* a))))))) :rule re_unfold_neg :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re x (re.* a))))
               (step t1 (cl (and (not (= x "")) (forall ((L Int)) (or (<= L 0) (< (str.len x) L) (not (str.in_re (str.substr y 0 L) a)) (not (str.in_re (str.substr x L (- (str.len x) L)) (re.* a))))))) :rule re_unfold_neg :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re x (re.* a))))
               (step t1 (cl (and (not (= x "")) (forall ((L Int)) (or (<= L 0) (< (str.len x) L) (not (str.in_re (str.substr x 0 L) a)) (not (str.in_re (str.substr y L (- (str.len x) L)) (re.* a))))))) :rule re_unfold_neg :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re x (re.* a))))
               (step t1 (cl (and (not (= x "")) (forall ((L Int)) (or (<= L 0) (< (str.len x) L) (not (str.in_re (str.substr x 0 L) a)) (not (str.in_re (str.substr x L (- (str.len y) L)) (re.* a))))))) :rule re_unfold_neg :premises (h1))"#: false,
        }
        "Regular expressions in the premises differs from the ones in the conclusion" {
            r#"(assume h1 (not (str.in_re x (re.* a))))
               (step t1 (cl (and (not (= x "")) (forall ((L Int)) (or (<= L 0) (< (str.len x) L) (not (str.in_re (str.substr x 0 L) b)) (not (str.in_re (str.substr x L (- (str.len x) L)) (re.* a))))))) :rule re_unfold_neg :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re x (re.* a))))
               (step t1 (cl (and (not (= x "")) (forall ((L Int)) (or (<= L 0) (< (str.len x) L) (not (str.in_re (str.substr x 0 L) a)) (not (str.in_re (str.substr x L (- (str.len x) L)) (re.* b))))))) :rule re_unfold_neg :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re y (re.++ a b))))
               (step t1 (cl (forall ((L Int)) (or (< L 0) (< (str.len y) L) (not (str.in_re (str.substr y 0 L) c)) (not (str.in_re (str.substr y L (- (str.len y) L)) b))))) :rule re_unfold_neg :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re y (re.++ a b))))
               (step t1 (cl (forall ((L Int)) (or (< L 0) (< (str.len y) L) (not (str.in_re (str.substr y 0 L) a)) (not (str.in_re (str.substr y L (- (str.len y) L)) d))))) :rule re_unfold_neg :premises (h1))"#: false,
        }
        "Incorrect singleton elimination in the conclusion" {
            r#"(assume h1 (not (str.in_re y (re.++ a b c))))
               (step t1 (cl (forall ((L Int)) (or (< L 0) (< (str.len y) L) (not (str.in_re (str.substr y 0 L) a)) (not (str.in_re (str.substr y L (- (str.len y) L)) (re.++ a b c)))))) :rule re_unfold_neg :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re y (re.++ a b c))))
               (step t1 (cl (forall ((L Int)) (or (< L 0) (< (str.len y) L) (not (str.in_re (str.substr y 0 L) a)) (not (str.in_re (str.substr y L (- (str.len y) L)) b))))) :rule re_unfold_neg :premises (h1))"#: false,
        }
    }
}

#[test]
fn re_unfold_neg_concat_fixed_prefix() {
    test_cases! {
        definitions = "
            (declare-fun x () String)
            (declare-fun y () String)
            (declare-fun z () String)
            (declare-fun a () RegLan)
            (declare-fun b () RegLan)
            (declare-fun c () RegLan)
            (declare-fun d () RegLan)
        ",
        "Simple working examples" {
            r#"(assume h1 (not (str.in_re x (re.++ (str.to_re "xyz") b))))
               (step t1 (cl (or (not (str.in_re (str.substr x 0 3) (str.to_re "xyz"))) (not (str.in_re (str.substr x 3 (- (str.len x) 3)) b)))) :rule re_unfold_neg_concat_fixed_prefix :premises (h1))"#: true,
            r#"(assume h1 (not (str.in_re x (re.++ (re.++ (str.to_re "x") (str.to_re "yzw")) a))))
               (step t1 (cl (or (not (str.in_re (str.substr x 0 4) (re.++ (str.to_re "x") (str.to_re "yzw")))) (not (str.in_re (str.substr x 4 (- (str.len x) 4)) a)))) :rule re_unfold_neg_concat_fixed_prefix :premises (h1))"#: true,
            r#"(assume h1 (not (str.in_re x (re.++ re.allchar c))))
               (step t1 (cl (or (not (str.in_re (str.substr x 0 1) re.allchar)) (not (str.in_re (str.substr x 1 (- (str.len x) 1)) c)))) :rule re_unfold_neg_concat_fixed_prefix :premises (h1))"#: true,
            r#"(assume h1 (not (str.in_re x (re.++ (re.union (str.to_re "xy") re.none) d))))
               (step t1 (cl (or (not (str.in_re (str.substr x 0 2) (re.union (str.to_re "xy") re.none))) (not (str.in_re (str.substr x 2 (- (str.len x) 2)) d)))) :rule re_unfold_neg_concat_fixed_prefix :premises (h1))"#: true,
            r#"(assume h1 (not (str.in_re x (re.++ (re.inter (str.to_re "xy") re.all) a))))
               (step t1 (cl (or (not (str.in_re (str.substr x 0 2) (re.inter (str.to_re "xy") re.all))) (not (str.in_re (str.substr x 2 (- (str.len x) 2)) a)))) :rule re_unfold_neg_concat_fixed_prefix :premises (h1))"#: true,
            r#"(assume h1 (not (str.in_re x (re.++ (re.inter (str.to_re "xy") (str.to_re "zw") re.all) b))))
               (step t1 (cl (or (not (str.in_re (str.substr x 0 2) (re.inter (str.to_re "xy") (str.to_re "zw") re.all))) (not (str.in_re (str.substr x 2 (- (str.len x) 2)) b)))) :rule re_unfold_neg_concat_fixed_prefix :premises (h1))"#: true,
        }
        "Premise is not of the form (not (str.in_re t R))" {
            r#"(assume h1 (str.in_re x (re.++ (str.to_re "xyz") b)))
               (step t1 (cl (or (not (str.in_re (str.substr x 0 3) (str.to_re "xyz"))) (not (str.in_re (str.substr x 3 (- (str.len x) 3)) b)))) :rule re_unfold_neg_concat_fixed_prefix :premises (h1))"#: false,
            r#"(assume h1 (not (str.< x y)))
               (step t1 (cl (or (not (str.in_re (str.substr x 0 3) (str.to_re "xyz"))) (not (str.in_re (str.substr x 3 (- (str.len x) 3)) b)))) :rule re_unfold_neg_concat_fixed_prefix :premises (h1))"#: false,
        }
        "Regular expression in the premise is not a re.++ application" {
            r#"(assume h1 (not (str.in_re x a)))
               (step t1 (cl (or (not (str.in_re (str.substr x 0 4) (re.++ (str.to_re "x") (str.to_re "yzw")))) (not (str.in_re (str.substr x 4 (- (str.len x) 4)) a)))) :rule re_unfold_neg_concat_fixed_prefix :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re x re.all)))
               (step t1 (cl (or (not (str.in_re (str.substr x 0 4) (re.++ (str.to_re "x") (str.to_re "yzw")))) (not (str.in_re (str.substr x 4 (- (str.len x) 4)) a)))) :rule re_unfold_neg_concat_fixed_prefix :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re x (re.union (re.++ (str.to_re "x") (str.to_re "yzw")) a))))
               (step t1 (cl (or (not (str.in_re (str.substr x 0 4) (re.++ (str.to_re "x") (str.to_re "yzw")))) (not (str.in_re (str.substr x 4 (- (str.len x) 4)) a)))) :rule re_unfold_neg_concat_fixed_prefix :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re x (re.inter (re.++ (str.to_re "x") (str.to_re "yzw")) a))))
               (step t1 (cl (or (not (str.in_re (str.substr x 0 4) (re.++ (str.to_re "x") (str.to_re "yzw")))) (not (str.in_re (str.substr x 4 (- (str.len x) 4)) a)))) :rule re_unfold_neg_concat_fixed_prefix :premises (h1))"#: false,
        }
        "Conclusion is not of the form (or (not (str.in_re pref r_1)) (not (str.in_re suff r_2)))" {
            r#"(assume h1 (not (str.in_re x (re.++ re.allchar c))))
               (step t1 (cl (and (not (str.in_re (str.substr x 0 1) re.allchar)) (not (str.in_re (str.substr x 1 (- (str.len x) 1)) c)))) :rule re_unfold_neg_concat_fixed_prefix :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re x (re.++ re.allchar c))))
               (step t1 (cl (or (str.in_re (str.substr x 0 1) re.allchar) (not (str.in_re (str.substr x 1 (- (str.len x) 1)) c)))) :rule re_unfold_neg_concat_fixed_prefix :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re x (re.++ re.allchar c))))
               (step t1 (cl (or (not (str.in_re (str.substr x 0 1) re.allchar)) (str.in_re (str.substr x 1 (- (str.len x) 1)) c))) :rule re_unfold_neg_concat_fixed_prefix :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re x (re.++ re.allchar c))))
               (step t1 (cl (or (not (str.< x y)) (not (str.in_re (str.substr x 1 (- (str.len x) 1)) c)))) :rule re_unfold_neg_concat_fixed_prefix :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re x (re.++ re.allchar c))))
               (step t1 (cl (or (not (str.in_re (str.substr x 0 1) re.allchar)) (not (str.< y z)))) :rule re_unfold_neg_concat_fixed_prefix :premises (h1))"#: false,
        }
        "Cannot calculate the regular expression fixed length" {
            r#"(assume h1 (not (str.in_re x (re.++ a d))))
               (step t1 (cl (or (not (str.in_re (str.substr x 0 2) (re.union (str.to_re "xy") re.none))) (not (str.in_re (str.substr x 2 (- (str.len x) 2)) d)))) :rule re_unfold_neg_concat_fixed_prefix :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re x (re.++ (str.to_re x) c))))
               (step t1 (cl (or (not (str.in_re (str.substr x 0 2) (re.union (str.to_re "xy") re.none))) (not (str.in_re (str.substr x 2 (- (str.len x) 2)) d)))) :rule re_unfold_neg_concat_fixed_prefix :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re x (re.++ (re.++ (str.to_re x) b) d))))
               (step t1 (cl (or (not (str.in_re (str.substr x 0 2) (re.union (str.to_re "xy") re.none))) (not (str.in_re (str.substr x 2 (- (str.len x) 2)) d)))) :rule re_unfold_neg_concat_fixed_prefix :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re x (re.++ (re.++ (str.to_re "xy") b) d))))
               (step t1 (cl (or (not (str.in_re (str.substr x 0 2) (re.union (str.to_re "xy") re.none))) (not (str.in_re (str.substr x 2 (- (str.len x) 2)) d)))) :rule re_unfold_neg_concat_fixed_prefix :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re x (re.++ (re.union a (str.to_re x)) c))))
               (step t1 (cl (or (not (str.in_re (str.substr x 0 2) (re.union (str.to_re "xy") re.none))) (not (str.in_re (str.substr x 2 (- (str.len x) 2)) d)))) :rule re_unfold_neg_concat_fixed_prefix :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re x (re.++ (re.union (str.to_re "ab") (str.to_re "ab")) c))))
               (step t1 (cl (or (not (str.in_re (str.substr x 0 2) (re.union (str.to_re "xy") re.none))) (not (str.in_re (str.substr x 2 (- (str.len x) 2)) d)))) :rule re_unfold_neg_concat_fixed_prefix :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re x (re.++ (re.union (str.to_re "ab") (str.to_re "ba") a) c))))
               (step t1 (cl (or (not (str.in_re (str.substr x 0 2) (re.union (str.to_re "xy") re.none))) (not (str.in_re (str.substr x 2 (- (str.len x) 2)) d)))) :rule re_unfold_neg_concat_fixed_prefix :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re x (re.++ (re.union (str.to_re "ab") (str.to_re "aba") (str.to_re "ba")) c))))
               (step t1 (cl (or (not (str.in_re (str.substr x 0 2) (re.union (str.to_re "xy") re.none))) (not (str.in_re (str.substr x 2 (- (str.len x) 2)) d)))) :rule re_unfold_neg_concat_fixed_prefix :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re x (re.++ (re.union (str.to_re "ab") (str.to_re "aba") re.none) c))))
               (step t1 (cl (or (not (str.in_re (str.substr x 0 2) (re.union (str.to_re "xy") re.none))) (not (str.in_re (str.substr x 2 (- (str.len x) 2)) d)))) :rule re_unfold_neg_concat_fixed_prefix :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re x (re.++ (re.inter a (str.to_re x)) c))))
               (step t1 (cl (or (not (str.in_re (str.substr x 0 2) (re.union (str.to_re "xy") re.none))) (not (str.in_re (str.substr x 2 (- (str.len x) 2)) d)))) :rule re_unfold_neg_concat_fixed_prefix :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re x (re.++ (re.inter (str.to_re "ab") (str.to_re "ab")) c))))
               (step t1 (cl (or (not (str.in_re (str.substr x 0 2) (re.union (str.to_re "xy") re.none))) (not (str.in_re (str.substr x 2 (- (str.len x) 2)) d)))) :rule re_unfold_neg_concat_fixed_prefix :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re x (re.++ (re.inter (str.to_re "ab") (str.to_re "ba") a) c))))
               (step t1 (cl (or (not (str.in_re (str.substr x 0 2) (re.union (str.to_re "xy") re.none))) (not (str.in_re (str.substr x 2 (- (str.len x) 2)) d)))) :rule re_unfold_neg_concat_fixed_prefix :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re x (re.++ (re.inter (str.to_re "ab") (str.to_re "aba") (str.to_re "ba")) c))))
               (step t1 (cl (or (not (str.in_re (str.substr x 0 2) (re.union (str.to_re "xy") re.none))) (not (str.in_re (str.substr x 2 (- (str.len x) 2)) d)))) :rule re_unfold_neg_concat_fixed_prefix :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re x (re.++ (re.inter (str.to_re "ab") (str.to_re "aba") re.all) c))))
               (step t1 (cl (or (not (str.in_re (str.substr x 0 2) (re.union (str.to_re "xy") re.none))) (not (str.in_re (str.substr x 2 (- (str.len x) 2)) d)))) :rule re_unfold_neg_concat_fixed_prefix :premises (h1))"#: false,
        }
    }
}

#[test]
fn re_unfold_neg_concat_fixed_suffix() {
    test_cases! {
        definitions = "
            (declare-fun x () String)
            (declare-fun y () String)
            (declare-fun z () String)
            (declare-fun a () RegLan)
            (declare-fun b () RegLan)
            (declare-fun c () RegLan)
            (declare-fun d () RegLan)
        ",
        "Simple working examples" {
            r#"(assume h1 (not (str.in_re x (re.++ a (str.to_re "xyz")))))
               (step t1 (cl (or (not (str.in_re (str.substr x (- (str.len x) 3) 3) (str.to_re "xyz"))) (not (str.in_re (str.substr x 0 (- (str.len x) 3)) a)))) :rule re_unfold_neg_concat_fixed_suffix :premises (h1))"#: true,
            r#"(assume h1 (not (str.in_re x (re.++ b (re.++ (str.to_re "x") (str.to_re "yzw"))))))
               (step t1 (cl (or (not (str.in_re (str.substr x (- (str.len x) 4) 4) (re.++ (str.to_re "x") (str.to_re "yzw")))) (not (str.in_re (str.substr x 0 (- (str.len x) 4)) b)))) :rule re_unfold_neg_concat_fixed_suffix :premises (h1))"#: true,
            r#"(assume h1 (not (str.in_re x (re.++ c re.allchar))))
               (step t1 (cl (or (not (str.in_re (str.substr x (- (str.len x) 1) 1) re.allchar)) (not (str.in_re (str.substr x 0 (- (str.len x) 1)) c)))) :rule re_unfold_neg_concat_fixed_suffix :premises (h1))"#: true,
            r#"(assume h1 (not (str.in_re x (re.++ d (re.union (str.to_re "xy") re.none)))))
               (step t1 (cl (or (not (str.in_re (str.substr x (- (str.len x) 2) 2) (re.union (str.to_re "xy") re.none))) (not (str.in_re (str.substr x 0 (- (str.len x) 2)) d)))) :rule re_unfold_neg_concat_fixed_suffix :premises (h1))"#: true,
            r#"(assume h1 (not (str.in_re x (re.++ a (re.inter (str.to_re "xy") re.all)))))
               (step t1 (cl (or (not (str.in_re (str.substr x (- (str.len x) 2) 2) (re.inter (str.to_re "xy") re.all))) (not (str.in_re (str.substr x 0 (- (str.len x) 2)) a)))) :rule re_unfold_neg_concat_fixed_suffix :premises (h1))"#: true,
            r#"(assume h1 (not (str.in_re x (re.++ b (re.inter (str.to_re "xy") (str.to_re "zw") re.all)))))
               (step t1 (cl (or (not (str.in_re (str.substr x (- (str.len x) 2) 2) (re.inter (str.to_re "xy") (str.to_re "zw") re.all))) (not (str.in_re (str.substr x 0 (- (str.len x) 2)) b)))) :rule re_unfold_neg_concat_fixed_suffix :premises (h1))"#: true,
        }
        "Premise is not of the form (not (str.in_re t R))" {
            r#"(assume h1 (str.in_re x (re.++ a (str.to_re "xyz"))))
               (step t1 (cl (or (not (str.in_re (str.substr x (- (str.len x) 3) 3) (str.to_re "xyz"))) (not (str.in_re (str.substr x 0 (- (str.len x) 3)) a)))) :rule re_unfold_neg_concat_fixed_suffix :premises (h1))"#: false,
            r#"(assume h1 (not (str.< x y)))
               (step t1 (cl (or (not (str.in_re (str.substr x (- (str.len x) 3) 3) (str.to_re "xyz"))) (not (str.in_re (str.substr x 0 (- (str.len x) 3)) a)))) :rule re_unfold_neg_concat_fixed_suffix :premises (h1))"#: false,
        }
        "Regular expression in the premise is not a re.++ application" {
            r#"(assume h1 (not (str.in_re x a)))
               (step t1 (cl (or (not (str.in_re (str.substr x (- (str.len x) 4) 4) (re.++ (str.to_re "x") (str.to_re "yzw")))) (not (str.in_re (str.substr x 0 (- (str.len x) 4)) b)))) :rule re_unfold_neg_concat_fixed_suffix :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re x re.all)))
               (step t1 (cl (or (not (str.in_re (str.substr x (- (str.len x) 4) 4) (re.++ (str.to_re "x") (str.to_re "yzw")))) (not (str.in_re (str.substr x 0 (- (str.len x) 4)) b)))) :rule re_unfold_neg_concat_fixed_suffix :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re x (re.union b (re.++ (str.to_re "x") (str.to_re "yzw"))))))
               (step t1 (cl (or (not (str.in_re (str.substr x (- (str.len x) 4) 4) (re.++ (str.to_re "x") (str.to_re "yzw")))) (not (str.in_re (str.substr x 0 (- (str.len x) 4)) b)))) :rule re_unfold_neg_concat_fixed_suffix :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re x (re.inter b (re.++ (str.to_re "x") (str.to_re "yzw"))))))
               (step t1 (cl (or (not (str.in_re (str.substr x (- (str.len x) 4) 4) (re.++ (str.to_re "x") (str.to_re "yzw")))) (not (str.in_re (str.substr x 0 (- (str.len x) 4)) b)))) :rule re_unfold_neg_concat_fixed_suffix :premises (h1))"#: false,
        }
        "Conclusion is not of the form (or (not (str.in_re suff r_1)) (not (str.in_re pref r_2)))" {
            r#"(assume h1 (not (str.in_re x (re.++ c re.allchar))))
               (step t1 (cl (and (not (str.in_re (str.substr x (- (str.len x) 1) 1) re.allchar)) (not (str.in_re (str.substr x 0 (- (str.len x) 1)) c)))) :rule re_unfold_neg_concat_fixed_suffix :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re x (re.++ c re.allchar))))
               (step t1 (cl (or (str.in_re (str.substr x (- (str.len x) 1) 1) re.allchar) (not (str.in_re (str.substr x 0 (- (str.len x) 1)) c)))) :rule re_unfold_neg_concat_fixed_suffix :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re x (re.++ c re.allchar))))
               (step t1 (cl (or (not (str.in_re (str.substr x (- (str.len x) 1) 1) re.allchar)) (str.in_re (str.substr x 0 (- (str.len x) 1)) c))) :rule re_unfold_neg_concat_fixed_suffix :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re x (re.++ c re.allchar))))
               (step t1 (cl (or (not (str.< x y)) (not (str.in_re (str.substr x 0 (- (str.len x) 1)) c)))) :rule re_unfold_neg_concat_fixed_suffix :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re x (re.++ c re.allchar))))
               (step t1 (cl (or (not (str.in_re (str.substr x (- (str.len x) 1) 1) re.allchar)) (not (str.< y x)))) :rule re_unfold_neg_concat_fixed_suffix :premises (h1))"#: false,
        }
        "Cannot calculate the regular expression fixed length" {
            r#"(assume h1 (not (str.in_re x (re.++ d a))))
               (step t1 (cl (or (not (str.in_re (str.substr x (- (str.len x) 2) 2) (re.union (str.to_re "xy") re.none))) (not (str.in_re (str.substr x 0 (- (str.len x) 2)) d)))) :rule re_unfold_neg_concat_fixed_suffix :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re x (re.++ d (str.to_re x)))))
               (step t1 (cl (or (not (str.in_re (str.substr x (- (str.len x) 2) 2) (re.union (str.to_re "xy") re.none))) (not (str.in_re (str.substr x 0 (- (str.len x) 2)) d)))) :rule re_unfold_neg_concat_fixed_suffix :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re x (re.++ d (re.++ (str.to_re "xy") a)))))
               (step t1 (cl (or (not (str.in_re (str.substr x (- (str.len x) 2) 2) (re.union (str.to_re "xy") re.none))) (not (str.in_re (str.substr x 0 (- (str.len x) 2)) d)))) :rule re_unfold_neg_concat_fixed_suffix :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re x (re.++ d (re.++ (str.to_re x) b)))))
               (step t1 (cl (or (not (str.in_re (str.substr x (- (str.len x) 2) 2) (re.union (str.to_re "xy") re.none))) (not (str.in_re (str.substr x 0 (- (str.len x) 2)) d)))) :rule re_unfold_neg_concat_fixed_suffix :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re x (re.++ d (re.union (str.to_re "x") b)))))
               (step t1 (cl (or (not (str.in_re (str.substr x (- (str.len x) 2) 2) (re.union (str.to_re "xy") re.none))) (not (str.in_re (str.substr x 0 (- (str.len x) 2)) d)))) :rule re_unfold_neg_concat_fixed_suffix :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re x (re.++ d (re.union (str.to_re "xy") (str.to_re "xy"))))))
               (step t1 (cl (or (not (str.in_re (str.substr x (- (str.len x) 2) 2) (re.union (str.to_re "xy") re.none))) (not (str.in_re (str.substr x 0 (- (str.len x) 2)) d)))) :rule re_unfold_neg_concat_fixed_suffix :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re x (re.++ d (re.union a (str.to_re "xy") (str.to_re "yx"))))))
               (step t1 (cl (or (not (str.in_re (str.substr x (- (str.len x) 2) 2) (re.union (str.to_re "xy") re.none))) (not (str.in_re (str.substr x 0 (- (str.len x) 2)) d)))) :rule re_unfold_neg_concat_fixed_suffix :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re x (re.++ d (re.union (str.to_re "xy") (str.to_re "xyz") (str.to_re "yz"))))))
               (step t1 (cl (or (not (str.in_re (str.substr x (- (str.len x) 2) 2) (re.union (str.to_re "xy") re.none))) (not (str.in_re (str.substr x 0 (- (str.len x) 2)) d)))) :rule re_unfold_neg_concat_fixed_suffix :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re x (re.++ d (re.union re.none (str.to_re "xy") (str.to_re "xyz"))))))
               (step t1 (cl (or (not (str.in_re (str.substr x (- (str.len x) 2) 2) (re.union (str.to_re "xy") re.none))) (not (str.in_re (str.substr x 0 (- (str.len x) 2)) d)))) :rule re_unfold_neg_concat_fixed_suffix :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re x (re.++ d (re.inter (str.to_re "x") b)))))
               (step t1 (cl (or (not (str.in_re (str.substr x (- (str.len x) 2) 2) (re.union (str.to_re "xy") re.none))) (not (str.in_re (str.substr x 0 (- (str.len x) 2)) d)))) :rule re_unfold_neg_concat_fixed_suffix :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re x (re.++ d (re.inter (str.to_re "xy") (str.to_re "xy"))))))
               (step t1 (cl (or (not (str.in_re (str.substr x (- (str.len x) 2) 2) (re.union (str.to_re "xy") re.none))) (not (str.in_re (str.substr x 0 (- (str.len x) 2)) d)))) :rule re_unfold_neg_concat_fixed_suffix :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re x (re.++ d (re.inter a (str.to_re "xy") (str.to_re "yx"))))))
               (step t1 (cl (or (not (str.in_re (str.substr x (- (str.len x) 2) 2) (re.union (str.to_re "xy") re.none))) (not (str.in_re (str.substr x 0 (- (str.len x) 2)) d)))) :rule re_unfold_neg_concat_fixed_suffix :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re x (re.++ d (re.inter (str.to_re "xy") (str.to_re "xyz") (str.to_re "yz"))))))
               (step t1 (cl (or (not (str.in_re (str.substr x (- (str.len x) 2) 2) (re.union (str.to_re "xy") re.none))) (not (str.in_re (str.substr x 0 (- (str.len x) 2)) d)))) :rule re_unfold_neg_concat_fixed_suffix :premises (h1))"#: false,
            r#"(assume h1 (not (str.in_re x (re.++ d (re.inter re.all (str.to_re "xy") (str.to_re "xyz"))))))
               (step t1 (cl (or (not (str.in_re (str.substr x (- (str.len x) 2) 2) (re.union (str.to_re "xy") re.none))) (not (str.in_re (str.substr x 0 (- (str.len x) 2)) d)))) :rule re_unfold_neg_concat_fixed_suffix :premises (h1))"#: false,
        }
    }
}

#[test]
fn re_kleene_star_unfold_pos() {
    test_cases! {
        definitions = "
            (declare-fun x () String)
            (declare-fun y () String)
            (declare-fun z () String)
            (declare-fun a () RegLan)
            (declare-fun b () RegLan)
            (declare-fun c () RegLan)
        ",
        "Simple working examples" {
            r#"(define-fun kk_2 () String (choice ((x String)) (exists ((k_0 String) (R_0 RegLan) (k_1 String) (R_1 RegLan) (R_2 RegLan)) (and (= x (str.++ k_0 k_1 x)) (str.in_re k_0 R_0) (str.in_re k_1 R_1) (str.in_re x R_2)))))
               (define-fun kk_1 () String (choice ((x String)) (exists ((k_0 String) (R_0 RegLan) (R_1 RegLan) (R_2 RegLan)) (and (= x (str.++ k_0 x kk_2)) (str.in_re k_0 R_0) (str.in_re x R_1) (str.in_re kk_2 R_2)))))
               (define-fun kk_0 () String (choice ((x String)) (exists ((R_0 RegLan) (R_1 RegLan) (R_2 RegLan)) (and (= x (str.++ x kk_1 kk_2)) (str.in_re x R_0) (str.in_re kk_1 R_1) (str.in_re kk_2 R_2)))))
               (assume h1 (str.in_re x (re.* a)))
               (step t1 (cl (or (= x "") (str.in_re x a) (and (and (= x (str.++ kk_0 kk_1 kk_2)) (str.in_re kk_0 (re.++ a (re.* a) a)) (and (str.in_re kk_1 (re.++ (re.* a) a)) (and (str.in_re kk_2 a) true))) (not (= kk_0 "")) (not (= kk_2 ""))))) :rule re_kleene_star_unfold_pos :premises (h1))"#: true,
            r#"(define-fun choice_term () String (choice ((x String)) (exists ((k_0 String) (R_0 RegLan) (R_1 RegLan)) (and (= y (str.++ k_0 x)) (str.in_re k_0 R_0) (str.in_re x R_1)))))
               (assume h1 (str.in_re y (re.* (str.to_re "abc"))))
               (step t1 (cl (or (= y "") (str.in_re y (str.to_re "abc")) (and (and (= y (str.++ "abc" choice_term "abc")) (str.in_re choice_term (re.++ (re.* (str.to_re "abc")) (str.to_re "abc"))) true) (not (= "abc" "")) (not (= "abc" ""))))) :rule re_kleene_star_unfold_pos :premises (h1))"#: true,
        }
        "Premise is not of the form (str.in_re t R)" {
            r#"(define-fun kk_2 () String (choice ((x String)) (exists ((k_0 String) (R_0 RegLan) (k_1 String) (R_1 RegLan) (R_2 RegLan)) (and (= x (str.++ k_0 k_1 x)) (str.in_re k_0 R_0) (str.in_re k_1 R_1) (str.in_re x R_2)))))
               (define-fun kk_1 () String (choice ((x String)) (exists ((k_0 String) (R_0 RegLan) (R_1 RegLan) (R_2 RegLan)) (and (= x (str.++ k_0 x kk_2)) (str.in_re k_0 R_0) (str.in_re x R_1) (str.in_re kk_2 R_2)))))
               (define-fun kk_0 () String (choice ((x String)) (exists ((R_0 RegLan) (R_1 RegLan) (R_2 RegLan)) (and (= x (str.++ x kk_1 kk_2)) (str.in_re x R_0) (str.in_re kk_1 R_1) (str.in_re kk_2 R_2)))))
               (assume h1 (not (str.in_re x (re.* a))))
               (step t1 (cl (or (= x "") (str.in_re x a) (and (and (= x (str.++ kk_0 kk_1 kk_2)) (str.in_re kk_0 (re.++ a (re.* a) a)) (and (str.in_re kk_1 (re.++ (re.* a) a)) (and (str.in_re kk_2 a) true))) (not (= kk_0 "")) (not (= kk_2 ""))))) :rule re_kleene_star_unfold_pos :premises (h1))"#: false,
        }
        "Conclusion is not of the form (or (= t_1 \"\") (str.in_re t_2 t_3) (and t_4 (not (= t_5 \"\")) (not (= t_6 \"\"))))" {
            r#"(define-fun choice_term () String (choice ((x String)) (exists ((k_0 String) (R_0 RegLan) (R_1 RegLan)) (and (= y (str.++ k_0 x)) (str.in_re k_0 R_0) (str.in_re x R_1)))))
               (assume h1 (str.in_re y (re.* (str.to_re "abc"))))
               (step t1 (cl (and (= y "") (str.in_re y (str.to_re "abc")) (and (and (= y (str.++ "abc" choice_term "abc")) (str.in_re choice_term (re.++ (re.* (str.to_re "abc")) (str.to_re "abc"))) true) (not (= "abc" "")) (not (= "abc" ""))))) :rule re_kleene_star_unfold_pos :premises (h1))"#: false,
            r#"(define-fun choice_term () String (choice ((x String)) (exists ((k_0 String) (R_0 RegLan) (R_1 RegLan)) (and (= y (str.++ k_0 x)) (str.in_re k_0 R_0) (str.in_re x R_1)))))
               (assume h1 (str.in_re y (re.* (str.to_re "abc"))))
               (step t1 (cl (or (not (= y "")) (str.in_re y (str.to_re "abc")) (and (and (= y (str.++ "abc" choice_term "abc")) (str.in_re choice_term (re.++ (re.* (str.to_re "abc")) (str.to_re "abc"))) true) (not (= "abc" "")) (not (= "abc" ""))))) :rule re_kleene_star_unfold_pos :premises (h1))"#: false,
            r#"(define-fun choice_term () String (choice ((x String)) (exists ((k_0 String) (R_0 RegLan) (R_1 RegLan)) (and (= y (str.++ k_0 x)) (str.in_re k_0 R_0) (str.in_re x R_1)))))
               (assume h1 (str.in_re y (re.* (str.to_re "abc"))))
               (step t1 (cl (or (= y "") (not (str.in_re y (str.to_re "abc"))) (and (and (= y (str.++ "abc" choice_term "abc")) (str.in_re choice_term (re.++ (re.* (str.to_re "abc")) (str.to_re "abc"))) true) (not (= "abc" "")) (not (= "abc" ""))))) :rule re_kleene_star_unfold_pos :premises (h1))"#: false,
            r#"(define-fun choice_term () String (choice ((x String)) (exists ((k_0 String) (R_0 RegLan) (R_1 RegLan)) (and (= y (str.++ k_0 x)) (str.in_re k_0 R_0) (str.in_re x R_1)))))
               (assume h1 (str.in_re y (re.* (str.to_re "abc"))))
               (step t1 (cl (or (= y "") (str.in_re y (str.to_re "abc")) (or (and (= y (str.++ "abc" choice_term "abc")) (str.in_re choice_term (re.++ (re.* (str.to_re "abc")) (str.to_re "abc"))) true) (not (= "abc" "")) (not (= "abc" ""))))) :rule re_kleene_star_unfold_pos :premises (h1))"#: false,
            r#"(define-fun choice_term () String (choice ((x String)) (exists ((k_0 String) (R_0 RegLan) (R_1 RegLan)) (and (= y (str.++ k_0 x)) (str.in_re k_0 R_0) (str.in_re x R_1)))))
               (assume h1 (str.in_re y (re.* (str.to_re "abc"))))
               (step t1 (cl (or (= y "") (str.in_re y (str.to_re "abc")) (and (and (= y (str.++ "abc" choice_term "abc")) (str.in_re choice_term (re.++ (re.* (str.to_re "abc")) (str.to_re "abc"))) true) (= "abc" "") (not (= "abc" ""))))) :rule re_kleene_star_unfold_pos :premises (h1))"#: false,
            r#"(define-fun choice_term () String (choice ((x String)) (exists ((k_0 String) (R_0 RegLan) (R_1 RegLan)) (and (= y (str.++ k_0 x)) (str.in_re k_0 R_0) (str.in_re x R_1)))))
               (assume h1 (str.in_re y (re.* (str.to_re "abc"))))
               (step t1 (cl (or (= y "") (str.in_re y (str.to_re "abc")) (and (and (= y (str.++ "abc" choice_term "abc")) (str.in_re choice_term (re.++ (re.* (str.to_re "abc")) (str.to_re "abc"))) true) (not (= "abc" "")) (= "abc" "")))) :rule re_kleene_star_unfold_pos :premises (h1))"#: false,
        }
    }
}

#[test]
fn re_concat_unfold_pos() {
    test_cases! {
        definitions = "
            (declare-fun x () String)
            (declare-fun y () String)
            (declare-fun z () String)
            (declare-fun a () RegLan)
            (declare-fun b () RegLan)
            (declare-fun c () RegLan)
        ",
        "Simple working examples" {
            r#"(assume h1 (str.in_re x (re.++ (str.to_re "a") (str.to_re "b") (str.to_re "c"))))
               (step t1 (cl (= x (str.++ "a" "b" "c"))) :rule re_concat_unfold_pos :premises (h1))"#: true,
            r#"(define-fun choice_term () String (choice ((x String)) (exists ((k_0 String) (R_0 RegLan) (R_1 RegLan)) (and (= y (str.++ k_0 x)) (str.in_re k_0 R_0) (str.in_re x R_1)))))
               (assume h1 (str.in_re y (re.++ (str.to_re "a") b (str.to_re "c"))))
               (step t1 (cl (and (= y (str.++ "a" choice_term "c")) (and (str.in_re choice_term (re.++ b (str.to_re "c"))) true))) :rule re_concat_unfold_pos :premises (h1))"#: true,
            r#"(define-fun kk_1 () String (choice ((x String)) (exists ((k_0 String) (R_0 RegLan) (R_1 RegLan)) (and (= z (str.++ k_0 x)) (str.in_re k_0 R_0) (str.in_re x R_1)))))
               (define-fun kk_0 () String (choice ((x String)) (exists ((R_0 RegLan) (R_1 RegLan)) (and (= z (str.++ x kk_1)) (str.in_re x R_0) (str.in_re kk_1 R_1)))))
               (assume h1 (str.in_re z (re.++ a b)))
               (step t1 (cl (and (= z (str.++ kk_0 kk_1)) (and (str.in_re kk_0 (re.++ a b)) (and (str.in_re kk_1 b) true)))) :rule re_concat_unfold_pos :premises (h1))"#: true,
        }
        "Premise is not of the form (str.in_re t R)" {
            r#"(assume h1 (not (str.in_re x (re.++ (str.to_re "a") (str.to_re "b") (str.to_re "c")))))
               (step t1 (cl (= x (str.++ "a" "b" "c"))) :rule re_concat_unfold_pos :premises (h1))"#: false,
        }
        "Conclusion is not of the form " {
            r#"(assume h1 (str.in_re x (re.++ (str.to_re "a") (str.to_re "b") (str.to_re "c"))))
               (step t1 (cl (not (= x (str.++ "a" "b" "c")))) :rule re_concat_unfold_pos :premises (h1))"#: false,
            r#"(assume h1 (str.in_re x (re.++ (str.to_re "a") (str.to_re "b") (str.to_re "c"))))
               (step t1 (cl (= x "a")) :rule re_concat_unfold_pos :premises (h1))"#: false,
            r#"(define-fun choice_term () String (choice ((x String)) (exists ((k_0 String) (R_0 RegLan) (R_1 RegLan)) (and (= y (str.++ k_0 x)) (str.in_re k_0 R_0) (str.in_re x R_1)))))
               (assume h1 (str.in_re y (re.++ (str.to_re "a") b (str.to_re "c"))))
               (step t1 (cl (or (= y (str.++ "a" choice_term "c")) (and (str.in_re choice_term (re.++ b (str.to_re "c"))) true))) :rule re_concat_unfold_pos :premises (h1))"#: false,
            r#"(define-fun choice_term () String (choice ((x String)) (exists ((k_0 String) (R_0 RegLan) (R_1 RegLan)) (and (= y (str.++ k_0 x)) (str.in_re k_0 R_0) (str.in_re x R_1)))))
               (assume h1 (str.in_re y (re.++ (str.to_re "a") b (str.to_re "c"))))
               (step t1 (cl (and (not (= y (str.++ "a" choice_term "c"))) (and (str.in_re choice_term (re.++ b (str.to_re "c"))) true))) :rule re_concat_unfold_pos :premises (h1))"#: false,
            r#"(define-fun choice_term () String (choice ((x String)) (exists ((k_0 String) (R_0 RegLan) (R_1 RegLan)) (and (= y (str.++ k_0 x)) (str.in_re k_0 R_0) (str.in_re x R_1)))))
               (assume h1 (str.in_re y (re.++ (str.to_re "a") b (str.to_re "c"))))
               (step t1 (cl (and (= y (str.++ "a" choice_term "c")) (or (str.in_re choice_term (re.++ b (str.to_re "c"))) true))) :rule re_concat_unfold_pos :premises (h1))"#: false,
        }
    }
}
