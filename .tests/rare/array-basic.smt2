; EXPECT: unsat
(set-logic ALL)
(declare-fun a () (Array Int Int))
(declare-fun i () Int)
(declare-fun v () Int)
(assert (and (not (= (select (store a i v) i) v)) true))
(check-sat)
