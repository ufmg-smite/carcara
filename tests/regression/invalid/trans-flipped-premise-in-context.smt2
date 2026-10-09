(set-logic QF_LIA)
(declare-fun x () Int)
(assert (not (= x 5)))
(check-sat)
