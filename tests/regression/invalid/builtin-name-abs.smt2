(set-logic QF_UFLIA)
(declare-fun abs (Int) Int)
(assert (= (abs 1) 2))
(check-sat)
