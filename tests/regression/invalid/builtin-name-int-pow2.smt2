(set-logic QF_UFNIA)
(declare-fun int.pow2 (Int) Int)
(assert (= (int.pow2 1) 5))
(check-sat)
