(set-logic QF_BV)
(declare-fun x () (_ BitVec 1))
(assert (= x x))
(check-sat)
