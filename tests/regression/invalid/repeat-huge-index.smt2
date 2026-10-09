(set-logic QF_BV)
(declare-fun x () (_ BitVec 2))
(assert (= ((_ repeat 18446744073709551615) x) ((_ repeat 18446744073709551615) x)))
(check-sat)
