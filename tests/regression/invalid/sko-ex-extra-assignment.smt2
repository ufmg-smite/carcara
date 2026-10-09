(set-logic UFLIA)
(declare-fun z () Int)
(assert (not (= z 5)))
(check-sat)
