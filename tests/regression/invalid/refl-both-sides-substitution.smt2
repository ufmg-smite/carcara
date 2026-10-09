(set-logic UFLIA)
(declare-fun x () Int)
(assert (not (forall ((y Int)) (= x y))))
(check-sat)
