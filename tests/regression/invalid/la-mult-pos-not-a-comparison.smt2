(set-logic QF_LIA)
(declare-fun p () Bool)
(declare-fun q () Bool)
(assert (not (=> (and (> 2 0) (or p q)) (or p q))))
