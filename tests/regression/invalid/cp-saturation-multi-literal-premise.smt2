(set-logic QF_LIA)
(declare-fun x1 () Int)
(declare-fun x2 () Int)

(assert (or (>= (* 2 x1) 1) (>= (* 2 x2) 1)))
(assert (not (>= (* 1 x1) 1)))
