(set-logic QF_LIA)
(declare-fun x1 () Int)
(declare-fun x2 () Int)

(assert (>= (+ (* 5 x1) (* -3 x2)) 2))
(assert (not (>= (+ (* 2 x1) (* -3 x2)) 2)))
