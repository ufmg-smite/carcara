(set-logic ALL)
(declare-const x2 (_ BitVec 2))
(declare-const y2 (_ BitVec 2))
(assert (not (= (bvult x2 y2) (>= (- (* 1 ((_ @int_of 0) y2)) (* 1 ((_ @int_of 0) x2))) 1))))
