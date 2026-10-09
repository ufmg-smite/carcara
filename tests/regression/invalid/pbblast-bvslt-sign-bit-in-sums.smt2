(set-logic ALL)
(declare-const x4 (_ BitVec 4))
(declare-const y4 (_ BitVec 4))
(assert (not (= (bvslt x4 y4) (>= (+ (- (+ (* 1 ((_ @int_of 0) y4)) (* 2 ((_ @int_of 1) y4)) (* 4 ((_ @int_of 2) y4)) (* 8 ((_ @int_of 3) y4))) (* 8 ((_ @int_of 3) y4))) (- (* 8 ((_ @int_of 3) x4)) (+ (* 1 ((_ @int_of 0) x4)) (* 2 ((_ @int_of 1) x4)) (* 4 ((_ @int_of 2) x4)) (* 8 ((_ @int_of 3) x4))))) 1))))
