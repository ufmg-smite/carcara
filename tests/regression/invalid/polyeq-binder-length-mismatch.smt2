(set-logic LIA)
(declare-fun y () Int)
(assert (exists ((x Int) (y Int)) (and (= x 0) (= y 1))))
(assert (not (exists ((x Int)) (and (= x 0) (= y 1)))))
