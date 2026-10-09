(set-logic HO_ALL)
(declare-fun y () Int)
(assert (not (= ((lambda ((x Int) (y Int)) (+ x y)) y) (lambda ((y Int)) (+ y y)))))
