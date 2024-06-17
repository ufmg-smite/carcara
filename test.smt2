(set-logic ALL)

(declare-const a Bool)
(declare-const b Bool)
(declare-const c Bool)
(declare-const d Bool)
(declare-const p1 Bool)
(declare-const p2 Bool)
(declare-const p3 Bool)
(define-fun f ((a Bool) (b Bool)) Bool a)

(assert (= a b))
(assert (= c d))
(assert (and p1 true))
(assert (or (not p1) (and p2 p3)))
(assert (or (not p3) (not (= (f a c) (f b d)))))

(check-sat)