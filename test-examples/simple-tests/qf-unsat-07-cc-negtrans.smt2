(set-logic QF_UF)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)
(declare-fun d () U)
(declare-fun f (U U) U)

(assert (not (= a (f d b))))
(assert (= (f a a) (f d b)))
(assert (= (f c b) (f a a)))

(assert (= a (f c b)))

(check-sat)
