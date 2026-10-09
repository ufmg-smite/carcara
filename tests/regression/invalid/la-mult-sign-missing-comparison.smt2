(set-logic QF_NRA)
(declare-fun a () Real)
(declare-fun b () Real)
(assert (not (=> (> a 0.0) (> (* a b) 0.0))))
