(set-logic ALL)
(declare-fun y () (Array Int (_ BitVec 1)))
(assert (= y ((as const (Array Int (_ BitVec 99999999999999999999999))) #b0)))
