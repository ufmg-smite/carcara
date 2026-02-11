; EXPECT: unsat
(set-logic ALL)
(declare-fun b0 () (_ BitVec 1))
(declare-fun b1 () (_ BitVec 1))
(declare-fun y () (_ BitVec 1))
(assert (and (not (= (concat b0 b1 y) (concat b0 b1 y))) true))
(check-sat)
