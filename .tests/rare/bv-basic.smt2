; EXPECT: unsat
(set-logic ALL)
(declare-fun x () (_ BitVec 8))
(assert (and (not (= (bvxor x x) (_ bv0 8))) true))
(check-sat)
