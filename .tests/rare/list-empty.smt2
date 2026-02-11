; EXPECT: unsat
(set-logic ALL)
(declare-fun z () Bool)
(assert (and (not (= z z)) true))
(check-sat)
