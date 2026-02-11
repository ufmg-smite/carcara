; EXPECT: unsat
(set-logic ALL)
(declare-fun p () Bool)
(declare-fun z () Bool)
(assert (and (not (= (or p z) (or p z))) true))
(check-sat)
