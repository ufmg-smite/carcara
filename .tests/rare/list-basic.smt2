; EXPECT: unsat
(set-logic ALL)
(declare-fun p () Bool)
(declare-fun q () Bool)
(declare-fun z () Bool)
(assert (and (not (= (or p q z) (or p q z))) true))
(check-sat)
