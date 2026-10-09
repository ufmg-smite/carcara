(set-logic ALL)
(declare-fun x () (_ BitVec 2))(declare-fun z () (_ BitVec 1))
(assert (= ((_ zero_extend 18446744073709551615) x) z))
(check-sat)
