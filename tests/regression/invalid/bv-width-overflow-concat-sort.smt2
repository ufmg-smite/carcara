(set-logic ALL)
(declare-fun x () (_ BitVec 18446744073709551615))(declare-fun y () (_ BitVec 2))(declare-fun z () (_ BitVec 1))
(assert (= (concat x y) z))
(check-sat)
