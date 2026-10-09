(set-logic QF_S)
(declare-fun u () String)
(declare-fun v () String)
(assert (not (= (str.++ u v) (str.++ v u))))
