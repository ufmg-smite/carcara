(set-logic ALL)

(assert (= ((_ int_to_bv (- 1)) 5) ((_ int_to_bv (- 1)) 5)))
(check-sat)
