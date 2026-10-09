(set-logic ALL)

(assert (= ((_ int_to_bv 18446744073709551616) 5) ((_ int_to_bv 18446744073709551616) 5)))
(check-sat)
