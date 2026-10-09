(set-logic QF_BV)
(assert (distinct ((_ zero_extend 18446744073709551615) #b1) ((_ zero_extend 18446744073709551615) #b0)))
(check-sat)
