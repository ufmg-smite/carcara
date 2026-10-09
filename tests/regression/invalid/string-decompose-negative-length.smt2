(set-logic QF_SLIA)
(assert (>= (str.len "") (- 1)))
(check-sat)
