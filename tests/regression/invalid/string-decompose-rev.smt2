(set-logic QF_SLIA)
(assert (>= (str.len "ab") 2))
(check-sat)
