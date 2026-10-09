(set-logic QF_SLIA)
(declare-const x String)
(assert (str.in_re x (re.++ (re.* (str.to_re "a")) (re.* (str.to_re "b")))))
(check-sat)
