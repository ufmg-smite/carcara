(set-logic ALL)
(assert (let ((y (forall ((b Bool)) b))) y))
(check-sat)
