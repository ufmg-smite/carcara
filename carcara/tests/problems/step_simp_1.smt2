(echo "run with --disable-simp")
(set-option :produce-proofs true)
(set-logic QF_UF)

(declare-sort S 0)
(declare-const A S)
(declare-fun f (S) Bool)
(declare-fun g (S) Bool)

; should produce two not_not elimination step
(assert (not (not (not (not (f A))))))
(assert (g A))
(assert (or (not (g A)) (not (f A)) (not (f A))))

(check-sat)
(get-proof)