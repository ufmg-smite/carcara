(set-logic QF_UF)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun f (U) U)
(declare-fun p () Bool)

(assert (= a b))
(assert (or p (not (= (f a) (f b)))))
(assert (not p))
(check-sat)
(exit)

; ++++++++++++++++++++++++

; (proof
;   (SCOPE
;     (CHAIN_RESOLUTION
;       (REORDERING ;; (or (not (= a b)) (= (f a) (f b)))
;         (IMPLIES_ELIM ;; (or (not (= a b)) (= (f a) (f b)))
;           (SCOPE ;; (=> (= a b) (= (f a) (f b)))
;             (CONG ;; (= (f a) (f b))
;               (SYMM ;; (= a b)
;                 (SYMM ;; (= b a)
;                   (ASSUME |:args| ((= a b)))))
;               |:args| (APPLY_UF f))
;             |:args| ((= a b))))
;         |:args| ((or (= (f a) (f b)) (not (= a b)))))
;       (CHAIN_RESOLUTION ;; (not (= (f a) (f b)))
;         (ASSUME |:args| ((or p (not (= (f a) (f b))))))
;         (ASSUME |:args| ((not p)))
;         |:args| (true p))
;       (ASSUME |:args| ((= a b)))
;       |:args| (true (= (f a) (f b)) false (= a b)))
;     |:args| ((= a b) (or p (not (= (f a) (f b)))) (not p)))
; )
