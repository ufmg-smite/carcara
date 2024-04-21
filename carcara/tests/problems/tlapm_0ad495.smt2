;; Proof obligation:
;;	ASSUME NEW CONSTANT CONSTANT_Client_,
;;	       NEW CONSTANT CONSTANT_Resource_,
;;	       NEW VARIABLE VARIABLE_unsat_,
;;	       NEW VARIABLE VARIABLE_alloc_,
;;	       ASSUME STATE_TypeInvariant_ ,
;;	              ACTION_Next_ 
;;	       PROVE  ?h12c0a ,
;;	       STATE_TypeInvariant_ /\ ?h6fbaa = STATE_vars_ => ?h12c0a 
;;	PROVE  STATE_TypeInvariant_ /\ (ACTION_Next_ \/ ?h6fbaa = STATE_vars_)
;;	       => ?h12c0a
;; TLA+ Proof Manager 1.5.0
;; Proof obligation #5
;; Generated from file "/home/rosalied/Documents/work/thesis-eval/tla_specs/tlaps_examples/Allocator.tla", line 165, characters 3-4

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun smt__TLA______Anon___OPAQUE___h12c0a () Idv)

(declare-fun smt__TLA______Anon___OPAQUE___h6fbaa () Idv)

(declare-fun smt__TLA______TrigEq___Idv (Idv Idv) Bool)

(declare-fun smt__TLA______Tt___Idv () Idv)

;; Axiom: ExtTrigEqDef Idv
(assert
  (!
    (forall ((smt__x Idv) (smt__y Idv))
      (! (= (smt__TLA______TrigEq___Idv smt__x smt__y) (= smt__x smt__y))
        :pattern ((smt__TLA______TrigEq___Idv smt__x smt__y))))
    :named |ExtTrigEqDef Idv|))

; hidden fact

; hidden fact

; omitted declaration of 'CONSTANT_EnabledWrapper_' (second-order)

; omitted declaration of 'CONSTANT_CdotWrapper_' (second-order)

(declare-fun smt__CONSTANT___Client___ () Idv)

(declare-fun smt__CONSTANT___Resource___ () Idv)

(declare-fun smt__VARIABLE___unsat___ () Idv)

(declare-fun smt__VARIABLE___unsat______prime () Idv)

(declare-fun smt__VARIABLE___alloc___ () Idv)

(declare-fun smt__VARIABLE___alloc______prime () Idv)

(declare-fun smt__STATE___TypeInvariant___ () Idv)

(declare-fun smt__STATE___available___ () Idv)

(declare-fun smt__STATE___Init___ () Idv)

(declare-fun smt__ACTION___Request___ (Idv Idv) Idv)

(declare-fun smt__ACTION___Allocate___ (Idv Idv) Idv)

(declare-fun smt__ACTION___Return___ (Idv Idv) Idv)

(declare-fun smt__ACTION___Next___ () Idv)

(declare-fun smt__STATE___vars___ () Idv)

(declare-fun smt__TEMPORAL___SimpleAllocator___ () Idv)

(declare-fun smt__STATE___Mutex___ () Idv)

(declare-fun smt__TEMPORAL___ClientsWillReturn___ () Idv)

(declare-fun smt__TEMPORAL___ClientsWillObtain___ () Idv)

(declare-fun smt__TEMPORAL___InfOftenSatisfied___ () Idv)

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

(assert
  (=> (= smt__STATE___TypeInvariant___ smt__TLA______Tt___Idv)
    (=> (= smt__ACTION___Next___ smt__TLA______Tt___Idv)
      (= smt__TLA______Anon___OPAQUE___h12c0a smt__TLA______Tt___Idv))))

(assert
  (=>
    (and (= smt__STATE___TypeInvariant___ smt__TLA______Tt___Idv)
      (smt__TLA______TrigEq___Idv smt__TLA______Anon___OPAQUE___h6fbaa
        smt__STATE___vars___))
    (= smt__TLA______Anon___OPAQUE___h12c0a smt__TLA______Tt___Idv)))

;; Goal
(assert
  (!
    (not
      (=>
        (and (= smt__STATE___TypeInvariant___ smt__TLA______Tt___Idv)
          (or (= smt__ACTION___Next___ smt__TLA______Tt___Idv)
            (smt__TLA______TrigEq___Idv smt__TLA______Anon___OPAQUE___h6fbaa
              smt__STATE___vars___)))
        (= smt__TLA______Anon___OPAQUE___h12c0a smt__TLA______Tt___Idv)))
    :named |Goal|))

(check-sat)
(get-proof)
