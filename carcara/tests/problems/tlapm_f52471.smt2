;; Proof obligation:
;;	ASSUME NEW CONSTANT CONSTANT_Client_,
;;	       NEW CONSTANT CONSTANT_Resource_,
;;	       NEW VARIABLE VARIABLE_unsat_,
;;	       NEW VARIABLE VARIABLE_alloc_,
;;	       \E CONSTANT_c_ \in CONSTANT_Client_,
;;	          CONSTANT_S_ \in SUBSET CONSTANT_Resource_ :
;;	          ACTION_Request_(CONSTANT_c_, CONSTANT_S_)
;;	          \/ ACTION_Allocate_(CONSTANT_c_, CONSTANT_S_)
;;	          \/ ACTION_Return_(CONSTANT_c_, CONSTANT_S_) 
;;	PROVE  \E CONSTANT_c_ \in CONSTANT_Client_,
;;	          CONSTANT_S_ \in SUBSET CONSTANT_Resource_ :
;;	          \/ ACTION_Request_(CONSTANT_c_, CONSTANT_S_)
;;	          \/ ACTION_Allocate_(CONSTANT_c_, CONSTANT_S_)
;;	          \/ ACTION_Return_(CONSTANT_c_, CONSTANT_S_)
;; TLA+ Proof Manager 1.5.0
;; Proof obligation #13
;; Generated from file "/home/rosalied/Documents/work/thesis-eval/tla_specs/tlaps_examples/Allocator.tla", line 156, characters 5-6

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun smt__TLA______Mem (Idv Idv) Bool)

(declare-fun smt__TLA______SetExtTrigger (Idv Idv) Bool)

(declare-fun smt__TLA______Subset (Idv) Idv)

(declare-fun smt__TLA______SubsetEq (Idv Idv) Bool)

(declare-fun smt__TLA______Tt___Idv () Idv)

;; Axiom: SetExt
(assert
  (!
    (forall ((smt__x Idv) (smt__y Idv))
      (!
        (=>
          (forall ((smt__z Idv))
            (= (smt__TLA______Mem smt__z smt__x)
              (smt__TLA______Mem smt__z smt__y))) (= smt__x smt__y))
        :pattern ((smt__TLA______SetExtTrigger smt__x smt__y))))
    :named |SetExt|))

;; Axiom: SubsetEqIntro
(assert
  (!
    (forall ((smt__x Idv) (smt__y Idv))
      (!
        (=>
          (forall ((smt__z Idv))
            (=> (smt__TLA______Mem smt__z smt__x)
              (smt__TLA______Mem smt__z smt__y)))
          (smt__TLA______SubsetEq smt__x smt__y))
        :pattern ((smt__TLA______SubsetEq smt__x smt__y))))
    :named |SubsetEqIntro|))

;; Axiom: SubsetEqElim
(assert
  (!
    (forall ((smt__x Idv) (smt__y Idv) (smt__z Idv))
      (!
        (=>
          (and (smt__TLA______SubsetEq smt__x smt__y)
            (smt__TLA______Mem smt__z smt__x))
          (smt__TLA______Mem smt__z smt__y))
        :pattern ((smt__TLA______SubsetEq smt__x smt__y)
                   (smt__TLA______Mem smt__z smt__x)))) :named |SubsetEqElim|))

;; Axiom: SubsetDefAlt
(assert
  (!
    (forall ((smt__a Idv) (smt__x Idv))
      (!
        (= (smt__TLA______Mem smt__x (smt__TLA______Subset smt__a))
          (smt__TLA______SubsetEq smt__x smt__a))
        :pattern ((smt__TLA______Mem smt__x (smt__TLA______Subset smt__a)))
        :pattern ((smt__TLA______SubsetEq smt__x smt__a)
                   (smt__TLA______Subset smt__a)))) :named |SubsetDefAlt|))

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

; hidden fact

; hidden fact

; hidden fact

; hidden fact

(assert
  (exists ((smt__CONSTANT___c___ Idv) (smt__CONSTANT___S___ Idv))
    (and (smt__TLA______Mem smt__CONSTANT___c___ smt__CONSTANT___Client___)
      (smt__TLA______Mem smt__CONSTANT___S___
        (smt__TLA______Subset smt__CONSTANT___Resource___))
      (or
        (or
          (=
            (smt__ACTION___Request___ smt__CONSTANT___c___
              smt__CONSTANT___S___) smt__TLA______Tt___Idv)
          (=
            (smt__ACTION___Allocate___ smt__CONSTANT___c___
              smt__CONSTANT___S___) smt__TLA______Tt___Idv))
        (=
          (smt__ACTION___Return___ smt__CONSTANT___c___ smt__CONSTANT___S___)
          smt__TLA______Tt___Idv)))))

;; Goal
(assert
  (!
    (not
      (exists ((smt__CONSTANT___c___ Idv) (smt__CONSTANT___S___ Idv))
        (and
          (smt__TLA______Mem smt__CONSTANT___c___ smt__CONSTANT___Client___)
          (smt__TLA______Mem smt__CONSTANT___S___
            (smt__TLA______Subset smt__CONSTANT___Resource___))
          (or
            (=
              (smt__ACTION___Request___ smt__CONSTANT___c___
                smt__CONSTANT___S___) smt__TLA______Tt___Idv)
            (=
              (smt__ACTION___Allocate___ smt__CONSTANT___c___
                smt__CONSTANT___S___) smt__TLA______Tt___Idv)
            (=
              (smt__ACTION___Return___ smt__CONSTANT___c___
                smt__CONSTANT___S___) smt__TLA______Tt___Idv)))))
    :named |Goal|))

(check-sat)
(get-proof)
