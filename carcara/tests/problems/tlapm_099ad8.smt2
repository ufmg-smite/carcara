;; Proof obligation:
;;	ASSUME NEW CONSTANT CONSTANT_Client_,
;;	       NEW CONSTANT CONSTANT_Resource_,
;;	       NEW VARIABLE VARIABLE_unsat_,
;;	       NEW VARIABLE VARIABLE_alloc_,
;;	       NEW CONSTANT CONSTANT_clt_ \in CONSTANT_Client_,
;;	       NEW CONSTANT CONSTANT_S_ \in SUBSET CONSTANT_Resource_,
;;	       NEW CONSTANT CONSTANT_c1_ \in CONSTANT_Client_,
;;	       NEW CONSTANT CONSTANT_c2_ \in CONSTANT_Client_,
;;	       NEW CONSTANT CONSTANT_r_ \in CONSTANT_Resource_,
;;	       /\ /\ VARIABLE_unsat_
;;	             \in [CONSTANT_Client_ -> SUBSET CONSTANT_Resource_]
;;	          /\ VARIABLE_alloc_
;;	             \in [CONSTANT_Client_ -> SUBSET CONSTANT_Resource_]
;;	       /\ STATE_Mutex_
;;	       /\ CONSTANT_S_ # {}
;;	          /\ CONSTANT_S_ \subseteq VARIABLE_alloc_[CONSTANT_clt_]
;;	       /\ CONSTANT_r_
;;	          \in ?VARIABLE_alloc_#prime[CONSTANT_c1_]
;;	              \cap ?VARIABLE_alloc_#prime[CONSTANT_c2_] ,
;;	       ?VARIABLE_alloc_#prime
;;	       = [VARIABLE_alloc_ EXCEPT
;;	            ![CONSTANT_clt_] = VARIABLE_alloc_[CONSTANT_clt_] \ CONSTANT_S_] ,
;;	       ?VARIABLE_unsat_#prime = VARIABLE_unsat_ 
;;	PROVE  ?VARIABLE_alloc_#prime[CONSTANT_c1_]
;;	       \subseteq VARIABLE_alloc_[CONSTANT_c1_]
;; TLA+ Proof Manager 1.5.0
;; Proof obligation #27
;; Generated from file "/home/rosalied/Documents/work/thesis-eval/tla_specs/tlaps_examples/Allocator.tla", line 196, characters 3-4

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun smt__TLA______Cap (Idv Idv) Idv)

(declare-fun smt__TLA______FunApp (Idv Idv) Idv)

(declare-fun smt__TLA______FunDom (Idv) Idv)

(declare-fun smt__TLA______FunExcept (Idv Idv Idv) Idv)

; omitted declaration of 'TLA__FunFcn' (second-order)

(declare-fun smt__TLA______FunIsafcn (Idv) Bool)

(declare-fun smt__TLA______FunSet (Idv Idv) Idv)

(declare-fun smt__TLA______Mem (Idv Idv) Bool)

(declare-fun smt__TLA______SetEnum___0 () Idv)

(declare-fun smt__TLA______SetExtTrigger (Idv Idv) Bool)

(declare-fun smt__TLA______SetMinus (Idv Idv) Idv)

(declare-fun smt__TLA______Subset (Idv) Idv)

(declare-fun smt__TLA______SubsetEq (Idv Idv) Bool)

(declare-fun smt__TLA______TrigEq___Idv (Idv Idv) Bool)

(declare-fun smt__TLA______TrigEq___Setdollarsign___Idvdollarsign___ (Idv
  Idv) Bool)

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

;; Axiom: CapDef
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv) (smt__x Idv))
      (!
        (= (smt__TLA______Mem smt__x (smt__TLA______Cap smt__a smt__b))
          (and (smt__TLA______Mem smt__x smt__a)
            (smt__TLA______Mem smt__x smt__b)))
        :pattern ((smt__TLA______Mem smt__x (smt__TLA______Cap smt__a smt__b)))
        :pattern ((smt__TLA______Mem smt__x smt__a)
                   (smt__TLA______Cap smt__a smt__b))
        :pattern ((smt__TLA______Mem smt__x smt__b)
                   (smt__TLA______Cap smt__a smt__b)))) :named |CapDef|))

;; Axiom: SetMinusDef
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv) (smt__x Idv))
      (!
        (= (smt__TLA______Mem smt__x (smt__TLA______SetMinus smt__a smt__b))
          (and (smt__TLA______Mem smt__x smt__a)
            (not (smt__TLA______Mem smt__x smt__b))))
        :pattern ((smt__TLA______Mem smt__x
                    (smt__TLA______SetMinus smt__a smt__b)))
        :pattern ((smt__TLA______Mem smt__x smt__a)
                   (smt__TLA______SetMinus smt__a smt__b))
        :pattern ((smt__TLA______Mem smt__x smt__b)
                   (smt__TLA______SetMinus smt__a smt__b))))
    :named |SetMinusDef|))

;; Axiom: FunExt
(assert
  (!
    (forall ((smt__f Idv) (smt__g Idv))
      (!
        (=>
          (and (smt__TLA______FunIsafcn smt__f)
            (smt__TLA______FunIsafcn smt__g)
            (= (smt__TLA______FunDom smt__f) (smt__TLA______FunDom smt__g))
            (forall ((smt__x Idv))
              (=> (smt__TLA______Mem smt__x (smt__TLA______FunDom smt__f))
                (= (smt__TLA______FunApp smt__f smt__x)
                  (smt__TLA______FunApp smt__g smt__x))))) (= smt__f smt__g))
        :pattern ((smt__TLA______FunIsafcn smt__f)
                   (smt__TLA______FunIsafcn smt__g)))) :named |FunExt|))

; omitted fact (second-order)

;; Axiom: FunSetIntro
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv) (smt__f Idv))
      (!
        (=>
          (and (smt__TLA______FunIsafcn smt__f)
            (= (smt__TLA______FunDom smt__f) smt__a)
            (forall ((smt__x Idv))
              (=> (smt__TLA______Mem smt__x smt__a)
                (smt__TLA______Mem (smt__TLA______FunApp smt__f smt__x)
                  smt__b))))
          (smt__TLA______Mem smt__f (smt__TLA______FunSet smt__a smt__b)))
        :pattern ((smt__TLA______Mem smt__f
                    (smt__TLA______FunSet smt__a smt__b)))))
    :named |FunSetIntro|))

;; Axiom: FunSetElim1
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv) (smt__f Idv))
      (!
        (=> (smt__TLA______Mem smt__f (smt__TLA______FunSet smt__a smt__b))
          (and (smt__TLA______FunIsafcn smt__f)
            (= (smt__TLA______FunDom smt__f) smt__a)))
        :pattern ((smt__TLA______Mem smt__f
                    (smt__TLA______FunSet smt__a smt__b)))))
    :named |FunSetElim1|))

;; Axiom: FunSetElim2
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv) (smt__f Idv) (smt__x Idv))
      (!
        (=>
          (and
            (smt__TLA______Mem smt__f (smt__TLA______FunSet smt__a smt__b))
            (smt__TLA______Mem smt__x smt__a))
          (smt__TLA______Mem (smt__TLA______FunApp smt__f smt__x) smt__b))
        :pattern ((smt__TLA______Mem smt__f
                    (smt__TLA______FunSet smt__a smt__b))
                   (smt__TLA______Mem smt__x smt__a))
        :pattern ((smt__TLA______Mem smt__f
                    (smt__TLA______FunSet smt__a smt__b))
                   (smt__TLA______FunApp smt__f smt__x))))
    :named |FunSetElim2|))

; omitted fact (second-order)

; omitted fact (second-order)

; omitted fact (second-order)

;; Axiom: FunExceptIsafcn
(assert
  (!
    (forall ((smt__f Idv) (smt__x Idv) (smt__y Idv))
      (!
        (smt__TLA______FunIsafcn
          (smt__TLA______FunExcept smt__f smt__x smt__y))
        :pattern ((smt__TLA______FunExcept smt__f smt__x smt__y))))
    :named |FunExceptIsafcn|))

;; Axiom: FunExceptDomDef
(assert
  (!
    (forall ((smt__f Idv) (smt__x Idv) (smt__y Idv))
      (!
        (=
          (smt__TLA______FunDom
            (smt__TLA______FunExcept smt__f smt__x smt__y))
          (smt__TLA______FunDom smt__f))
        :pattern ((smt__TLA______FunExcept smt__f smt__x smt__y))))
    :named |FunExceptDomDef|))

;; Axiom: FunExceptAppDef1
(assert
  (!
    (forall ((smt__f Idv) (smt__x Idv) (smt__y Idv))
      (!
        (=> (smt__TLA______Mem smt__x (smt__TLA______FunDom smt__f))
          (=
            (smt__TLA______FunApp
              (smt__TLA______FunExcept smt__f smt__x smt__y) smt__x) 
            smt__y))
        :pattern ((smt__TLA______FunExcept smt__f smt__x smt__y))))
    :named |FunExceptAppDef1|))

;; Axiom: FunExceptAppDef2
(assert
  (!
    (forall ((smt__f Idv) (smt__x Idv) (smt__y Idv) (smt__z Idv))
      (!
        (=> (smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f))
          (and
            (=> (= smt__z smt__x)
              (=
                (smt__TLA______FunApp
                  (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z)
                smt__y))
            (=> (distinct smt__z smt__x)
              (=
                (smt__TLA______FunApp
                  (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z)
                (smt__TLA______FunApp smt__f smt__z)))))
        :pattern ((smt__TLA______FunApp
                    (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))
        :pattern ((smt__TLA______FunExcept smt__f smt__x smt__y)
                   (smt__TLA______FunApp smt__f smt__z))))
    :named |FunExceptAppDef2|))

;; Axiom: DisjointTrigger
(assert
  (!
    (forall ((smt__x Idv) (smt__y Idv))
      (!
        (smt__TLA______SetExtTrigger (smt__TLA______Cap smt__x smt__y)
          smt__TLA______SetEnum___0)
        :pattern ((smt__TLA______Cap smt__x smt__y))))
    :named |DisjointTrigger|))

;; Axiom: EnumDefElim 0
(assert
  (!
    (forall ((smt__x Idv))
      (! (not (smt__TLA______Mem smt__x smt__TLA______SetEnum___0))
        :pattern ((smt__TLA______Mem smt__x smt__TLA______SetEnum___0))))
    :named |EnumDefElim 0|))

;; Axiom: ExtTrigEqDef Idv
(assert
  (!
    (forall ((smt__x Idv) (smt__y Idv))
      (! (= (smt__TLA______TrigEq___Idv smt__x smt__y) (= smt__x smt__y))
        :pattern ((smt__TLA______TrigEq___Idv smt__x smt__y))))
    :named |ExtTrigEqDef Idv|))

;; Axiom: ExtTrigEqDef Set$Idv$
(assert
  (!
    (forall ((smt__x Idv) (smt__y Idv))
      (!
        (=
          (smt__TLA______TrigEq___Setdollarsign___Idvdollarsign___ smt__x
            smt__y) (= smt__x smt__y))
        :pattern ((smt__TLA______TrigEq___Setdollarsign___Idvdollarsign___
                    smt__x smt__y)))) :named |ExtTrigEqDef Set$Idv$|))

;; Axiom: ExtTrigEqTrigger Idv
(assert
  (!
    (forall ((smt__x Idv) (smt__y Idv))
      (! (smt__TLA______SetExtTrigger smt__x smt__y)
        :pattern ((smt__TLA______TrigEq___Setdollarsign___Idvdollarsign___
                    smt__x smt__y)))) :named |ExtTrigEqTrigger Idv|))

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

(declare-fun smt__STATE___available___ () Idv)

(declare-fun smt__STATE___Init___ () Idv)

(declare-fun smt__ACTION___Request___ (Idv Idv) Idv)

(declare-fun smt__ACTION___Allocate___ (Idv Idv) Idv)

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

; hidden fact

; hidden fact

(declare-fun smt__CONSTANT___clt___ () Idv)

(assert (smt__TLA______Mem smt__CONSTANT___clt___ smt__CONSTANT___Client___))

(declare-fun smt__CONSTANT___S___ () Idv)

(assert
  (smt__TLA______Mem smt__CONSTANT___S___
    (smt__TLA______Subset smt__CONSTANT___Resource___)))

; hidden fact

; hidden fact

; hidden fact

(declare-fun smt__CONSTANT___c1___ () Idv)

(assert (smt__TLA______Mem smt__CONSTANT___c1___ smt__CONSTANT___Client___))

(declare-fun smt__CONSTANT___c2___ () Idv)

(assert (smt__TLA______Mem smt__CONSTANT___c2___ smt__CONSTANT___Client___))

(declare-fun smt__CONSTANT___r___ () Idv)

(assert (smt__TLA______Mem smt__CONSTANT___r___ smt__CONSTANT___Resource___))

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

(assert
  (and
    (and
      (smt__TLA______Mem smt__VARIABLE___unsat___
        (smt__TLA______FunSet smt__CONSTANT___Client___
          (smt__TLA______Subset smt__CONSTANT___Resource___)))
      (smt__TLA______Mem smt__VARIABLE___alloc___
        (smt__TLA______FunSet smt__CONSTANT___Client___
          (smt__TLA______Subset smt__CONSTANT___Resource___))))
    (= smt__STATE___Mutex___ smt__TLA______Tt___Idv)
    (and
      (not
        (smt__TLA______TrigEq___Setdollarsign___Idvdollarsign___
          smt__CONSTANT___S___ smt__TLA______SetEnum___0))
      (smt__TLA______SubsetEq smt__CONSTANT___S___
        (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___)))
    (smt__TLA______Mem smt__CONSTANT___r___
      (smt__TLA______Cap
        (smt__TLA______FunApp smt__VARIABLE___alloc______prime
          smt__CONSTANT___c1___)
        (smt__TLA______FunApp smt__VARIABLE___alloc______prime
          smt__CONSTANT___c2___)))))

(assert
  (smt__TLA______TrigEq___Idv smt__VARIABLE___alloc______prime
    (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___
      (smt__TLA______SetMinus
        (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___)
        smt__CONSTANT___S___))))

(assert
  (smt__TLA______TrigEq___Idv smt__VARIABLE___unsat______prime
    smt__VARIABLE___unsat___))

;; Goal
(assert
  (!
    (not
      (smt__TLA______SubsetEq
        (smt__TLA______FunApp smt__VARIABLE___alloc______prime
          smt__CONSTANT___c1___)
        (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))
    :named |Goal|))

(check-sat)
(get-proof)
