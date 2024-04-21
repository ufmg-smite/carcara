;; Proof obligation:
;;	ASSUME NEW CONSTANT CONSTANT_Client_,
;;	       NEW CONSTANT CONSTANT_Resource_,
;;	       NEW VARIABLE VARIABLE_unsat_,
;;	       NEW VARIABLE VARIABLE_alloc_,
;;	       NEW CONSTANT CONSTANT_clt_ \in CONSTANT_Client_,
;;	       NEW CONSTANT CONSTANT_S_ \in SUBSET CONSTANT_Resource_,
;;	       ASSUME STATE_TypeInvariant_ ,
;;	              \A CONSTANT_c1_, CONSTANT_c2_ \in CONSTANT_Client_ :
;;	                 \A CONSTANT_r_ \in CONSTANT_Resource_ :
;;	                    CONSTANT_r_
;;	                    \in VARIABLE_alloc_[CONSTANT_c1_]
;;	                        \cap VARIABLE_alloc_[CONSTANT_c2_]
;;	                    => CONSTANT_c1_ = CONSTANT_c2_ ,
;;	              ACTION_Return_(CONSTANT_clt_, CONSTANT_S_) ,
;;	              NEW CONSTANT CONSTANT_c1_ \in CONSTANT_Client_,
;;	              NEW CONSTANT CONSTANT_c2_ \in CONSTANT_Client_,
;;	              NEW CONSTANT CONSTANT_r_ \in CONSTANT_Resource_,
;;	              CONSTANT_r_
;;	              \in ?VARIABLE_alloc_#prime[CONSTANT_c1_]
;;	                  \cap ?VARIABLE_alloc_#prime[CONSTANT_c2_] 
;;	       PROVE  CONSTANT_c1_ = CONSTANT_c2_ 
;;	PROVE  STATE_TypeInvariant_
;;	       /\ (\A CONSTANT_c1_, CONSTANT_c2_ \in CONSTANT_Client_ :
;;	              \A CONSTANT_r_ \in CONSTANT_Resource_ :
;;	                 CONSTANT_r_
;;	                 \in VARIABLE_alloc_[CONSTANT_c1_]
;;	                     \cap VARIABLE_alloc_[CONSTANT_c2_]
;;	                 => CONSTANT_c1_ = CONSTANT_c2_)
;;	       /\ ACTION_Return_(CONSTANT_clt_, CONSTANT_S_)
;;	       => (\A CONSTANT_c1_, CONSTANT_c2_ \in CONSTANT_Client_ :
;;	              \A CONSTANT_r_ \in CONSTANT_Resource_ :
;;	                 CONSTANT_r_
;;	                 \in ?VARIABLE_alloc_#prime[CONSTANT_c1_]
;;	                     \cap ?VARIABLE_alloc_#prime[CONSTANT_c2_]
;;	                 => CONSTANT_c1_ = CONSTANT_c2_)
;; TLA+ Proof Manager 1.5.0
;; Proof obligation #26
;; Generated from file "/home/rosalied/Documents/work/thesis-eval/tla_specs/tlaps_examples/Allocator.tla", line 194, characters 3-4

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun smt__TLA______Cap (Idv Idv) Idv)

(declare-fun smt__TLA______FunApp (Idv Idv) Idv)

(declare-fun smt__TLA______FunDom (Idv) Idv)

; omitted declaration of 'TLA__FunFcn' (second-order)

(declare-fun smt__TLA______FunIsafcn (Idv) Bool)

(declare-fun smt__TLA______Mem (Idv Idv) Bool)

(declare-fun smt__TLA______SetEnum___0 () Idv)

(declare-fun smt__TLA______SetExtTrigger (Idv Idv) Bool)

(declare-fun smt__TLA______Subset (Idv) Idv)

(declare-fun smt__TLA______SubsetEq (Idv Idv) Bool)

(declare-fun smt__TLA______TrigEq___Idv (Idv Idv) Bool)

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

; omitted fact (second-order)

; omitted fact (second-order)

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

(assert
  (=> (= smt__STATE___TypeInvariant___ smt__TLA______Tt___Idv)
    (=>
      (forall ((smt__CONSTANT___c1___ Idv) (smt__CONSTANT___c2___ Idv))
        (=>
          (and
            (smt__TLA______Mem smt__CONSTANT___c1___
              smt__CONSTANT___Client___)
            (smt__TLA______Mem smt__CONSTANT___c2___
              smt__CONSTANT___Client___))
          (forall ((smt__CONSTANT___r___ Idv))
            (=>
              (smt__TLA______Mem smt__CONSTANT___r___
                smt__CONSTANT___Resource___)
              (=>
                (smt__TLA______Mem smt__CONSTANT___r___
                  (smt__TLA______Cap
                    (smt__TLA______FunApp smt__VARIABLE___alloc___
                      smt__CONSTANT___c1___)
                    (smt__TLA______FunApp smt__VARIABLE___alloc___
                      smt__CONSTANT___c2___)))
                (smt__TLA______TrigEq___Idv smt__CONSTANT___c1___
                  smt__CONSTANT___c2___))))))
      (=>
        (=
          (smt__ACTION___Return___ smt__CONSTANT___clt___
            smt__CONSTANT___S___) smt__TLA______Tt___Idv)
        (forall ((smt__CONSTANT___c1___ Idv))
          (=>
            (smt__TLA______Mem smt__CONSTANT___c1___
              smt__CONSTANT___Client___)
            (forall ((smt__CONSTANT___c2___ Idv))
              (=>
                (smt__TLA______Mem smt__CONSTANT___c2___
                  smt__CONSTANT___Client___)
                (forall ((smt__CONSTANT___r___ Idv))
                  (=>
                    (smt__TLA______Mem smt__CONSTANT___r___
                      smt__CONSTANT___Resource___)
                    (=>
                      (smt__TLA______Mem smt__CONSTANT___r___
                        (smt__TLA______Cap
                          (smt__TLA______FunApp
                            smt__VARIABLE___alloc______prime
                            smt__CONSTANT___c1___)
                          (smt__TLA______FunApp
                            smt__VARIABLE___alloc______prime
                            smt__CONSTANT___c2___)))
                      (smt__TLA______TrigEq___Idv smt__CONSTANT___c1___
                        smt__CONSTANT___c2___))))))))))))

;; Goal
(assert
  (!
    (not
      (=>
        (and
          (and (= smt__STATE___TypeInvariant___ smt__TLA______Tt___Idv)
            (forall ((smt__CONSTANT___c1___ Idv) (smt__CONSTANT___c2___ Idv))
              (=>
                (and
                  (smt__TLA______Mem smt__CONSTANT___c1___
                    smt__CONSTANT___Client___)
                  (smt__TLA______Mem smt__CONSTANT___c2___
                    smt__CONSTANT___Client___))
                (forall ((smt__CONSTANT___r___ Idv))
                  (=>
                    (smt__TLA______Mem smt__CONSTANT___r___
                      smt__CONSTANT___Resource___)
                    (=>
                      (smt__TLA______Mem smt__CONSTANT___r___
                        (smt__TLA______Cap
                          (smt__TLA______FunApp smt__VARIABLE___alloc___
                            smt__CONSTANT___c1___)
                          (smt__TLA______FunApp smt__VARIABLE___alloc___
                            smt__CONSTANT___c2___)))
                      (smt__TLA______TrigEq___Idv smt__CONSTANT___c1___
                        smt__CONSTANT___c2___)))))))
          (=
            (smt__ACTION___Return___ smt__CONSTANT___clt___
              smt__CONSTANT___S___) smt__TLA______Tt___Idv))
        (forall ((smt__CONSTANT___c1___ Idv) (smt__CONSTANT___c2___ Idv))
          (=>
            (and
              (smt__TLA______Mem smt__CONSTANT___c1___
                smt__CONSTANT___Client___)
              (smt__TLA______Mem smt__CONSTANT___c2___
                smt__CONSTANT___Client___))
            (forall ((smt__CONSTANT___r___ Idv))
              (=>
                (smt__TLA______Mem smt__CONSTANT___r___
                  smt__CONSTANT___Resource___)
                (=>
                  (smt__TLA______Mem smt__CONSTANT___r___
                    (smt__TLA______Cap
                      (smt__TLA______FunApp smt__VARIABLE___alloc______prime
                        smt__CONSTANT___c1___)
                      (smt__TLA______FunApp smt__VARIABLE___alloc______prime
                        smt__CONSTANT___c2___)))
                  (smt__TLA______TrigEq___Idv smt__CONSTANT___c1___
                    smt__CONSTANT___c2___)))))))) :named |Goal|))

(check-sat)
(get-proof)
