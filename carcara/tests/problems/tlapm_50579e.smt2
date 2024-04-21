;; Proof obligation:
;;	ASSUME NEW CONSTANT CONSTANT_Client_,
;;	       NEW CONSTANT CONSTANT_Resource_,
;;	       NEW VARIABLE VARIABLE_unsat_,
;;	       NEW VARIABLE VARIABLE_alloc_
;;	PROVE  (/\ VARIABLE_unsat_ = [CONSTANT_c_ \in CONSTANT_Client_ |-> {}]
;;	        /\ VARIABLE_alloc_ = [CONSTANT_c_ \in CONSTANT_Client_ |-> {}])
;;	       => (\A CONSTANT_c1_, CONSTANT_c2_ \in CONSTANT_Client_ :
;;	              \A CONSTANT_r_ \in CONSTANT_Resource_ :
;;	                 CONSTANT_r_
;;	                 \in VARIABLE_alloc_[CONSTANT_c1_]
;;	                     \cap VARIABLE_alloc_[CONSTANT_c2_]
;;	                 => CONSTANT_c1_ = CONSTANT_c2_)
;; TLA+ Proof Manager 1.5.0
;; Proof obligation #20
;; Generated from file "/home/rosalied/Documents/work/thesis-eval/tla_specs/tlaps_examples/Allocator.tla", line 173, characters 1-2

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

(declare-fun smt__TLA______TrigEq___Idv (Idv Idv) Bool)

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

(declare-fun smt__TLA______FunFcn___flatnd___1 (Idv) Idv)

;; Axiom: FunConstrIsafcn TLA__FunFcn_flatnd_1
(assert
  (!
    (forall ((smt__a Idv))
      (! (smt__TLA______FunIsafcn (smt__TLA______FunFcn___flatnd___1 smt__a))
        :pattern ((smt__TLA______FunFcn___flatnd___1 smt__a))))
    :named |FunConstrIsafcn TLA__FunFcn_flatnd_1|))

;; Axiom: FunDomDef TLA__FunFcn_flatnd_1
(assert
  (!
    (forall ((smt__a Idv))
      (!
        (= (smt__TLA______FunDom (smt__TLA______FunFcn___flatnd___1 smt__a))
          smt__a) :pattern ((smt__TLA______FunFcn___flatnd___1 smt__a))))
    :named |FunDomDef TLA__FunFcn_flatnd_1|))

;; Axiom: FunAppDef TLA__FunFcn_flatnd_1
(assert
  (!
    (forall ((smt__a Idv) (smt__x Idv))
      (!
        (=> (smt__TLA______Mem smt__x smt__a)
          (=
            (smt__TLA______FunApp (smt__TLA______FunFcn___flatnd___1 smt__a)
              smt__x) smt__TLA______SetEnum___0))
        :pattern ((smt__TLA______FunApp
                    (smt__TLA______FunFcn___flatnd___1 smt__a) smt__x))
        :pattern ((smt__TLA______Mem smt__x smt__a)
                   (smt__TLA______FunFcn___flatnd___1 smt__a))))
    :named |FunAppDef TLA__FunFcn_flatnd_1|))

;; Goal
(assert
  (!
    (not
      (=>
        (and
          (smt__TLA______TrigEq___Idv smt__VARIABLE___unsat___
            (smt__TLA______FunFcn___flatnd___1 smt__CONSTANT___Client___))
          (smt__TLA______TrigEq___Idv smt__VARIABLE___alloc___
            (smt__TLA______FunFcn___flatnd___1 smt__CONSTANT___Client___)))
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
                    smt__CONSTANT___c2___)))))))) :named |Goal|))

(check-sat)
(get-proof)
