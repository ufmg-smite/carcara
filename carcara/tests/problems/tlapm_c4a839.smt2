(set-option :produce-proofs true)
(set-logic UFLIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun smt__TLA__FunApp (Idv Idv) Idv)

(declare-fun smt__TLA__FunDom (Idv) Idv)

; omitted declaration of 'TLA__FunFcn' (second-order)

(declare-fun smt__TLA__FunIsafcn (Idv) Bool)

(declare-fun smt__TLA__FunSet (Idv Idv) Idv)

(declare-fun smt__TLA__Mem (Idv Idv) Bool)

(declare-fun smt__TLA__SetEnum_0 () Idv)

(declare-fun smt__TLA__SetExtTrigger (Idv Idv) Bool)

; omitted declaration of 'TLA__SetSt' (second-order)

(declare-fun smt__TLA__Subset (Idv) Idv)

(declare-fun smt__TLA__SubsetEq (Idv Idv) Bool)

;; Axiom: SetExt
(assert
  (!
    (forall ((smt__x Idv) (smt__y Idv))
      (!
        (=>
          (forall ((smt__z Idv))
            (= (smt__TLA__Mem smt__z smt__x) (smt__TLA__Mem smt__z smt__y)))
          (= smt__x smt__y))
        :pattern ((smt__TLA__SetExtTrigger smt__x smt__y)))) :named |SetExt|))

;; Axiom: SubsetEqIntro
(assert
  (!
    (forall ((smt__x Idv) (smt__y Idv))
      (!
        (=>
          (forall ((smt__z Idv))
            (=> (smt__TLA__Mem smt__z smt__x) (smt__TLA__Mem smt__z smt__y)))
          (smt__TLA__SubsetEq smt__x smt__y))
        :pattern ((smt__TLA__SubsetEq smt__x smt__y))))
    :named |SubsetEqIntro|))

;; Axiom: SubsetEqElim
(assert
  (!
    (forall ((smt__x Idv) (smt__y Idv) (smt__z Idv))
      (!
        (=>
          (and (smt__TLA__SubsetEq smt__x smt__y)
            (smt__TLA__Mem smt__z smt__x)) (smt__TLA__Mem smt__z smt__y))
        :pattern ((smt__TLA__SubsetEq smt__x smt__y)
                   (smt__TLA__Mem smt__z smt__x)))) :named |SubsetEqElim|))

;; Axiom: SubsetDefAlt
(assert
  (!
    (forall ((smt__a Idv) (smt__x Idv))
      (!
        (= (smt__TLA__Mem smt__x (smt__TLA__Subset smt__a))
          (smt__TLA__SubsetEq smt__x smt__a))
        :pattern ((smt__TLA__Mem smt__x (smt__TLA__Subset smt__a)))
        :pattern ((smt__TLA__SubsetEq smt__x smt__a)
                   (smt__TLA__Subset smt__a)))) :named |SubsetDefAlt|))

; omitted fact (second-order)

;; Axiom: FunExt
(assert
  (!
    (forall ((smt__f Idv) (smt__g Idv))
      (!
        (=>
          (and (smt__TLA__FunIsafcn smt__f) (smt__TLA__FunIsafcn smt__g)
            (= (smt__TLA__FunDom smt__f) (smt__TLA__FunDom smt__g))
            (forall ((smt__x Idv))
              (=> (smt__TLA__Mem smt__x (smt__TLA__FunDom smt__f))
                (= (smt__TLA__FunApp smt__f smt__x)
                  (smt__TLA__FunApp smt__g smt__x))))) (= smt__f smt__g))
        :pattern ((smt__TLA__FunIsafcn smt__f) (smt__TLA__FunIsafcn smt__g))))
    :named |FunExt|))

; omitted fact (second-order)

;; Axiom: FunSetIntro
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv) (smt__f Idv))
      (!
        (=>
          (and (smt__TLA__FunIsafcn smt__f)
            (= (smt__TLA__FunDom smt__f) smt__a)
            (forall ((smt__x Idv))
              (=> (smt__TLA__Mem smt__x smt__a)
                (smt__TLA__Mem (smt__TLA__FunApp smt__f smt__x) smt__b))))
          (smt__TLA__Mem smt__f (smt__TLA__FunSet smt__a smt__b)))
        :pattern ((smt__TLA__Mem smt__f (smt__TLA__FunSet smt__a smt__b)))))
    :named |FunSetIntro|))

;; Axiom: FunSetElim1
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv) (smt__f Idv))
      (!
        (=> (smt__TLA__Mem smt__f (smt__TLA__FunSet smt__a smt__b))
          (and (smt__TLA__FunIsafcn smt__f)
            (= (smt__TLA__FunDom smt__f) smt__a)))
        :pattern ((smt__TLA__Mem smt__f (smt__TLA__FunSet smt__a smt__b)))))
    :named |FunSetElim1|))

;; Axiom: FunSetElim2
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv) (smt__f Idv) (smt__x Idv))
      (!
        (=>
          (and (smt__TLA__Mem smt__f (smt__TLA__FunSet smt__a smt__b))
            (smt__TLA__Mem smt__x smt__a))
          (smt__TLA__Mem (smt__TLA__FunApp smt__f smt__x) smt__b))
        :pattern ((smt__TLA__Mem smt__f (smt__TLA__FunSet smt__a smt__b))
                   (smt__TLA__Mem smt__x smt__a))
        :pattern ((smt__TLA__Mem smt__f (smt__TLA__FunSet smt__a smt__b))
                   (smt__TLA__FunApp smt__f smt__x)))) :named |FunSetElim2|))

; omitted fact (second-order)

; omitted fact (second-order)

; omitted fact (second-order)

;; Axiom: EnumDefElim 0
(assert
  (!
    (forall ((smt__x Idv))
      (! (not (smt__TLA__Mem smt__x smt__TLA__SetEnum_0))
        :pattern ((smt__TLA__Mem smt__x smt__TLA__SetEnum_0))))
    :named |EnumDefElim 0|))

(declare-fun smt__CONSTANT_S_ () Idv)

; hidden fact

; hidden fact

(declare-fun smt__CONSTANT_f_ () Idv)

(assert
  (smt__TLA__Mem smt__CONSTANT_f_
    (smt__TLA__FunSet smt__CONSTANT_S_ (smt__TLA__Subset smt__CONSTANT_S_))))

; hidden fact

; hidden fact

; hidden fact

; hidden fact

(declare-fun smt__CONSTANT_x_ () Idv)

(assert (smt__TLA__Mem smt__CONSTANT_x_ smt__CONSTANT_S_))

; hidden fact

; hidden fact

(declare-fun smt__TLA__SetSt_flatnd_1 (Idv) Idv)

;; Axiom: SetStDef TLA__SetSt_flatnd_1 ===== T
(assert
  (!
    (forall ((smt__a Idv) (smt__x Idv))
      (!
        (= (smt__TLA__Mem smt__x (smt__TLA__SetSt_flatnd_1 smt__a))
          (and (smt__TLA__Mem smt__x smt__a)
            (not
              (smt__TLA__Mem smt__x
                (smt__TLA__FunApp smt__CONSTANT_f_ smt__x)))))
        :pattern ((smt__TLA__Mem smt__x (smt__TLA__SetSt_flatnd_1 smt__a)))
        :pattern ((smt__TLA__Mem smt__x smt__a)
                   (smt__TLA__SetSt_flatnd_1 smt__a))))
    :named |SetStDef TLA__SetSt_flatnd_1|))

;; Goal
(assert
  (!
    (not
      (or
        (smt__TLA__Mem smt__CONSTANT_x_
          (smt__TLA__SetSt_flatnd_1 smt__CONSTANT_S_))
        (not
          (smt__TLA__Mem smt__CONSTANT_x_
            (smt__TLA__SetSt_flatnd_1 smt__CONSTANT_S_))))) :named |Goal|))

(check-sat)
(get-proof)
(exit)
