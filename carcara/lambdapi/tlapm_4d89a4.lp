require open Stdlib.Prop;

require open Stdlib.Set;

require open Stdlib.Eq;

require open Stdlib.Nat;

require open lambdapi.Classic;

require open lambdapi.Alethe;

require open lambdapi.Simplify;

require open lambdapi.Rare;

symbol Idv : Set;

symbol smt__TLA______Cap : τ (Idv ⤳ Idv ⤳ Idv) ≔ (𝑰 0);

symbol smt__TLA______Cup : τ (Idv ⤳ Idv ⤳ Idv) ≔ (𝑰 1);

symbol smt__TLA______FunApp : τ (Idv ⤳ Idv ⤳ Idv) ≔ (𝑰 2);

symbol smt__TLA______FunDom : τ (Idv ⤳ Idv) ≔ (𝑰 3);

symbol smt__TLA______FunExcept : τ (Idv ⤳ Idv ⤳ Idv ⤳ Idv) ≔ (𝑰 4);

symbol smt__TLA______FunIsafcn : τ (Idv ⤳ o) ≔ (𝑰 5);

symbol smt__TLA______FunSet : τ (Idv ⤳ Idv ⤳ Idv) ≔ (𝑰 6);

symbol smt__TLA______Mem : τ (Idv ⤳ Idv ⤳ o) ≔ (𝑰 7);

symbol smt__TLA______SetEnum___0 : τ (Idv) ≔ (𝑰 8);

symbol smt__TLA______SetExtTrigger : τ (Idv ⤳ Idv ⤳ o) ≔ (𝑰 9);

symbol smt__TLA______SetMinus : τ (Idv ⤳ Idv ⤳ Idv) ≔ (𝑰 10);

symbol smt__TLA______Subset : τ (Idv ⤳ Idv) ≔ (𝑰 11);

symbol smt__TLA______SubsetEq : τ (Idv ⤳ Idv ⤳ o) ≔ (𝑰 12);

symbol smt__TLA______TrigEq___Idv : τ (Idv ⤳ Idv ⤳ o) ≔ (𝑰 13);

symbol smt__TLA______TrigEq___Setdollarsign___Idvdollarsign___ : τ (Idv ⤳ Idv ⤳ o) ≔ (𝑰 14);

symbol smt__TLA______Tt___Idv : τ (Idv) ≔ (𝑰 15);

symbol smt__CONSTANT___Client___ : τ (Idv) ≔ (𝑰 16);

symbol smt__CONSTANT___Resource___ : τ (Idv) ≔ (𝑰 17);

symbol smt__VARIABLE___unsat___ : τ (Idv) ≔ (𝑰 18);

symbol smt__VARIABLE___unsat______prime : τ (Idv) ≔ (𝑰 19);

symbol smt__VARIABLE___alloc___ : τ (Idv) ≔ (𝑰 20);

symbol smt__VARIABLE___alloc______prime : τ (Idv) ≔ (𝑰 21);

symbol smt__STATE___available___ : τ (Idv) ≔ (𝑰 22);

symbol smt__STATE___Init___ : τ (Idv) ≔ (𝑰 23);

symbol smt__ACTION___Request___ : τ (Idv ⤳ Idv ⤳ Idv) ≔ (𝑰 24);

symbol smt__ACTION___Return___ : τ (Idv ⤳ Idv ⤳ Idv) ≔ (𝑰 25);

symbol smt__ACTION___Next___ : τ (Idv) ≔ (𝑰 26);

symbol smt__STATE___vars___ : τ (Idv) ≔ (𝑰 27);

symbol smt__TEMPORAL___SimpleAllocator___ : τ (Idv) ≔ (𝑰 28);

symbol smt__STATE___Mutex___ : τ (Idv) ≔ (𝑰 29);

symbol smt__TEMPORAL___ClientsWillReturn___ : τ (Idv) ≔ (𝑰 30);

symbol smt__TEMPORAL___ClientsWillObtain___ : τ (Idv) ≔ (𝑰 31);

symbol smt__TEMPORAL___InfOftenSatisfied___ : τ (Idv) ≔ (𝑰 32);

symbol smt__CONSTANT___clt___ : τ (Idv) ≔ (𝑰 33);

symbol smt__CONSTANT___S___ : τ (Idv) ≔ (𝑰 34);

symbol smt__CONSTANT___c1___ : τ (Idv) ≔ (𝑰 35);

symbol smt__CONSTANT___c2___ : τ (Idv) ≔ (𝑰 36);

symbol smt__CONSTANT___r___ : τ (Idv) ≔ (𝑰 37);

symbol p_1 : (smt__TLA______Subset smt__CONSTANT___Resource___);

symbol p_2 : (smt__TLA______Mem smt__CONSTANT___c1___ smt__CONSTANT___Client___);

symbol p_4 : (smt__TLA______FunSet smt__CONSTANT___Client___ (smt__TLA______Subset smt__CONSTANT___Resource___));

symbol p_5 : (smt__TLA______Mem smt__VARIABLE___alloc___ (smt__TLA______FunSet smt__CONSTANT___Client___ (smt__TLA______Subset smt__CONSTANT___Resource___)));

symbol p_6 : ((smt__TLA______Mem smt__VARIABLE___unsat___ (smt__TLA______FunSet smt__CONSTANT___Client___ (smt__TLA______Subset smt__CONSTANT___Resource___))) ∧ᶜ (smt__TLA______Mem smt__VARIABLE___alloc___ (smt__TLA______FunSet smt__CONSTANT___Client___ (smt__TLA______Subset smt__CONSTANT___Resource___))));

symbol p_3 : (smt__TLA______FunApp smt__VARIABLE___unsat___ smt__CONSTANT___clt___);

symbol p_7 : (((smt__TLA______Mem smt__VARIABLE___unsat___ (smt__TLA______FunSet smt__CONSTANT___Client___ (smt__TLA______Subset smt__CONSTANT___Resource___))) ∧ᶜ (smt__TLA______Mem smt__VARIABLE___alloc___ (smt__TLA______FunSet smt__CONSTANT___Client___ (smt__TLA______Subset smt__CONSTANT___Resource___)))) ∧ᶜ (smt__STATE___Mutex___ = smt__TLA______Tt___Idv) ∧ᶜ ((¬ ((smt__TLA______TrigEq___Setdollarsign___Idvdollarsign___ smt__CONSTANT___S___ smt__TLA______SetEnum___0))) ∧ᶜ (smt__TLA______SubsetEq smt__CONSTANT___S___ (smt__TLA______Cap smt__STATE___available___ (smt__TLA______FunApp smt__VARIABLE___unsat___ smt__CONSTANT___clt___)))));

symbol p_8 : (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___);

symbol p_9 : (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___));

symbol p_10 : (smt__TLA______TrigEq___Idv smt__VARIABLE___alloc______prime (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)));

symbol p_12 : (smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___);

symbol p_11 : (smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___c2___);

symbol p_13 : (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___)) ⇒ᶜ ((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___c2___)));

symbol p_14 : (¬ ((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___c2___)));

symbol p_16 : (smt__TLA______FunApp smt__VARIABLE___alloc______prime smt__CONSTANT___c1___);

symbol p_15 : (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___);

symbol p_17 : (smt__TLA______TrigEq___Idv (smt__TLA______FunApp smt__VARIABLE___alloc______prime smt__CONSTANT___c1___) (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___));

symbol p_18 : (¬ ((smt__TLA______TrigEq___Idv (smt__TLA______FunApp smt__VARIABLE___alloc______prime smt__CONSTANT___c1___) (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___))));

symbol p_19 : (smt__VARIABLE___alloc______prime = (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)));

symbol p_28 : (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___);

symbol p_29 : ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___));

symbol p_94 : ((smt__VARIABLE___alloc______prime = (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___))) ∧ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___)));

symbol p_92 : (¬ ((smt__VARIABLE___alloc______prime = (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)))));

symbol p_93 : (¬ (((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))));

symbol p_24 : ((smt__TLA______FunApp smt__VARIABLE___alloc______prime smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___));

symbol p_96 : ((((smt__VARIABLE___alloc______prime = (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___))) ∧ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___)))) ⇒ᶜ (((smt__TLA______FunApp smt__VARIABLE___alloc______prime smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___))));

symbol p_20 : ((smt__TLA______TrigEq___Idv smt__VARIABLE___alloc______prime (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___))) = (smt__VARIABLE___alloc______prime = (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___))));

symbol p_23 : (¬ (((smt__TLA______TrigEq___Idv smt__VARIABLE___alloc______prime (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___))) = (smt__VARIABLE___alloc______prime = (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___))))));

symbol p_22 : (¬ ((smt__TLA______TrigEq___Idv smt__VARIABLE___alloc______prime (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)))));

symbol p_21 : (¬ ((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y)))));

symbol p_30 : (smt__CONSTANT___clt___ = smt__CONSTANT___c1___);

symbol p_31 : ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___)));

symbol p_91 : (¬ (((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___)))));

symbol p_83 : ((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___clt___ = smt__CONSTANT___c1___));

symbol p_90 : (¬ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___clt___ = smt__CONSTANT___c1___))));

symbol p_32 : (¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___)));

symbol p_89 : (¬ ((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___)));

symbol p_85 : (smt__CONSTANT___c1___ = smt__CONSTANT___clt___);

symbol p_86 : ((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___));

symbol p_87 : (((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y)))) ⇒ᶜ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___))));

symbol p_84 : (((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y)))) ⇒ᶜ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___clt___ = smt__CONSTANT___c1___))));

symbol p_88 : ((((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y)))) ⇒ᶜ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___)))) = (((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y)))) ⇒ᶜ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___clt___ = smt__CONSTANT___c1___)))));

symbol p_33 : ((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___)));

symbol p_34 : (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))));

symbol p_82 : (¬ ((((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))))));

symbol p_35 : (smt__TLA______FunDom smt__VARIABLE___alloc___);

symbol p_36 : (smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___));

symbol p_37 : (¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___))));

symbol p_38 : ((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___)))));

symbol p_81 : (¬ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___)))))));

symbol p_64 : ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)) = ⊤);

symbol p_66 : (smt__CONSTANT___Client___ = (smt__TLA______FunDom smt__VARIABLE___alloc___));

symbol p_67 : ((smt__TLA______FunIsafcn smt__VARIABLE___alloc___) ∧ᶜ (smt__CONSTANT___Client___ = (smt__TLA______FunDom smt__VARIABLE___alloc___)));

symbol p_80 : (¬ (((smt__TLA______FunIsafcn smt__VARIABLE___alloc___) ∧ᶜ (smt__CONSTANT___Client___ = (smt__TLA______FunDom smt__VARIABLE___alloc___)))));

symbol p_68 : (¬ ((smt__TLA______Mem smt__VARIABLE___alloc___ (smt__TLA______FunSet smt__CONSTANT___Client___ (smt__TLA______Subset smt__CONSTANT___Resource___)))));

symbol p_69 : ((¬ ((smt__TLA______Mem smt__VARIABLE___alloc___ (smt__TLA______FunSet smt__CONSTANT___Client___ (smt__TLA______Subset smt__CONSTANT___Resource___))))) ∨ᶜ ((smt__TLA______FunIsafcn smt__VARIABLE___alloc___) ∧ᶜ (smt__CONSTANT___Client___ = (smt__TLA______FunDom smt__VARIABLE___alloc___))));

symbol p_79 : (¬ (((¬ ((smt__TLA______Mem smt__VARIABLE___alloc___ (smt__TLA______FunSet smt__CONSTANT___Client___ (smt__TLA______Subset smt__CONSTANT___Resource___))))) ∨ᶜ ((smt__TLA______FunIsafcn smt__VARIABLE___alloc___) ∧ᶜ (smt__CONSTANT___Client___ = (smt__TLA______FunDom smt__VARIABLE___alloc___))))));

symbol p_78 : (¬ ((`∀ᶜ smt__a, `∀ᶜ smt__b, `∀ᶜ smt__f, ((¬ ((smt__TLA______Mem smt__f (smt__TLA______FunSet smt__a smt__b)))) ∨ᶜ ((smt__TLA______FunIsafcn smt__f) ∧ᶜ (smt__a = (smt__TLA______FunDom smt__f)))))));

symbol p_70 : ((`∀ᶜ smt__a, `∀ᶜ smt__b, `∀ᶜ smt__f, (((smt__TLA______Mem smt__f (smt__TLA______FunSet smt__a smt__b))) ⇒ᶜ (((smt__TLA______FunIsafcn smt__f) ∧ᶜ ((smt__TLA______FunDom smt__f) = smt__a))))) = (`∀ᶜ smt__a, `∀ᶜ smt__b, `∀ᶜ smt__f, ((¬ ((smt__TLA______Mem smt__f (smt__TLA______FunSet smt__a smt__b)))) ∨ᶜ ((smt__TLA______FunIsafcn smt__f) ∧ᶜ (smt__a = (smt__TLA______FunDom smt__f))))));

symbol p_75 : (smt__TLA______Mem smt__f (smt__TLA______FunSet smt__a smt__b));

symbol p_73 : (smt__TLA______FunIsafcn smt__f);

symbol p_71 : (smt__TLA______FunDom smt__f);

symbol p_76 : ((smt__TLA______FunDom smt__f) = smt__a);

symbol p_72 : (smt__a = (smt__TLA______FunDom smt__f));

symbol p_77 : ((smt__TLA______FunIsafcn smt__f) ∧ᶜ ((smt__TLA______FunDom smt__f) = smt__a));

symbol p_74 : ((smt__TLA______FunIsafcn smt__f) ∧ᶜ (smt__a = (smt__TLA______FunDom smt__f)));

symbol p_65 : ((smt__TLA______Mem smt__CONSTANT___c1___ smt__CONSTANT___Client___) = ⊤);

symbol p_58 : ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___));

symbol p_59 : ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)));

symbol p_60 : (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___))));

symbol p_61 : ((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))));

symbol p_62 : (((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))) ⇒ᶜ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))))));

symbol p_57 : (((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))) ⇒ᶜ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___)))))));

symbol p_63 : ((((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))) ⇒ᶜ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___))))))) = (((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))) ⇒ᶜ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))))))));

symbol p_56 : (¬ ((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))));

symbol p_39 : ((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, (((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f))) ⇒ᶜ (((((smt__z = smt__x)) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = smt__y))) ∧ᶜ (((distinct 2 (cons _  smt__z (cons _  smt__x □)))) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z)))))))) = (`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z)))))));

symbol p_48 : (smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f));

symbol p_52 : (smt__z = smt__x);

symbol p_42 : (smt__x = smt__z);

symbol p_40 : (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z);

symbol p_51 : ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = smt__y);

symbol p_45 : (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z));

symbol p_53 : (((smt__z = smt__x)) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = smt__y)));

symbol p_46 : (((smt__x = smt__z)) ⇒ᶜ ((smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))));

symbol p_49 : (distinct 2 (cons _  smt__z (cons _  smt__x □)));

symbol p_55 : (¬ ((smt__z = smt__x)));

symbol p_43 : (¬ ((smt__x = smt__z)));

symbol p_41 : ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z));

symbol p_50 : (((distinct 2 (cons _  smt__z (cons _  smt__x □)))) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))));

symbol p_44 : (((¬ ((smt__x = smt__z)))) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))));

symbol p_54 : ((((smt__z = smt__x)) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = smt__y))) ∧ᶜ (((distinct 2 (cons _  smt__z (cons _  smt__x □)))) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z)))));

symbol p_47 : ((((smt__x = smt__z)) ⇒ᶜ ((smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z)))) ∧ᶜ (((¬ ((smt__x = smt__z)))) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z)))));

symbol p_95 : (¬ (((smt__VARIABLE___alloc______prime = (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___))) ∧ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___)))));

symbol p_25 : (¬ (((smt__TLA______FunApp smt__VARIABLE___alloc______prime smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___))));

symbol p_26 : ((smt__TLA______TrigEq___Idv (smt__TLA______FunApp smt__VARIABLE___alloc______prime smt__CONSTANT___c1___) (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)) = ((smt__TLA______FunApp smt__VARIABLE___alloc______prime smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)));

symbol p_27 : (¬ (((smt__TLA______TrigEq___Idv (smt__TLA______FunApp smt__VARIABLE___alloc______prime smt__CONSTANT___c1___) (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)) = ((smt__TLA______FunApp smt__VARIABLE___alloc______prime smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))));

symbol FunSetElim1 : π̇ ((`∀ᶜ smt__a, `∀ᶜ smt__b, `∀ᶜ smt__f, (((smt__TLA______Mem smt__f (smt__TLA______FunSet smt__a smt__b))) ⇒ᶜ (((smt__TLA______FunIsafcn smt__f) ∧ᶜ ((smt__TLA______FunDom smt__f) = smt__a)))))
    ⟇ ▩) ≔ 
begin
admit;
end;

symbol FunExceptAppDef2 : π̇ ((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, (((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f))) ⇒ᶜ (((((smt__z = smt__x)) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = smt__y))) ∧ᶜ (((distinct 2 (cons _  smt__z (cons _  smt__x □)))) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))))
    ⟇ ▩) ≔ 
begin
admit;
end;

symbol ExtTrigEqDefIdv : π̇ ((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y)))
    ⟇ ▩) ≔ 
begin
admit;
end;

symbol a22 : π̇ ((smt__TLA______Mem smt__CONSTANT___c1___ smt__CONSTANT___Client___) ⟇ ▩) ≔ 
begin
admit;
end;

symbol a25 : π̇ ((((smt__TLA______Mem smt__VARIABLE___unsat___ (smt__TLA______FunSet smt__CONSTANT___Client___ (smt__TLA______Subset smt__CONSTANT___Resource___))) ∧ᶜ (smt__TLA______Mem smt__VARIABLE___alloc___ (smt__TLA______FunSet smt__CONSTANT___Client___ (smt__TLA______Subset smt__CONSTANT___Resource___)))) ∧ᶜ (smt__STATE___Mutex___ = smt__TLA______Tt___Idv) ∧ᶜ ((¬ ((smt__TLA______TrigEq___Setdollarsign___Idvdollarsign___ smt__CONSTANT___S___ smt__TLA______SetEnum___0))) ∧ᶜ (smt__TLA______SubsetEq smt__CONSTANT___S___ (smt__TLA______Cap smt__STATE___available___ (smt__TLA______FunApp smt__VARIABLE___unsat___ smt__CONSTANT___clt___)))))
    ⟇ ▩) ≔ 
begin
admit;
end;

symbol a26 : π̇ ((smt__TLA______TrigEq___Idv smt__VARIABLE___alloc______prime (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)))
    ⟇ ▩) ≔ 
begin
admit;
end;

symbol a28 : π̇ ((((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___)) ⇒ᶜ ((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___c2___)))
    ⟇ ▩) ≔ 
begin
admit;
end;

symbol a29 : π̇ ((¬ ((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___c2___))) ⟇ ▩) ≔ 
begin
admit;
end;

symbol Goal : π̇ ((¬ ((smt__TLA______TrigEq___Idv (smt__TLA______FunApp smt__VARIABLE___alloc______prime smt__CONSTANT___c1___) (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___))))
    ⟇ ▩) ≔ 
begin
admit;
end;

symbol t0 : π̇ (p_94  ⟇ p_92  ⟇ p_93 ⟇ ▩) ≔ 
begin
apply and_neg;
reflexivity;
end;

symbol t2 : π̇ ((¬ ((smt__VARIABLE___alloc______prime = (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)))))
     ⟇ (¬ (((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))))
     ⟇ ((smt__TLA______FunApp smt__VARIABLE___alloc______prime smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___))
    ⟇ ▩) ≔ 
begin
have t2_a0 : π̇ ((smt__VARIABLE___alloc______prime = (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)))
        ⟇ ▩) {
    admit;
};
have t2_a1 : π̇ (((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))
        ⟇ ▩) {
    admit;
};
have t2_t0 : π̇ (p_23  ⟇ p_22  ⟇ p_19 ⟇ ▩) {
    apply equiv_pos2;
};
have t2_t1 : π̇ (p_22  ⟇ p_19  ⟇ p_23 ⟇ ▩) {
    admit;
};
have t2_t2 : π̇ (((¬ ((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y))))) ∨ᶜ ((smt__TLA______TrigEq___Idv smt__VARIABLE___alloc______prime (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___))) = (smt__VARIABLE___alloc______prime = (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)))))
        ⟇ ▩) {
    apply ∨ᶜᵢ₁;
    apply imply_to_or;
    apply ⇒ᶜᵢ;
    assume H;
    apply  (∀ᶜₑ (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) (∀ᶜₑ smt__VARIABLE___alloc______prime H));
};
have t2_t3 : π̇ (p_21  ⟇ p_20 ⟇ ▩) {
    admit;
};
have t2_t4 : π̇ (((smt__TLA______TrigEq___Idv smt__VARIABLE___alloc______prime (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___))) = (smt__VARIABLE___alloc______prime = (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___))))
        ⟇ ▩) {
    have t2_t3_ExtTrigEqDefIdv : π̇ (((smt__TLA______TrigEq___Idv smt__VARIABLE___alloc______prime (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___))) = (smt__VARIABLE___alloc______prime = (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___))))
            ⟇ ▩) {
        apply resolutionᵣ _ _ _ t2_t3 ExtTrigEqDefIdv;
    };
    refine t2_t3_ExtTrigEqDefIdv;
};
have t2_t5 : π̇ ((smt__VARIABLE___alloc______prime = (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)))
        ⟇ ▩) {
    have t2_t1_a26 : π̇ ((smt__VARIABLE___alloc______prime = (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)))
             ⟇ (¬ (((smt__TLA______TrigEq___Idv smt__VARIABLE___alloc______prime (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___))) = (smt__VARIABLE___alloc______prime = (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___))))))
            ⟇ ▩) {
        apply resolutionᵣ _ _ _ t2_t1 a26;
    };
    have t2_t1_a26_t2_t4 : π̇ ((smt__VARIABLE___alloc______prime = (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)))
            ⟇ ▩) {
        have t2_t1_a26' : (π̇ ((smt__VARIABLE___alloc______prime = (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)))
                 ⟇ (¬ (((smt__TLA______TrigEq___Idv smt__VARIABLE___alloc______prime (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___))) = (smt__VARIABLE___alloc______prime = (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___))))))
                ⟇ ▩) → π̇ ((¬ (((smt__TLA______TrigEq___Idv smt__VARIABLE___alloc______prime (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___))) = (smt__VARIABLE___alloc______prime = (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___))))))
                 ⟇ (smt__VARIABLE___alloc______prime = (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)))
                ⟇ ▩)) {
            assume H2;
            apply ⟇ₑ H2 
            {
                assume H;
                apply ⟇ᵢ₂;
                apply H;
            }
            {
                assume H1;
                apply ⟇ᵢ₁;
                apply H1;
            };
        };
        apply resolutionᵣ _ _ _ (t2_t1_a26' t2_t1_a26) t2_t4;
    };
    refine t2_t1_a26_t2_t4;
};
have t2_t6 : π̇ ((smt__CONSTANT___c1___ = smt__CONSTANT___c1___) ⟇ ▩) {
    apply ∨ᶜᵢ₁;
    reflexivity;
};
have t2_t7 : π̇ (((smt__TLA______FunApp smt__VARIABLE___alloc______prime smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))
        ⟇ ▩) {
    apply ∨ᶜᵢ₁;
    apply feq2ᶜ smt__TLA______FunApp (π̇ₗ t2_t5) (π̇ₗ t2_t6);
};
have t2_t8 : π̇ (p_91  ⟇ p_30  ⟇ p_29 ⟇ ▩) {
    apply or_pos;
    reflexivity;
};
have t2_t9 : π̇ (p_30  ⟇ p_29  ⟇ p_91 ⟇ ▩) {
    admit;
};
have t2_t10 : π̇ (p_90  ⟇ p_12  ⟇ p_32 ⟇ ▩) {
    apply equiv_pos1;
};
have t2_t11 : π̇ (p_12  ⟇ p_32  ⟇ p_90 ⟇ ▩) {
    admit;
};
have t2_t12 : π̇ (p_89  ⟇ p_11 ⟇ ▩) {
    apply implies (π̇ₗ a28);
};
have t2_t13 : π̇ (p_11  ⟇ p_89 ⟇ ▩) {
    admit;
};
have t2_t14 : π̇ ((¬ ((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___))) ⟇ ▩) {
    have t2_t13_a29 : π̇ ((¬ ((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___))) ⟇ ▩) {
        apply resolutionₗ _ _ _ t2_t13 a29;
    };
    refine t2_t13_a29;
};
have t2_t15 : π̇ ((¬ (((((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y)))) ⇒ᶜ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___)))) = (((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y)))) ⇒ᶜ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___clt___ = smt__CONSTANT___c1___)))))))
         ⟇ (¬ ((((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y)))) ⇒ᶜ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___))))))
         ⟇ p_84
        ⟇ ▩) {
    apply equiv_pos2;
};
have t2_t16 : π̇ (((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y))) = (`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y))))
        ⟇ ▩) {
    apply ∨ᶜᵢ₁;
    reflexivity;
};
have t2_t17 : π̇ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___))
        ⟇ ▩) {
    apply ∨ᶜᵢ₁;
    reflexivity;
};
have t2_t18 : π̇ (((smt__CONSTANT___c1___ = smt__CONSTANT___clt___) = (smt__CONSTANT___clt___ = smt__CONSTANT___c1___))
        ⟇ ▩) {
    apply ∨ᶜᵢ₁;
    rewrite eq-symm smt__CONSTANT___c1___ smt__CONSTANT___clt___;
    reflexivity;
};
have t2_t19 : π̇ ((((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___)) = ((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___clt___ = smt__CONSTANT___c1___)))
        ⟇ ▩) {
    apply ∨ᶜᵢ₁;
    apply (feq2ᶜ (=) (π̇ₗ t2_t17) (π̇ₗ t2_t18));
};
have t2_t20 : π̇ (p_88 ⟇ ▩) {
    apply ∨ᶜᵢ₁;
    apply (feq2ᶜ (⇒ᶜ) (π̇ₗ t2_t16) (π̇ₗ t2_t19));
};
have t2_t21 : π̇ (p_87
         ⟇ (`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y)))
        ⟇ ▩) {
    apply implies_neg1;
};
have t2_t22 : π̇ ((¬ ((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y)))))
         ⟇ ((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___))
        ⟇ ▩) {
    have t2_t22_a0 : π̇ ((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y)))
            ⟇ ▩) {
        admit;
    };
    have t2_t22_t0 : π̇ (((¬ ((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y))))) ∨ᶜ ((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___)))
            ⟇ ▩) {
        apply ∨ᶜᵢ₁;
        apply imply_to_or;
        apply ⇒ᶜᵢ;
        assume H;
        apply  (∀ᶜₑ smt__CONSTANT___clt___ (∀ᶜₑ smt__CONSTANT___c1___ H));
    };
    have t2_t22_t1 : π̇ (p_21  ⟇ p_86 ⟇ ▩) {
        admit;
    };
    have t2_t22_t2 : π̇ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___))
            ⟇ ▩) {
        have t2_t22_t1_t2_t22_a0 : π̇ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___))
                ⟇ ▩) {
            apply resolutionᵣ _ _ _ t2_t22_t1 t2_t22_a0;
        };
        refine t2_t22_t1_t2_t22_a0;
    };
    apply subproof1 (π̇ₗ t2_t22_a0) (π̇ₗ t2_t22_t2);
};
have t2_t23 : π̇ ((((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y)))) ⇒ᶜ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___))))
         ⟇ ((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___))
        ⟇ ▩) {
    have t2_t21_t2_t22 : π̇ ((((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y)))) ⇒ᶜ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___))))
             ⟇ ((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___))
            ⟇ ▩) {
        have t2_t21' : (π̇ ((((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y)))) ⇒ᶜ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___))))
                 ⟇ (`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y)))
                ⟇ ▩) → π̇ ((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y)))
                 ⟇ (((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y)))) ⇒ᶜ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___))))
                ⟇ ▩)) {
            assume H2;
            apply ⟇ₑ H2 
            {
                assume H;
                apply ⟇ᵢ₂;
                apply H;
            }
            {
                assume H1;
                apply ⟇ᵢ₁;
                apply H1;
            };
        };
        apply resolutionₗ _ _ _ (t2_t21' t2_t21) t2_t22;
    };
    refine t2_t21_t2_t22;
};
have t2_t24 : π̇ (p_87
         ⟇ (¬ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___))))
        ⟇ ▩) {
    apply implies_neg2;
};
have t2_t25 : π̇ ((((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y)))) ⇒ᶜ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___))))
         ⟇ (((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y)))) ⇒ᶜ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___))))
        ⟇ ▩) {
    have t2_t23_t2_t24 : π̇ ((((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y)))) ⇒ᶜ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___))))
             ⟇ (((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y)))) ⇒ᶜ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___))))
            ⟇ ▩) {
        have t2_t23' : (π̇ ((((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y)))) ⇒ᶜ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___))))
                 ⟇ ((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___))
                ⟇ ▩) → π̇ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___))
                 ⟇ (((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y)))) ⇒ᶜ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___))))
                ⟇ ▩)) {
            assume H2;
            apply ⟇ₑ H2 
            {
                assume H;
                apply ⟇ᵢ₂;
                apply H;
            }
            {
                assume H1;
                apply ⟇ᵢ₁;
                apply H1;
            };
        };
        have t2_t24' : (π̇ ((((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y)))) ⇒ᶜ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___))))
                 ⟇ (¬ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___))))
                ⟇ ▩) → π̇ ((¬ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___))))
                 ⟇ (((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y)))) ⇒ᶜ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___))))
                ⟇ ▩)) {
            assume H2;
            apply ⟇ₑ H2 
            {
                assume H;
                apply ⟇ᵢ₂;
                apply H;
            }
            {
                assume H1;
                apply ⟇ᵢ₁;
                apply H1;
            };
        };
        apply resolutionₗ _ _ _ (t2_t23' t2_t23) (t2_t24' t2_t24);
    };
    refine t2_t23_t2_t24;
};
have t2_t26 : π̇ (p_87 ⟇ ▩) {
    admit;
};
have t2_t27 : π̇ ((((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y)))) ⇒ᶜ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___clt___ = smt__CONSTANT___c1___))))
        ⟇ ▩) {
    have t2_t15_t2_t20 : π̇ ((¬ ((((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y)))) ⇒ᶜ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___))))))
             ⟇ (((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y)))) ⇒ᶜ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___clt___ = smt__CONSTANT___c1___))))
            ⟇ ▩) {
        apply resolutionᵣ _ _ _ t2_t15 t2_t20;
    };
    have t2_t15_t2_t20_t2_t26 : π̇ ((((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y)))) ⇒ᶜ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___clt___ = smt__CONSTANT___c1___))))
            ⟇ ▩) {
        apply resolutionᵣ _ _ _ t2_t15_t2_t20 t2_t26;
    };
    refine t2_t15_t2_t20_t2_t26;
};
have t2_t28 : π̇ (p_21  ⟇ p_83 ⟇ ▩) {
    apply implies (π̇ₗ t2_t27);
};
have t2_t29 : π̇ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___clt___ = smt__CONSTANT___c1___))
        ⟇ ▩) {
    have t2_t28_ExtTrigEqDefIdv : π̇ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___clt___ = smt__CONSTANT___c1___))
            ⟇ ▩) {
        apply resolutionᵣ _ _ _ t2_t28 ExtTrigEqDefIdv;
    };
    refine t2_t28_ExtTrigEqDefIdv;
};
have t2_t30 : π̇ ((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ⟇ ▩) {
    have t2_t11_t2_t14 : π̇ ((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___)))
             ⟇ (¬ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___clt___ = smt__CONSTANT___c1___))))
            ⟇ ▩) {
        apply resolutionₗ _ _ _ t2_t11 t2_t14;
    };
    have t2_t11_t2_t14_t2_t29 : π̇ ((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ⟇ ▩) {
        have t2_t11_t2_t14' : (π̇ ((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___)))
                 ⟇ (¬ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___clt___ = smt__CONSTANT___c1___))))
                ⟇ ▩) → π̇ ((¬ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___clt___ = smt__CONSTANT___c1___))))
                 ⟇ (¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___)))
                ⟇ ▩)) {
            assume H2;
            apply ⟇ₑ H2 
            {
                assume H;
                apply ⟇ᵢ₂;
                apply H;
            }
            {
                assume H1;
                apply ⟇ᵢ₁;
                apply H1;
            };
        };
        apply resolutionᵣ _ _ _ (t2_t11_t2_t14' t2_t11_t2_t14) t2_t29;
    };
    refine t2_t11_t2_t14_t2_t29;
};
have t2_t31 : π̇ (p_82  ⟇ p_31 ⟇ ▩) {
    apply and_pos;
    reflexivity;
};
have t2_t32 : π̇ (p_31  ⟇ p_82 ⟇ ▩) {
    admit;
};
have t2_t33 : π̇ (p_81  ⟇ p_37  ⟇ p_34 ⟇ ▩) {
    apply or_pos;
    reflexivity;
};
have t2_t34 : π̇ (p_37  ⟇ p_34  ⟇ p_81 ⟇ ▩) {
    admit;
};
have t2_t35 : π̇ ((((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)) = ⊤) = (smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))
        ⟇ ▩) {
    apply ∨ᶜᵢ₁;
    try rewrite .[ x in x = _ ] equiv_simplify₁;
    try rewrite .[ x in x = _ ] equiv_simplify₂;
    try rewrite .[ x in x = _ ] equiv_simplify₃;
    try rewrite .[ x in x = _ ] equiv_simplify₄;
    try rewrite .[ x in x = _ ] equiv_simplify₅;
    try rewrite .[ x in x = _ ] equiv_simplify₆;
    try rewrite .[ x in x = _ ] equiv_simplify₇;
    try rewrite .[ x in x = _ ] equiv_simplify₈;
    reflexivity;
};
have t2_t36 : π̇ ((¬ (((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)) = ⊤)))
         ⟇ p_36
        ⟇ ▩) {
    apply equiv1 t2_t35;
};
have t2_t37 : π̇ (p_80  ⟇ p_66 ⟇ ▩) {
    apply and_pos;
    reflexivity;
};
have t2_t38 : π̇ (p_66  ⟇ p_80 ⟇ ▩) {
    admit;
};
have t2_t39 : π̇ (p_79  ⟇ p_68  ⟇ p_67 ⟇ ▩) {
    apply or_pos;
    reflexivity;
};
have t2_t40 : π̇ (p_68  ⟇ p_67  ⟇ p_79 ⟇ ▩) {
    admit;
};
have t2_t41 : π̇ (p_6 ⟇ ▩) {
    admit;
};
have t2_t42 : π̇ (p_5 ⟇ ▩) {
    admit;
};
have t2_t43 : π̇ (((¬ ((`∀ᶜ smt__a, `∀ᶜ smt__b, `∀ᶜ smt__f, ((¬ ((smt__TLA______Mem smt__f (smt__TLA______FunSet smt__a smt__b)))) ∨ᶜ ((smt__TLA______FunIsafcn smt__f) ∧ᶜ (smt__a = (smt__TLA______FunDom smt__f))))))) ∨ᶜ ((¬ ((smt__TLA______Mem smt__VARIABLE___alloc___ (smt__TLA______FunSet smt__CONSTANT___Client___ (smt__TLA______Subset smt__CONSTANT___Resource___))))) ∨ᶜ ((smt__TLA______FunIsafcn smt__VARIABLE___alloc___) ∧ᶜ (smt__CONSTANT___Client___ = (smt__TLA______FunDom smt__VARIABLE___alloc___)))))
        ⟇ ▩) {
    apply ∨ᶜᵢ₁;
    apply imply_to_or;
    apply ⇒ᶜᵢ;
    assume H;
    apply  (∀ᶜₑ smt__VARIABLE___alloc___ (∀ᶜₑ (smt__TLA______Subset smt__CONSTANT___Resource___) (∀ᶜₑ smt__CONSTANT___Client___ H)));
};
have t2_t44 : π̇ (p_78  ⟇ p_69 ⟇ ▩) {
    admit;
};
have t2_t45 : π̇ ((¬ (((`∀ᶜ smt__a, `∀ᶜ smt__b, `∀ᶜ smt__f, (((smt__TLA______Mem smt__f (smt__TLA______FunSet smt__a smt__b))) ⇒ᶜ (((smt__TLA______FunIsafcn smt__f) ∧ᶜ ((smt__TLA______FunDom smt__f) = smt__a))))) = (`∀ᶜ smt__a, `∀ᶜ smt__b, `∀ᶜ smt__f, ((¬ ((smt__TLA______Mem smt__f (smt__TLA______FunSet smt__a smt__b)))) ∨ᶜ ((smt__TLA______FunIsafcn smt__f) ∧ᶜ (smt__a = (smt__TLA______FunDom smt__f))))))))
         ⟇ (¬ ((`∀ᶜ smt__a, `∀ᶜ smt__b, `∀ᶜ smt__f, (((smt__TLA______Mem smt__f (smt__TLA______FunSet smt__a smt__b))) ⇒ᶜ (((smt__TLA______FunIsafcn smt__f) ∧ᶜ ((smt__TLA______FunDom smt__f) = smt__a)))))))
         ⟇ (`∀ᶜ smt__a, `∀ᶜ smt__b, `∀ᶜ smt__f, ((¬ ((smt__TLA______Mem smt__f (smt__TLA______FunSet smt__a smt__b)))) ∨ᶜ ((smt__TLA______FunIsafcn smt__f) ∧ᶜ (smt__a = (smt__TLA______FunDom smt__f)))))
        ⟇ ▩) {
    apply equiv_pos2;
};
have t2_t46 : π̇ (((`∀ᶜ smt__a, `∀ᶜ smt__b, `∀ᶜ smt__f, (((smt__TLA______Mem smt__f (smt__TLA______FunSet smt__a smt__b))) ⇒ᶜ (((smt__TLA______FunIsafcn smt__f) ∧ᶜ ((smt__TLA______FunDom smt__f) = smt__a))))) = (`∀ᶜ smt__a, `∀ᶜ smt__b, `∀ᶜ smt__f, (((smt__TLA______Mem smt__f (smt__TLA______FunSet smt__a smt__b))) ⇒ᶜ (((smt__TLA______FunIsafcn smt__f) ∧ᶜ (smt__a = (smt__TLA______FunDom smt__f)))))))
        ⟇ ▩) {
    apply ∨ᶜᵢ₁;
    apply bind_∀;
    assume smt__a;
    apply bind_∀;
    assume smt__b;
    apply bind_∀;
    assume smt__f;
    have t2_t46_t0 : π̇ (((smt__TLA______Mem smt__f (smt__TLA______FunSet smt__a smt__b)) = (smt__TLA______Mem smt__f (smt__TLA______FunSet smt__a smt__b)))
            ⟇ ▩) {
        apply ∨ᶜᵢ₁;
        reflexivity;
    };
    have t2_t46_t1 : π̇ (((smt__TLA______FunIsafcn smt__f) = (smt__TLA______FunIsafcn smt__f)) ⟇ ▩) {
        apply ∨ᶜᵢ₁;
        reflexivity;
    };
    have t2_t46_t2 : π̇ ((((smt__TLA______FunDom smt__f) = smt__a) = (smt__a = (smt__TLA______FunDom smt__f))) ⟇ ▩) {
        apply ∨ᶜᵢ₁;
        rewrite eq-symm (smt__TLA______FunDom smt__f) smt__a;
        reflexivity;
    };
    have t2_t46_t3 : π̇ ((((smt__TLA______FunIsafcn smt__f) ∧ᶜ ((smt__TLA______FunDom smt__f) = smt__a)) = ((smt__TLA______FunIsafcn smt__f) ∧ᶜ (smt__a = (smt__TLA______FunDom smt__f))))
            ⟇ ▩) {
        apply ∨ᶜᵢ₁;
        rewrite .[ x in x ∧ᶜ _ ] (π̇ₗ t2_t46_t1);
        rewrite .[ x in _ ∧ᶜ x ] (π̇ₗ t2_t46_t2);
        reflexivity;
    };
    have t2_t46_t4 : π̇ (((((smt__TLA______Mem smt__f (smt__TLA______FunSet smt__a smt__b))) ⇒ᶜ (((smt__TLA______FunIsafcn smt__f) ∧ᶜ ((smt__TLA______FunDom smt__f) = smt__a)))) = (((smt__TLA______Mem smt__f (smt__TLA______FunSet smt__a smt__b))) ⇒ᶜ (((smt__TLA______FunIsafcn smt__f) ∧ᶜ (smt__a = (smt__TLA______FunDom smt__f))))))
            ⟇ ▩) {
        apply ∨ᶜᵢ₁;
        apply (feq2ᶜ (⇒ᶜ) (π̇ₗ t2_t46_t0) (π̇ₗ t2_t46_t3));
    };
    apply π̇ₗ t2_t46_t4;
};
have t2_t47 : π̇ (((`∀ᶜ smt__a, `∀ᶜ smt__b, `∀ᶜ smt__f, (((smt__TLA______Mem smt__f (smt__TLA______FunSet smt__a smt__b))) ⇒ᶜ (((smt__TLA______FunIsafcn smt__f) ∧ᶜ (smt__a = (smt__TLA______FunDom smt__f)))))) = (`∀ᶜ smt__a, `∀ᶜ smt__b, `∀ᶜ smt__f, ((¬ ((smt__TLA______Mem smt__f (smt__TLA______FunSet smt__a smt__b)))) ∨ᶜ ((smt__TLA______FunIsafcn smt__f) ∧ᶜ (smt__a = (smt__TLA______FunDom smt__f))))))
        ⟇ ▩) {
    admit;
};
have t2_t48 : π̇ (p_70 ⟇ ▩) {
    apply ∨ᶜᵢ₁;
    rewrite (π̇ₗ t2_t46);
    rewrite (π̇ₗ t2_t47);
    reflexivity;
};
have t2_t49 : π̇ ((`∀ᶜ smt__a, `∀ᶜ smt__b, `∀ᶜ smt__f, ((¬ ((smt__TLA______Mem smt__f (smt__TLA______FunSet smt__a smt__b)))) ∨ᶜ ((smt__TLA______FunIsafcn smt__f) ∧ᶜ (smt__a = (smt__TLA______FunDom smt__f)))))
        ⟇ ▩) {
    have t2_t45_t2_t48 : π̇ ((¬ ((`∀ᶜ smt__a, `∀ᶜ smt__b, `∀ᶜ smt__f, (((smt__TLA______Mem smt__f (smt__TLA______FunSet smt__a smt__b))) ⇒ᶜ (((smt__TLA______FunIsafcn smt__f) ∧ᶜ ((smt__TLA______FunDom smt__f) = smt__a)))))))
             ⟇ (`∀ᶜ smt__a, `∀ᶜ smt__b, `∀ᶜ smt__f, ((¬ ((smt__TLA______Mem smt__f (smt__TLA______FunSet smt__a smt__b)))) ∨ᶜ ((smt__TLA______FunIsafcn smt__f) ∧ᶜ (smt__a = (smt__TLA______FunDom smt__f)))))
            ⟇ ▩) {
        apply resolutionᵣ _ _ _ t2_t45 t2_t48;
    };
    have t2_t45_t2_t48_FunSetElim1 : π̇ ((`∀ᶜ smt__a, `∀ᶜ smt__b, `∀ᶜ smt__f, ((¬ ((smt__TLA______Mem smt__f (smt__TLA______FunSet smt__a smt__b)))) ∨ᶜ ((smt__TLA______FunIsafcn smt__f) ∧ᶜ (smt__a = (smt__TLA______FunDom smt__f)))))
            ⟇ ▩) {
        apply resolutionᵣ _ _ _ t2_t45_t2_t48 FunSetElim1;
    };
    refine t2_t45_t2_t48_FunSetElim1;
};
have t2_t50 : π̇ (((¬ ((smt__TLA______Mem smt__VARIABLE___alloc___ (smt__TLA______FunSet smt__CONSTANT___Client___ (smt__TLA______Subset smt__CONSTANT___Resource___))))) ∨ᶜ ((smt__TLA______FunIsafcn smt__VARIABLE___alloc___) ∧ᶜ (smt__CONSTANT___Client___ = (smt__TLA______FunDom smt__VARIABLE___alloc___))))
        ⟇ ▩) {
    have t2_t44_t2_t49 : π̇ (((¬ ((smt__TLA______Mem smt__VARIABLE___alloc___ (smt__TLA______FunSet smt__CONSTANT___Client___ (smt__TLA______Subset smt__CONSTANT___Resource___))))) ∨ᶜ ((smt__TLA______FunIsafcn smt__VARIABLE___alloc___) ∧ᶜ (smt__CONSTANT___Client___ = (smt__TLA______FunDom smt__VARIABLE___alloc___))))
            ⟇ ▩) {
        apply resolutionᵣ _ _ _ t2_t44 t2_t49;
    };
    refine t2_t44_t2_t49;
};
have t2_t51 : π̇ (((smt__TLA______FunIsafcn smt__VARIABLE___alloc___) ∧ᶜ (smt__CONSTANT___Client___ = (smt__TLA______FunDom smt__VARIABLE___alloc___)))
        ⟇ ▩) {
    have t2_t40_t2_t42 : π̇ (((smt__TLA______FunIsafcn smt__VARIABLE___alloc___) ∧ᶜ (smt__CONSTANT___Client___ = (smt__TLA______FunDom smt__VARIABLE___alloc___)))
             ⟇ (¬ (((¬ ((smt__TLA______Mem smt__VARIABLE___alloc___ (smt__TLA______FunSet smt__CONSTANT___Client___ (smt__TLA______Subset smt__CONSTANT___Resource___))))) ∨ᶜ ((smt__TLA______FunIsafcn smt__VARIABLE___alloc___) ∧ᶜ (smt__CONSTANT___Client___ = (smt__TLA______FunDom smt__VARIABLE___alloc___))))))
            ⟇ ▩) {
        apply resolutionᵣ _ _ _ t2_t40 t2_t42;
    };
    have t2_t40_t2_t42_t2_t50 : π̇ (((smt__TLA______FunIsafcn smt__VARIABLE___alloc___) ∧ᶜ (smt__CONSTANT___Client___ = (smt__TLA______FunDom smt__VARIABLE___alloc___)))
            ⟇ ▩) {
        have t2_t40_t2_t42' : (π̇ (((smt__TLA______FunIsafcn smt__VARIABLE___alloc___) ∧ᶜ (smt__CONSTANT___Client___ = (smt__TLA______FunDom smt__VARIABLE___alloc___)))
                 ⟇ (¬ (((¬ ((smt__TLA______Mem smt__VARIABLE___alloc___ (smt__TLA______FunSet smt__CONSTANT___Client___ (smt__TLA______Subset smt__CONSTANT___Resource___))))) ∨ᶜ ((smt__TLA______FunIsafcn smt__VARIABLE___alloc___) ∧ᶜ (smt__CONSTANT___Client___ = (smt__TLA______FunDom smt__VARIABLE___alloc___))))))
                ⟇ ▩) → π̇ ((¬ (((¬ ((smt__TLA______Mem smt__VARIABLE___alloc___ (smt__TLA______FunSet smt__CONSTANT___Client___ (smt__TLA______Subset smt__CONSTANT___Resource___))))) ∨ᶜ ((smt__TLA______FunIsafcn smt__VARIABLE___alloc___) ∧ᶜ (smt__CONSTANT___Client___ = (smt__TLA______FunDom smt__VARIABLE___alloc___))))))
                 ⟇ ((smt__TLA______FunIsafcn smt__VARIABLE___alloc___) ∧ᶜ (smt__CONSTANT___Client___ = (smt__TLA______FunDom smt__VARIABLE___alloc___)))
                ⟇ ▩)) {
            assume H2;
            apply ⟇ₑ H2 
            {
                assume H;
                apply ⟇ᵢ₂;
                apply H;
            }
            {
                assume H1;
                apply ⟇ᵢ₁;
                apply H1;
            };
        };
        apply resolutionᵣ _ _ _ (t2_t40_t2_t42' t2_t40_t2_t42) t2_t50;
    };
    refine t2_t40_t2_t42_t2_t50;
};
have t2_t52 : π̇ ((smt__CONSTANT___Client___ = (smt__TLA______FunDom smt__VARIABLE___alloc___)) ⟇ ▩) {
    have t2_t38_t2_t51 : π̇ ((smt__CONSTANT___Client___ = (smt__TLA______FunDom smt__VARIABLE___alloc___)) ⟇ ▩) {
        have t2_t38' : (π̇ ((smt__CONSTANT___Client___ = (smt__TLA______FunDom smt__VARIABLE___alloc___))
                 ⟇ (¬ (((smt__TLA______FunIsafcn smt__VARIABLE___alloc___) ∧ᶜ (smt__CONSTANT___Client___ = (smt__TLA______FunDom smt__VARIABLE___alloc___)))))
                ⟇ ▩) → π̇ ((¬ (((smt__TLA______FunIsafcn smt__VARIABLE___alloc___) ∧ᶜ (smt__CONSTANT___Client___ = (smt__TLA______FunDom smt__VARIABLE___alloc___)))))
                 ⟇ (smt__CONSTANT___Client___ = (smt__TLA______FunDom smt__VARIABLE___alloc___))
                ⟇ ▩)) {
            assume H2;
            apply ⟇ₑ H2 
            {
                assume H;
                apply ⟇ᵢ₂;
                apply H;
            }
            {
                assume H1;
                apply ⟇ᵢ₁;
                apply H1;
            };
        };
        apply resolutionᵣ _ _ _ (t2_t38' t2_t38) t2_t51;
    };
    refine t2_t38_t2_t51;
};
have t2_t53 : π̇ (((smt__TLA______FunDom smt__VARIABLE___alloc___) = smt__CONSTANT___Client___) ⟇ ▩) {
    apply ∨ᶜᵢ₁;
    symmetry;
    apply (π̇ₗ t2_t52);
};
have t2_t54 : π̇ (((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)) = (smt__TLA______Mem smt__CONSTANT___c1___ smt__CONSTANT___Client___))
        ⟇ ▩) {
    apply ∨ᶜᵢ₁;
    apply feq2ᶜ smt__TLA______Mem (π̇ₗ t2_t6) (π̇ₗ t2_t53);
};
have t2_t55 : π̇ ((((smt__TLA______Mem smt__CONSTANT___c1___ smt__CONSTANT___Client___) = ⊤) = (smt__TLA______Mem smt__CONSTANT___c1___ smt__CONSTANT___Client___))
        ⟇ ▩) {
    apply ∨ᶜᵢ₁;
    try rewrite .[ x in x = _ ] equiv_simplify₁;
    try rewrite .[ x in x = _ ] equiv_simplify₂;
    try rewrite .[ x in x = _ ] equiv_simplify₃;
    try rewrite .[ x in x = _ ] equiv_simplify₄;
    try rewrite .[ x in x = _ ] equiv_simplify₅;
    try rewrite .[ x in x = _ ] equiv_simplify₆;
    try rewrite .[ x in x = _ ] equiv_simplify₇;
    try rewrite .[ x in x = _ ] equiv_simplify₈;
    reflexivity;
};
have t2_t56 : π̇ (p_65  ⟇ (¬ ((smt__TLA______Mem smt__CONSTANT___c1___ smt__CONSTANT___Client___))) ⟇ ▩) {
    apply equiv2 t2_t55;
};
have t2_t57 : π̇ (((smt__TLA______Mem smt__CONSTANT___c1___ smt__CONSTANT___Client___) = ⊤) ⟇ ▩) {
    have t2_t56_a22 : π̇ (((smt__TLA______Mem smt__CONSTANT___c1___ smt__CONSTANT___Client___) = ⊤) ⟇ ▩) {
        have t2_t56' : (π̇ (((smt__TLA______Mem smt__CONSTANT___c1___ smt__CONSTANT___Client___) = ⊤)
                 ⟇ (¬ ((smt__TLA______Mem smt__CONSTANT___c1___ smt__CONSTANT___Client___)))
                ⟇ ▩) → π̇ ((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ smt__CONSTANT___Client___)))
                 ⟇ ((smt__TLA______Mem smt__CONSTANT___c1___ smt__CONSTANT___Client___) = ⊤)
                ⟇ ▩)) {
            assume H2;
            apply ⟇ₑ H2 
            {
                assume H;
                apply ⟇ᵢ₂;
                apply H;
            }
            {
                assume H1;
                apply ⟇ᵢ₁;
                apply H1;
            };
        };
        apply resolutionᵣ _ _ _ (t2_t56' t2_t56) a22;
    };
    refine t2_t56_a22;
};
have t2_t58 : π̇ (p_64 ⟇ ▩) {
    apply ∨ᶜᵢ₁;
    rewrite (π̇ₗ t2_t54);
    rewrite (π̇ₗ t2_t57);
    reflexivity;
};
have t2_t59 : π̇ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)) ⟇ ▩) {
    have t2_t36_t2_t58 : π̇ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___))
            ⟇ ▩) {
        apply resolutionᵣ _ _ _ t2_t36 t2_t58;
    };
    refine t2_t36_t2_t58;
};
have t2_t60 : π̇ ((¬ (((((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))) ⇒ᶜ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___))))))) = (((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))) ⇒ᶜ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))))))))))
         ⟇ (¬ ((((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))) ⇒ᶜ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))))))))
         ⟇ p_57
        ⟇ ▩) {
    apply equiv_pos2;
};
have t2_t61 : π̇ (((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z)))))) = (`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z)))))))
        ⟇ ▩) {
    apply ∨ᶜᵢ₁;
    reflexivity;
};
have t2_t62 : π̇ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) = (¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))))
        ⟇ ▩) {
    apply ∨ᶜᵢ₁;
    reflexivity;
};
have t2_t63 : π̇ ((((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) = ((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))))
        ⟇ ▩) {
    apply ∨ᶜᵢ₁;
    reflexivity;
};
have t2_t64 : π̇ (((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) = (smt__CONSTANT___clt___ = smt__CONSTANT___c1___))
        ⟇ ▩) {
    apply ∨ᶜᵢ₁;
    reflexivity;
};
have t2_t65 : π̇ ((((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)) = ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___)))
        ⟇ ▩) {
    apply ∨ᶜᵢ₁;
    rewrite eq-symm (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___);
    reflexivity;
};
have t2_t66 : π̇ ((((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___))) = ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))))
        ⟇ ▩) {
    apply ∨ᶜᵢ₁;
    rewrite .[ x in x ∨ᶜ _ ] (π̇ₗ t2_t64);
    rewrite .[ x in _ ∨ᶜ x ] (π̇ₗ t2_t65);
    reflexivity;
};
have t2_t67 : π̇ (((((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))) = (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___)))))
        ⟇ ▩) {
    apply ∨ᶜᵢ₁;
    rewrite .[ x in x ∧ᶜ _ ] (π̇ₗ t2_t63);
    rewrite .[ x in _ ∧ᶜ x ] (π̇ₗ t2_t66);
    reflexivity;
};
have t2_t68 : π̇ ((((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___))))) = ((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))))))
        ⟇ ▩) {
    apply ∨ᶜᵢ₁;
    rewrite .[ x in x ∨ᶜ _ ] (π̇ₗ t2_t62);
    rewrite .[ x in _ ∨ᶜ x ] (π̇ₗ t2_t67);
    reflexivity;
};
have t2_t69 : π̇ (p_63 ⟇ ▩) {
    apply ∨ᶜᵢ₁;
    apply (feq2ᶜ (⇒ᶜ) (π̇ₗ t2_t61) (π̇ₗ t2_t68));
};
have t2_t70 : π̇ (p_62
         ⟇ (`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))
        ⟇ ▩) {
    apply implies_neg1;
};
have t2_t71 : π̇ ((¬ ((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))))
         ⟇ ((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))))
        ⟇ ▩) {
    have t2_t71_a0 : π̇ ((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))
            ⟇ ▩) {
        admit;
    };
    have t2_t71_t0 : π̇ (((¬ ((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z)))))))) ∨ᶜ ((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___))))))
            ⟇ ▩) {
        apply ∨ᶜᵢ₁;
        apply imply_to_or;
        apply ⇒ᶜᵢ;
        assume H;
        apply  (∀ᶜₑ smt__CONSTANT___c1___ (∀ᶜₑ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) (∀ᶜₑ smt__CONSTANT___clt___ (∀ᶜₑ smt__VARIABLE___alloc___ H))));
    };
    have t2_t71_t1 : π̇ (p_56  ⟇ p_61 ⟇ ▩) {
        admit;
    };
    have t2_t71_t2 : π̇ ((¬ (((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, (((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f))) ⇒ᶜ (((((smt__z = smt__x)) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = smt__y))) ∧ᶜ (((distinct 2 (cons _  smt__z (cons _  smt__x □)))) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z)))))))) = (`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z)))))))))
             ⟇ (¬ ((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, (((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f))) ⇒ᶜ (((((smt__z = smt__x)) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = smt__y))) ∧ᶜ (((distinct 2 (cons _  smt__z (cons _  smt__x □)))) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))))))
             ⟇ (`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))
            ⟇ ▩) {
        apply equiv_pos2;
    };
    have t2_t71_t3 : π̇ (((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, (((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f))) ⇒ᶜ (((((smt__z = smt__x)) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = smt__y))) ∧ᶜ (((distinct 2 (cons _  smt__z (cons _  smt__x □)))) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z)))))))) = (`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, (((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f))) ⇒ᶜ (((((smt__x = smt__z)) ⇒ᶜ ((smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z)))) ∧ᶜ (((¬ ((smt__x = smt__z)))) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z)))))))))
            ⟇ ▩) {
        apply ∨ᶜᵢ₁;
        apply bind_∀;
        assume smt__f;
        apply bind_∀;
        assume smt__x;
        apply bind_∀;
        assume smt__y;
        apply bind_∀;
        assume smt__z;
        have t2_t71_t3_t0 : π̇ (((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)) = (smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))
                ⟇ ▩) {
            apply ∨ᶜᵢ₁;
            reflexivity;
        };
        have t2_t71_t3_t1 : π̇ (((smt__z = smt__x) = (smt__x = smt__z)) ⟇ ▩) {
            apply ∨ᶜᵢ₁;
            rewrite eq-symm smt__z smt__x;
            reflexivity;
        };
        have t2_t71_t3_t2 : π̇ ((((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = smt__y) = (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z)))
                ⟇ ▩) {
            apply ∨ᶜᵢ₁;
            rewrite eq-symm (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) smt__y;
            reflexivity;
        };
        have t2_t71_t3_t3 : π̇ (((((smt__z = smt__x)) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = smt__y))) = (((smt__x = smt__z)) ⇒ᶜ ((smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z)))))
                ⟇ ▩) {
            apply ∨ᶜᵢ₁;
            apply (feq2ᶜ (⇒ᶜ) (π̇ₗ t2_t71_t3_t1) (π̇ₗ t2_t71_t3_t2));
        };
        have t2_t71_t3_t4 : π̇ (((distinct 2 (cons _  smt__z (cons _  smt__x □))) = (¬ ((smt__z = smt__x)))) ⟇ ▩) {
            apply ∨ᶜᵢ₁;
            rewrite distinct-binary-elim smt__z smt__x;
            reflexivity;
        };
        have t2_t71_t3_t5 : π̇ (((¬ ((smt__z = smt__x))) = (¬ ((smt__x = smt__z)))) ⟇ ▩) {
            apply ∨ᶜᵢ₁;
            apply feqᶜ (¬) (π̇ₗ t2_t71_t3_t1);
        };
        have t2_t71_t3_t6 : π̇ (((distinct 2 (cons _  smt__z (cons _  smt__x □))) = (¬ ((smt__x = smt__z)))) ⟇ ▩) {
            apply ∨ᶜᵢ₁;
            rewrite (π̇ₗ t2_t71_t3_t4);
            rewrite (π̇ₗ t2_t71_t3_t5);
            reflexivity;
        };
        have t2_t71_t3_t7 : π̇ ((((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z)) = ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z)))
                ⟇ ▩) {
            apply ∨ᶜᵢ₁;
            reflexivity;
        };
        have t2_t71_t3_t8 : π̇ (((((distinct 2 (cons _  smt__z (cons _  smt__x □)))) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z)))) = (((¬ ((smt__x = smt__z)))) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z)))))
                ⟇ ▩) {
            apply ∨ᶜᵢ₁;
            apply (feq2ᶜ (⇒ᶜ) (π̇ₗ t2_t71_t3_t6) (π̇ₗ t2_t71_t3_t7));
        };
        have t2_t71_t3_t9 : π̇ ((((((smt__z = smt__x)) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = smt__y))) ∧ᶜ (((distinct 2 (cons _  smt__z (cons _  smt__x □)))) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))) = ((((smt__x = smt__z)) ⇒ᶜ ((smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z)))) ∧ᶜ (((¬ ((smt__x = smt__z)))) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))
                ⟇ ▩) {
            apply ∨ᶜᵢ₁;
            rewrite .[ x in x ∧ᶜ _ ] (π̇ₗ t2_t71_t3_t3);
            rewrite .[ x in _ ∧ᶜ x ] (π̇ₗ t2_t71_t3_t8);
            reflexivity;
        };
        have t2_t71_t3_t10 : π̇ (((((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f))) ⇒ᶜ (((((smt__z = smt__x)) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = smt__y))) ∧ᶜ (((distinct 2 (cons _  smt__z (cons _  smt__x □)))) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))) = (((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f))) ⇒ᶜ (((((smt__x = smt__z)) ⇒ᶜ ((smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z)))) ∧ᶜ (((¬ ((smt__x = smt__z)))) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))))
                ⟇ ▩) {
            apply ∨ᶜᵢ₁;
            apply (feq2ᶜ (⇒ᶜ) (π̇ₗ t2_t71_t3_t0) (π̇ₗ t2_t71_t3_t9));
        };
        apply π̇ₗ t2_t71_t3_t10;
    };
    have t2_t71_t4 : π̇ (((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, (((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f))) ⇒ᶜ (((((smt__x = smt__z)) ⇒ᶜ ((smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z)))) ∧ᶜ (((¬ ((smt__x = smt__z)))) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z)))))))) = (`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z)))))))
            ⟇ ▩) {
        admit;
    };
    have t2_t71_t5 : π̇ (p_39 ⟇ ▩) {
        apply ∨ᶜᵢ₁;
        rewrite (π̇ₗ t2_t71_t3);
        rewrite (π̇ₗ t2_t71_t4);
        reflexivity;
    };
    have t2_t71_t6 : π̇ ((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))
            ⟇ ▩) {
        have t2_t71_t2_t2_t71_t5 : π̇ ((¬ ((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, (((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f))) ⇒ᶜ (((((smt__z = smt__x)) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = smt__y))) ∧ᶜ (((distinct 2 (cons _  smt__z (cons _  smt__x □)))) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))))))
                 ⟇ (`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))
                ⟇ ▩) {
            apply resolutionᵣ _ _ _ t2_t71_t2 t2_t71_t5;
        };
        have t2_t71_t2_t2_t71_t5_FunExceptAppDef2 : π̇ ((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))
                ⟇ ▩) {
            apply resolutionᵣ _ _ _ t2_t71_t2_t2_t71_t5 FunExceptAppDef2;
        };
        refine t2_t71_t2_t2_t71_t5_FunExceptAppDef2;
    };
    have t2_t71_t7 : π̇ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))))
            ⟇ ▩) {
        have t2_t71_t1_t2_t71_t6 : π̇ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))))
                ⟇ ▩) {
            apply resolutionᵣ _ _ _ t2_t71_t1 t2_t71_t6;
        };
        refine t2_t71_t1_t2_t71_t6;
    };
    apply subproof1 (π̇ₗ t2_t71_a0) (π̇ₗ t2_t71_t7);
};
have t2_t72 : π̇ ((((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))) ⇒ᶜ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))))))
         ⟇ ((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))))
        ⟇ ▩) {
    have t2_t70_t2_t71 : π̇ ((((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))) ⇒ᶜ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))))))
             ⟇ ((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))))
            ⟇ ▩) {
        have t2_t70' : (π̇ ((((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))) ⇒ᶜ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))))))
                 ⟇ (`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))
                ⟇ ▩) → π̇ ((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))
                 ⟇ (((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))) ⇒ᶜ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))))))
                ⟇ ▩)) {
            assume H2;
            apply ⟇ₑ H2 
            {
                assume H;
                apply ⟇ᵢ₂;
                apply H;
            }
            {
                assume H1;
                apply ⟇ᵢ₁;
                apply H1;
            };
        };
        apply resolutionₗ _ _ _ (t2_t70' t2_t70) t2_t71;
    };
    refine t2_t70_t2_t71;
};
have t2_t73 : π̇ (p_62
         ⟇ (¬ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))))))
        ⟇ ▩) {
    apply implies_neg2;
};
have t2_t74 : π̇ ((((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))) ⇒ᶜ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))))))
         ⟇ (((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))) ⇒ᶜ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))))))
        ⟇ ▩) {
    have t2_t72_t2_t73 : π̇ ((((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))) ⇒ᶜ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))))))
             ⟇ (((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))) ⇒ᶜ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))))))
            ⟇ ▩) {
        have t2_t72' : (π̇ ((((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))) ⇒ᶜ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))))))
                 ⟇ ((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))))
                ⟇ ▩) → π̇ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))))
                 ⟇ (((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))) ⇒ᶜ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))))))
                ⟇ ▩)) {
            assume H2;
            apply ⟇ₑ H2 
            {
                assume H;
                apply ⟇ᵢ₂;
                apply H;
            }
            {
                assume H1;
                apply ⟇ᵢ₁;
                apply H1;
            };
        };
        have t2_t73' : (π̇ ((((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))) ⇒ᶜ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))))))
                 ⟇ (¬ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))))))
                ⟇ ▩) → π̇ ((¬ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))))))
                 ⟇ (((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))) ⇒ᶜ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))))))
                ⟇ ▩)) {
            assume H2;
            apply ⟇ₑ H2 
            {
                assume H;
                apply ⟇ᵢ₂;
                apply H;
            }
            {
                assume H1;
                apply ⟇ᵢ₁;
                apply H1;
            };
        };
        apply resolutionₗ _ _ _ (t2_t72' t2_t72) (t2_t73' t2_t73);
    };
    refine t2_t72_t2_t73;
};
have t2_t75 : π̇ (p_62 ⟇ ▩) {
    admit;
};
have t2_t76 : π̇ ((((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))) ⇒ᶜ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___)))))))
        ⟇ ▩) {
    have t2_t60_t2_t69 : π̇ ((¬ ((((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))) ⇒ᶜ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))))))))
             ⟇ (((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))) ⇒ᶜ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___)))))))
            ⟇ ▩) {
        apply resolutionᵣ _ _ _ t2_t60 t2_t69;
    };
    have t2_t60_t2_t69_t2_t75 : π̇ ((((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))) ⇒ᶜ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___)))))))
            ⟇ ▩) {
        apply resolutionᵣ _ _ _ t2_t60_t2_t69 t2_t75;
    };
    refine t2_t60_t2_t69_t2_t75;
};
have t2_t77 : π̇ (p_56  ⟇ p_38 ⟇ ▩) {
    apply implies (π̇ₗ t2_t76);
};
have t2_t78 : π̇ ((¬ (((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, (((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f))) ⇒ᶜ (((((smt__z = smt__x)) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = smt__y))) ∧ᶜ (((distinct 2 (cons _  smt__z (cons _  smt__x □)))) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z)))))))) = (`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z)))))))))
         ⟇ (¬ ((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, (((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f))) ⇒ᶜ (((((smt__z = smt__x)) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = smt__y))) ∧ᶜ (((distinct 2 (cons _  smt__z (cons _  smt__x □)))) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))))))
         ⟇ (`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))
        ⟇ ▩) {
    apply equiv_pos2;
};
have t2_t79 : π̇ (((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, (((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f))) ⇒ᶜ (((((smt__z = smt__x)) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = smt__y))) ∧ᶜ (((distinct 2 (cons _  smt__z (cons _  smt__x □)))) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z)))))))) = (`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, (((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f))) ⇒ᶜ (((((smt__x = smt__z)) ⇒ᶜ ((smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z)))) ∧ᶜ (((¬ ((smt__x = smt__z)))) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z)))))))))
        ⟇ ▩) {
    apply ∨ᶜᵢ₁;
    apply bind_∀;
    assume smt__f;
    apply bind_∀;
    assume smt__x;
    apply bind_∀;
    assume smt__y;
    apply bind_∀;
    assume smt__z;
    have t2_t79_t0 : π̇ (((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)) = (smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))
            ⟇ ▩) {
        apply ∨ᶜᵢ₁;
        reflexivity;
    };
    have t2_t79_t1 : π̇ (((smt__z = smt__x) = (smt__x = smt__z)) ⟇ ▩) {
        apply ∨ᶜᵢ₁;
        rewrite eq-symm smt__z smt__x;
        reflexivity;
    };
    have t2_t79_t2 : π̇ ((((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = smt__y) = (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z)))
            ⟇ ▩) {
        apply ∨ᶜᵢ₁;
        rewrite eq-symm (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) smt__y;
        reflexivity;
    };
    have t2_t79_t3 : π̇ (((((smt__z = smt__x)) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = smt__y))) = (((smt__x = smt__z)) ⇒ᶜ ((smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z)))))
            ⟇ ▩) {
        apply ∨ᶜᵢ₁;
        apply (feq2ᶜ (⇒ᶜ) (π̇ₗ t2_t79_t1) (π̇ₗ t2_t79_t2));
    };
    have t2_t79_t4 : π̇ (((distinct 2 (cons _  smt__z (cons _  smt__x □))) = (¬ ((smt__z = smt__x)))) ⟇ ▩) {
        apply ∨ᶜᵢ₁;
        rewrite distinct-binary-elim smt__z smt__x;
        reflexivity;
    };
    have t2_t79_t5 : π̇ (((¬ ((smt__z = smt__x))) = (¬ ((smt__x = smt__z)))) ⟇ ▩) {
        apply ∨ᶜᵢ₁;
        apply feqᶜ (¬) (π̇ₗ t2_t79_t1);
    };
    have t2_t79_t6 : π̇ (((distinct 2 (cons _  smt__z (cons _  smt__x □))) = (¬ ((smt__x = smt__z)))) ⟇ ▩) {
        apply ∨ᶜᵢ₁;
        rewrite (π̇ₗ t2_t79_t4);
        rewrite (π̇ₗ t2_t79_t5);
        reflexivity;
    };
    have t2_t79_t7 : π̇ ((((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z)) = ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z)))
            ⟇ ▩) {
        apply ∨ᶜᵢ₁;
        reflexivity;
    };
    have t2_t79_t8 : π̇ (((((distinct 2 (cons _  smt__z (cons _  smt__x □)))) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z)))) = (((¬ ((smt__x = smt__z)))) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z)))))
            ⟇ ▩) {
        apply ∨ᶜᵢ₁;
        apply (feq2ᶜ (⇒ᶜ) (π̇ₗ t2_t79_t6) (π̇ₗ t2_t79_t7));
    };
    have t2_t79_t9 : π̇ ((((((smt__z = smt__x)) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = smt__y))) ∧ᶜ (((distinct 2 (cons _  smt__z (cons _  smt__x □)))) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))) = ((((smt__x = smt__z)) ⇒ᶜ ((smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z)))) ∧ᶜ (((¬ ((smt__x = smt__z)))) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))
            ⟇ ▩) {
        apply ∨ᶜᵢ₁;
        rewrite .[ x in x ∧ᶜ _ ] (π̇ₗ t2_t79_t3);
        rewrite .[ x in _ ∧ᶜ x ] (π̇ₗ t2_t79_t8);
        reflexivity;
    };
    have t2_t79_t10 : π̇ (((((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f))) ⇒ᶜ (((((smt__z = smt__x)) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = smt__y))) ∧ᶜ (((distinct 2 (cons _  smt__z (cons _  smt__x □)))) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))) = (((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f))) ⇒ᶜ (((((smt__x = smt__z)) ⇒ᶜ ((smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z)))) ∧ᶜ (((¬ ((smt__x = smt__z)))) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))))
            ⟇ ▩) {
        apply ∨ᶜᵢ₁;
        apply (feq2ᶜ (⇒ᶜ) (π̇ₗ t2_t79_t0) (π̇ₗ t2_t79_t9));
    };
    apply π̇ₗ t2_t79_t10;
};
have t2_t80 : π̇ (((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, (((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f))) ⇒ᶜ (((((smt__x = smt__z)) ⇒ᶜ ((smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z)))) ∧ᶜ (((¬ ((smt__x = smt__z)))) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z)))))))) = (`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z)))))))
        ⟇ ▩) {
    admit;
};
have t2_t81 : π̇ (p_39 ⟇ ▩) {
    apply ∨ᶜᵢ₁;
    rewrite (π̇ₗ t2_t79);
    rewrite (π̇ₗ t2_t80);
    reflexivity;
};
have t2_t82 : π̇ ((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))
        ⟇ ▩) {
    have t2_t78_t2_t81 : π̇ ((¬ ((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, (((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f))) ⇒ᶜ (((((smt__z = smt__x)) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = smt__y))) ∧ᶜ (((distinct 2 (cons _  smt__z (cons _  smt__x □)))) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))))))
             ⟇ (`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))
            ⟇ ▩) {
        apply resolutionᵣ _ _ _ t2_t78 t2_t81;
    };
    have t2_t78_t2_t81_FunExceptAppDef2 : π̇ ((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))
            ⟇ ▩) {
        apply resolutionᵣ _ _ _ t2_t78_t2_t81 FunExceptAppDef2;
    };
    refine t2_t78_t2_t81_FunExceptAppDef2;
};
have t2_t83 : π̇ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___)))))
        ⟇ ▩) {
    have t2_t77_t2_t82 : π̇ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___)))))
            ⟇ ▩) {
        apply resolutionᵣ _ _ _ t2_t77 t2_t82;
    };
    refine t2_t77_t2_t82;
};
have t2_t84 : π̇ ((((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))))
        ⟇ ▩) {
    have t2_t34_t2_t59 : π̇ ((((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))))
             ⟇ (¬ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___)))))))
            ⟇ ▩) {
        apply resolutionᵣ _ _ _ t2_t34 t2_t59;
    };
    have t2_t34_t2_t59_t2_t83 : π̇ ((((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))))
            ⟇ ▩) {
        have t2_t34_t2_t59' : (π̇ ((((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))))
                 ⟇ (¬ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___)))))))
                ⟇ ▩) → π̇ ((¬ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___)))))))
                 ⟇ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))))
                ⟇ ▩)) {
            assume H2;
            apply ⟇ₑ H2 
            {
                assume H;
                apply ⟇ᵢ₂;
                apply H;
            }
            {
                assume H1;
                apply ⟇ᵢ₁;
                apply H1;
            };
        };
        apply resolutionᵣ _ _ _ (t2_t34_t2_t59' t2_t34_t2_t59) t2_t83;
    };
    refine t2_t34_t2_t59_t2_t83;
};
have t2_t85 : π̇ (((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___)))
        ⟇ ▩) {
    have t2_t32_t2_t84 : π̇ (((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___)))
            ⟇ ▩) {
        have t2_t32' : (π̇ (((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___)))
                 ⟇ (¬ ((((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))))))
                ⟇ ▩) → π̇ ((¬ ((((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))))))
                 ⟇ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___)))
                ⟇ ▩)) {
            assume H2;
            apply ⟇ₑ H2 
            {
                assume H;
                apply ⟇ᵢ₂;
                apply H;
            }
            {
                assume H1;
                apply ⟇ᵢ₁;
                apply H1;
            };
        };
        apply resolutionᵣ _ _ _ (t2_t32' t2_t32) t2_t84;
    };
    refine t2_t32_t2_t84;
};
have t2_t86 : π̇ (((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))
        ⟇ ▩) {
    have t2_t9_t2_t30 : π̇ (((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))
             ⟇ (¬ (((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___)))))
            ⟇ ▩) {
        apply resolutionₗ _ _ _ t2_t9 t2_t30;
    };
    have t2_t9_t2_t30_t2_t85 : π̇ (((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))
            ⟇ ▩) {
        have t2_t9_t2_t30' : (π̇ (((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))
                 ⟇ (¬ (((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___)))))
                ⟇ ▩) → π̇ ((¬ (((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___)))))
                 ⟇ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))
                ⟇ ▩)) {
            assume H2;
            apply ⟇ₑ H2 
            {
                assume H;
                apply ⟇ᵢ₂;
                apply H;
            }
            {
                assume H1;
                apply ⟇ᵢ₁;
                apply H1;
            };
        };
        apply resolutionᵣ _ _ _ (t2_t9_t2_t30' t2_t9_t2_t30) t2_t85;
    };
    refine t2_t9_t2_t30_t2_t85;
};
have t2_t87 : π̇ (p_58 ⟇ ▩) {
    apply ∨ᶜᵢ₁;
    symmetry;
    apply (π̇ₗ t2_t86);
};
have t2_t88 : π̇ (p_24 ⟇ ▩) {
    apply ∨ᶜᵢ₁;
    rewrite (π̇ₗ t2_t7);
    rewrite (π̇ₗ t2_t87);
    reflexivity;
};
apply subproof2 (π̇ₗ t2_a0) (π̇ₗ t2_a1) (π̇ₗ t2_t88);
end;

symbol t3 : π̇ (p_95  ⟇ p_19 ⟇ ▩) ≔ 
begin
apply and_pos;
reflexivity;
end;

symbol t4 : π̇ (p_95  ⟇ p_29 ⟇ ▩) ≔ 
begin
apply and_pos;
reflexivity;
end;

symbol t5 : π̇ (((smt__TLA______FunApp smt__VARIABLE___alloc______prime smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___))
     ⟇ (¬ (((smt__VARIABLE___alloc______prime = (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___))) ∧ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___)))))
     ⟇ (¬ (((smt__VARIABLE___alloc______prime = (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___))) ∧ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___)))))
    ⟇ ▩) ≔ 
begin
have t2_t3 : π̇ ((¬ (((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))))
         ⟇ ((smt__TLA______FunApp smt__VARIABLE___alloc______prime smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___))
         ⟇ (¬ (((smt__VARIABLE___alloc______prime = (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___))) ∧ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___)))))
        ⟇ ▩) {
    have t3' : (π̇ ((¬ (((smt__VARIABLE___alloc______prime = (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___))) ∧ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___)))))
             ⟇ (smt__VARIABLE___alloc______prime = (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)))
            ⟇ ▩) → π̇ ((smt__VARIABLE___alloc______prime = (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)))
             ⟇ (¬ (((smt__VARIABLE___alloc______prime = (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___))) ∧ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___)))))
            ⟇ ▩)) {
        assume H2;
        apply ⟇ₑ H2 
        {
            assume H;
            apply ⟇ᵢ₂;
            apply H;
        }
        {
            assume H1;
            apply ⟇ᵢ₁;
            apply H1;
        };
    };
    apply resolutionᵣ _ _ _ t2 (t3' t3);
};
have t2_t3_t4 : π̇ (((smt__TLA______FunApp smt__VARIABLE___alloc______prime smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___))
         ⟇ (¬ (((smt__VARIABLE___alloc______prime = (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___))) ∧ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___)))))
         ⟇ (¬ (((smt__VARIABLE___alloc______prime = (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___))) ∧ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___)))))
        ⟇ ▩) {
    have t4' : (π̇ ((¬ (((smt__VARIABLE___alloc______prime = (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___))) ∧ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___)))))
             ⟇ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))
            ⟇ ▩) → π̇ (((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))
             ⟇ (¬ (((smt__VARIABLE___alloc______prime = (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___))) ∧ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___)))))
            ⟇ ▩)) {
        assume H2;
        apply ⟇ₑ H2 
        {
            assume H;
            apply ⟇ᵢ₂;
            apply H;
        }
        {
            assume H1;
            apply ⟇ᵢ₁;
            apply H1;
        };
    };
    apply resolutionᵣ _ _ _ t2_t3 (t4' t4);
};
refine t2_t3_t4;
end;

symbol t6 : π̇ (p_95  ⟇ p_95  ⟇ p_24 ⟇ ▩) ≔ 
begin
admit;
end;

symbol t7 : π̇ (p_95  ⟇ p_24 ⟇ ▩) ≔ 
begin
admit;
end;

symbol t13 : π̇ ((¬ ((smt__VARIABLE___alloc______prime = (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)))))
     ⟇ (¬ (((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))))
     ⟇ ((smt__TLA______FunApp smt__VARIABLE___alloc______prime smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___))
    ⟇ ▩) ≔ 
begin
have t0_t7 : π̇ ((¬ ((smt__VARIABLE___alloc______prime = (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)))))
         ⟇ (¬ (((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))))
         ⟇ ((smt__TLA______FunApp smt__VARIABLE___alloc______prime smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___))
        ⟇ ▩) {
    apply resolutionₗ _ _ _ t0 t7;
};
refine t0_t7;
end;

symbol t14 : π̇ (p_92  ⟇ p_24  ⟇ p_93 ⟇ ▩) ≔ 
begin
admit;
end;

symbol t15 : π̇ (p_91  ⟇ p_30  ⟇ p_29 ⟇ ▩) ≔ 
begin
apply or_pos;
reflexivity;
end;

symbol t16 : π̇ (p_30  ⟇ p_29  ⟇ p_91 ⟇ ▩) ≔ 
begin
admit;
end;

symbol t17 : π̇ (p_90  ⟇ p_12  ⟇ p_32 ⟇ ▩) ≔ 
begin
apply equiv_pos1;
end;

symbol t18 : π̇ (p_12  ⟇ p_32  ⟇ p_90 ⟇ ▩) ≔ 
begin
admit;
end;

symbol t19 : π̇ (p_89  ⟇ p_11 ⟇ ▩) ≔ 
begin
apply implies (π̇ₗ a28);
end;

symbol t20 : π̇ (p_11  ⟇ p_89 ⟇ ▩) ≔ 
begin
admit;
end;

symbol t21 : π̇ ((¬ ((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___))) ⟇ ▩) ≔ 
begin
have t20_a29 : π̇ ((¬ ((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___))) ⟇ ▩) {
    apply resolutionₗ _ _ _ t20 a29;
};
refine t20_a29;
end;

symbol t22 : π̇ ((¬ (((((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y)))) ⇒ᶜ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___)))) = (((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y)))) ⇒ᶜ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___clt___ = smt__CONSTANT___c1___)))))))
     ⟇ (¬ ((((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y)))) ⇒ᶜ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___))))))
     ⟇ p_84
    ⟇ ▩) ≔ 
begin
apply equiv_pos2;
end;

symbol t23 : π̇ (((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y))) = (`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y))))
    ⟇ ▩) ≔ 
begin
apply ∨ᶜᵢ₁;
reflexivity;
end;

symbol t24 : π̇ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___))
    ⟇ ▩) ≔ 
begin
apply ∨ᶜᵢ₁;
reflexivity;
end;

symbol t25 : π̇ (((smt__CONSTANT___c1___ = smt__CONSTANT___clt___) = (smt__CONSTANT___clt___ = smt__CONSTANT___c1___))
    ⟇ ▩) ≔ 
begin
apply ∨ᶜᵢ₁;
rewrite eq-symm smt__CONSTANT___c1___ smt__CONSTANT___clt___;
reflexivity;
end;

symbol t26 : π̇ ((((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___)) = ((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___clt___ = smt__CONSTANT___c1___)))
    ⟇ ▩) ≔ 
begin
apply ∨ᶜᵢ₁;
apply (feq2ᶜ (=) (π̇ₗ t24) (π̇ₗ t25));
end;

symbol t27 : π̇ (p_88 ⟇ ▩) ≔ 
begin
apply ∨ᶜᵢ₁;
apply (feq2ᶜ (⇒ᶜ) (π̇ₗ t23) (π̇ₗ t26));
end;

symbol t28 : π̇ (p_87
     ⟇ (`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y)))
    ⟇ ▩) ≔ 
begin
apply implies_neg1;
end;

symbol t29 : π̇ ((¬ ((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y)))))
     ⟇ ((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___))
    ⟇ ▩) ≔ 
begin
have t29_a0 : π̇ ((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y))) ⟇ ▩) {
    admit;
};
have t29_t0 : π̇ (((¬ ((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y))))) ∨ᶜ ((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___)))
        ⟇ ▩) {
    apply ∨ᶜᵢ₁;
    apply imply_to_or;
    apply ⇒ᶜᵢ;
    assume H;
    apply  (∀ᶜₑ smt__CONSTANT___clt___ (∀ᶜₑ smt__CONSTANT___c1___ H));
};
have t29_t1 : π̇ (p_21  ⟇ p_86 ⟇ ▩) {
    admit;
};
have t29_t2 : π̇ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___))
        ⟇ ▩) {
    have t29_t1_t29_a0 : π̇ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___))
            ⟇ ▩) {
        apply resolutionᵣ _ _ _ t29_t1 t29_a0;
    };
    refine t29_t1_t29_a0;
};
apply subproof1 (π̇ₗ t29_a0) (π̇ₗ t29_t2);
end;

symbol t30 : π̇ ((((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y)))) ⇒ᶜ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___))))
     ⟇ ((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___))
    ⟇ ▩) ≔ 
begin
have t28_t29 : π̇ ((((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y)))) ⇒ᶜ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___))))
         ⟇ ((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___))
        ⟇ ▩) {
    have t28' : (π̇ ((((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y)))) ⇒ᶜ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___))))
             ⟇ (`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y)))
            ⟇ ▩) → π̇ ((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y)))
             ⟇ (((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y)))) ⇒ᶜ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___))))
            ⟇ ▩)) {
        assume H2;
        apply ⟇ₑ H2 
        {
            assume H;
            apply ⟇ᵢ₂;
            apply H;
        }
        {
            assume H1;
            apply ⟇ᵢ₁;
            apply H1;
        };
    };
    apply resolutionₗ _ _ _ (t28' t28) t29;
};
refine t28_t29;
end;

symbol t31 : π̇ (p_87
     ⟇ (¬ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___))))
    ⟇ ▩) ≔ 
begin
apply implies_neg2;
end;

symbol t32 : π̇ ((((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y)))) ⇒ᶜ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___))))
     ⟇ (((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y)))) ⇒ᶜ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___))))
    ⟇ ▩) ≔ 
begin
have t30_t31 : π̇ ((((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y)))) ⇒ᶜ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___))))
         ⟇ (((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y)))) ⇒ᶜ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___))))
        ⟇ ▩) {
    have t30' : (π̇ ((((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y)))) ⇒ᶜ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___))))
             ⟇ ((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___))
            ⟇ ▩) → π̇ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___))
             ⟇ (((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y)))) ⇒ᶜ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___))))
            ⟇ ▩)) {
        assume H2;
        apply ⟇ₑ H2 
        {
            assume H;
            apply ⟇ᵢ₂;
            apply H;
        }
        {
            assume H1;
            apply ⟇ᵢ₁;
            apply H1;
        };
    };
    have t31' : (π̇ ((((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y)))) ⇒ᶜ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___))))
             ⟇ (¬ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___))))
            ⟇ ▩) → π̇ ((¬ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___))))
             ⟇ (((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y)))) ⇒ᶜ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___))))
            ⟇ ▩)) {
        assume H2;
        apply ⟇ₑ H2 
        {
            assume H;
            apply ⟇ᵢ₂;
            apply H;
        }
        {
            assume H1;
            apply ⟇ᵢ₁;
            apply H1;
        };
    };
    apply resolutionₗ _ _ _ (t30' t30) (t31' t31);
};
refine t30_t31;
end;

symbol t33 : π̇ (p_87 ⟇ ▩) ≔ 
begin
admit;
end;

symbol t34 : π̇ ((((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y)))) ⇒ᶜ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___clt___ = smt__CONSTANT___c1___))))
    ⟇ ▩) ≔ 
begin
have t22_t27 : π̇ ((¬ ((((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y)))) ⇒ᶜ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___c1___ = smt__CONSTANT___clt___))))))
         ⟇ (((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y)))) ⇒ᶜ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___clt___ = smt__CONSTANT___c1___))))
        ⟇ ▩) {
    apply resolutionᵣ _ _ _ t22 t27;
};
have t22_t27_t33 : π̇ ((((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y)))) ⇒ᶜ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___clt___ = smt__CONSTANT___c1___))))
        ⟇ ▩) {
    apply resolutionᵣ _ _ _ t22_t27 t33;
};
refine t22_t27_t33;
end;

symbol t35 : π̇ (p_21  ⟇ p_83 ⟇ ▩) ≔ 
begin
apply implies (π̇ₗ t34);
end;

symbol t36 : π̇ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___clt___ = smt__CONSTANT___c1___))
    ⟇ ▩) ≔ 
begin
have t35_ExtTrigEqDefIdv : π̇ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___clt___ = smt__CONSTANT___c1___))
        ⟇ ▩) {
    apply resolutionᵣ _ _ _ t35 ExtTrigEqDefIdv;
};
refine t35_ExtTrigEqDefIdv;
end;

symbol t37 : π̇ ((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ⟇ ▩) ≔ 
begin
have t18_t21 : π̇ ((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___)))
         ⟇ (¬ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___clt___ = smt__CONSTANT___c1___))))
        ⟇ ▩) {
    apply resolutionₗ _ _ _ t18 t21;
};
have t18_t21_t36 : π̇ ((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ⟇ ▩) {
    have t18_t21' : (π̇ ((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___)))
             ⟇ (¬ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___clt___ = smt__CONSTANT___c1___))))
            ⟇ ▩) → π̇ ((¬ (((smt__TLA______TrigEq___Idv smt__CONSTANT___c1___ smt__CONSTANT___clt___) = (smt__CONSTANT___clt___ = smt__CONSTANT___c1___))))
             ⟇ (¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___)))
            ⟇ ▩)) {
        assume H2;
        apply ⟇ₑ H2 
        {
            assume H;
            apply ⟇ᵢ₂;
            apply H;
        }
        {
            assume H1;
            apply ⟇ᵢ₁;
            apply H1;
        };
    };
    apply resolutionᵣ _ _ _ (t18_t21' t18_t21) t36;
};
refine t18_t21_t36;
end;

symbol t38 : π̇ (p_82  ⟇ p_31 ⟇ ▩) ≔ 
begin
apply and_pos;
reflexivity;
end;

symbol t39 : π̇ (p_31  ⟇ p_82 ⟇ ▩) ≔ 
begin
admit;
end;

symbol t40 : π̇ (p_81  ⟇ p_37  ⟇ p_34 ⟇ ▩) ≔ 
begin
apply or_pos;
reflexivity;
end;

symbol t41 : π̇ (p_37  ⟇ p_34  ⟇ p_81 ⟇ ▩) ≔ 
begin
admit;
end;

symbol t42 : π̇ ((((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)) = ⊤) = (smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))
    ⟇ ▩) ≔ 
begin
apply ∨ᶜᵢ₁;
try rewrite .[ x in x = _ ] equiv_simplify₁;
try rewrite .[ x in x = _ ] equiv_simplify₂;
try rewrite .[ x in x = _ ] equiv_simplify₃;
try rewrite .[ x in x = _ ] equiv_simplify₄;
try rewrite .[ x in x = _ ] equiv_simplify₅;
try rewrite .[ x in x = _ ] equiv_simplify₆;
try rewrite .[ x in x = _ ] equiv_simplify₇;
try rewrite .[ x in x = _ ] equiv_simplify₈;
reflexivity;
end;

symbol t43 : π̇ ((¬ (((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)) = ⊤)))
     ⟇ p_36
    ⟇ ▩) ≔ 
begin
apply equiv1 t42;
end;

symbol t44 : π̇ ((smt__CONSTANT___c1___ = smt__CONSTANT___c1___) ⟇ ▩) ≔ 
begin
apply ∨ᶜᵢ₁;
reflexivity;
end;

symbol t45 : π̇ (p_80  ⟇ p_66 ⟇ ▩) ≔ 
begin
apply and_pos;
reflexivity;
end;

symbol t46 : π̇ (p_66  ⟇ p_80 ⟇ ▩) ≔ 
begin
admit;
end;

symbol t47 : π̇ (p_79  ⟇ p_68  ⟇ p_67 ⟇ ▩) ≔ 
begin
apply or_pos;
reflexivity;
end;

symbol t48 : π̇ (p_68  ⟇ p_67  ⟇ p_79 ⟇ ▩) ≔ 
begin
admit;
end;

symbol t49 : π̇ (p_6 ⟇ ▩) ≔ 
begin
admit;
end;

symbol t50 : π̇ (p_5 ⟇ ▩) ≔ 
begin
admit;
end;

symbol t51 : π̇ (((¬ ((`∀ᶜ smt__a, `∀ᶜ smt__b, `∀ᶜ smt__f, ((¬ ((smt__TLA______Mem smt__f (smt__TLA______FunSet smt__a smt__b)))) ∨ᶜ ((smt__TLA______FunIsafcn smt__f) ∧ᶜ (smt__a = (smt__TLA______FunDom smt__f))))))) ∨ᶜ ((¬ ((smt__TLA______Mem smt__VARIABLE___alloc___ (smt__TLA______FunSet smt__CONSTANT___Client___ (smt__TLA______Subset smt__CONSTANT___Resource___))))) ∨ᶜ ((smt__TLA______FunIsafcn smt__VARIABLE___alloc___) ∧ᶜ (smt__CONSTANT___Client___ = (smt__TLA______FunDom smt__VARIABLE___alloc___)))))
    ⟇ ▩) ≔ 
begin
apply ∨ᶜᵢ₁;
apply imply_to_or;
apply ⇒ᶜᵢ;
assume H;
apply  (∀ᶜₑ smt__VARIABLE___alloc___ (∀ᶜₑ (smt__TLA______Subset smt__CONSTANT___Resource___) (∀ᶜₑ smt__CONSTANT___Client___ H)));
end;

symbol t52 : π̇ (p_78  ⟇ p_69 ⟇ ▩) ≔ 
begin
admit;
end;

symbol t53 : π̇ ((¬ (((`∀ᶜ smt__a, `∀ᶜ smt__b, `∀ᶜ smt__f, (((smt__TLA______Mem smt__f (smt__TLA______FunSet smt__a smt__b))) ⇒ᶜ (((smt__TLA______FunIsafcn smt__f) ∧ᶜ ((smt__TLA______FunDom smt__f) = smt__a))))) = (`∀ᶜ smt__a, `∀ᶜ smt__b, `∀ᶜ smt__f, ((¬ ((smt__TLA______Mem smt__f (smt__TLA______FunSet smt__a smt__b)))) ∨ᶜ ((smt__TLA______FunIsafcn smt__f) ∧ᶜ (smt__a = (smt__TLA______FunDom smt__f))))))))
     ⟇ (¬ ((`∀ᶜ smt__a, `∀ᶜ smt__b, `∀ᶜ smt__f, (((smt__TLA______Mem smt__f (smt__TLA______FunSet smt__a smt__b))) ⇒ᶜ (((smt__TLA______FunIsafcn smt__f) ∧ᶜ ((smt__TLA______FunDom smt__f) = smt__a)))))))
     ⟇ (`∀ᶜ smt__a, `∀ᶜ smt__b, `∀ᶜ smt__f, ((¬ ((smt__TLA______Mem smt__f (smt__TLA______FunSet smt__a smt__b)))) ∨ᶜ ((smt__TLA______FunIsafcn smt__f) ∧ᶜ (smt__a = (smt__TLA______FunDom smt__f)))))
    ⟇ ▩) ≔ 
begin
apply equiv_pos2;
end;

symbol t54 : π̇ (((`∀ᶜ smt__a, `∀ᶜ smt__b, `∀ᶜ smt__f, (((smt__TLA______Mem smt__f (smt__TLA______FunSet smt__a smt__b))) ⇒ᶜ (((smt__TLA______FunIsafcn smt__f) ∧ᶜ ((smt__TLA______FunDom smt__f) = smt__a))))) = (`∀ᶜ smt__a, `∀ᶜ smt__b, `∀ᶜ smt__f, (((smt__TLA______Mem smt__f (smt__TLA______FunSet smt__a smt__b))) ⇒ᶜ (((smt__TLA______FunIsafcn smt__f) ∧ᶜ (smt__a = (smt__TLA______FunDom smt__f)))))))
    ⟇ ▩) ≔ 
begin
apply ∨ᶜᵢ₁;
apply bind_∀;
assume smt__a;
apply bind_∀;
assume smt__b;
apply bind_∀;
assume smt__f;
have t54_t0 : π̇ (((smt__TLA______Mem smt__f (smt__TLA______FunSet smt__a smt__b)) = (smt__TLA______Mem smt__f (smt__TLA______FunSet smt__a smt__b)))
        ⟇ ▩) {
    apply ∨ᶜᵢ₁;
    reflexivity;
};
have t54_t1 : π̇ (((smt__TLA______FunIsafcn smt__f) = (smt__TLA______FunIsafcn smt__f)) ⟇ ▩) {
    apply ∨ᶜᵢ₁;
    reflexivity;
};
have t54_t2 : π̇ ((((smt__TLA______FunDom smt__f) = smt__a) = (smt__a = (smt__TLA______FunDom smt__f))) ⟇ ▩) {
    apply ∨ᶜᵢ₁;
    rewrite eq-symm (smt__TLA______FunDom smt__f) smt__a;
    reflexivity;
};
have t54_t3 : π̇ ((((smt__TLA______FunIsafcn smt__f) ∧ᶜ ((smt__TLA______FunDom smt__f) = smt__a)) = ((smt__TLA______FunIsafcn smt__f) ∧ᶜ (smt__a = (smt__TLA______FunDom smt__f))))
        ⟇ ▩) {
    apply ∨ᶜᵢ₁;
    rewrite .[ x in x ∧ᶜ _ ] (π̇ₗ t54_t1);
    rewrite .[ x in _ ∧ᶜ x ] (π̇ₗ t54_t2);
    reflexivity;
};
have t54_t4 : π̇ (((((smt__TLA______Mem smt__f (smt__TLA______FunSet smt__a smt__b))) ⇒ᶜ (((smt__TLA______FunIsafcn smt__f) ∧ᶜ ((smt__TLA______FunDom smt__f) = smt__a)))) = (((smt__TLA______Mem smt__f (smt__TLA______FunSet smt__a smt__b))) ⇒ᶜ (((smt__TLA______FunIsafcn smt__f) ∧ᶜ (smt__a = (smt__TLA______FunDom smt__f))))))
        ⟇ ▩) {
    apply ∨ᶜᵢ₁;
    apply (feq2ᶜ (⇒ᶜ) (π̇ₗ t54_t0) (π̇ₗ t54_t3));
};
apply π̇ₗ t54_t4;
end;

symbol t55 : π̇ (((`∀ᶜ smt__a, `∀ᶜ smt__b, `∀ᶜ smt__f, (((smt__TLA______Mem smt__f (smt__TLA______FunSet smt__a smt__b))) ⇒ᶜ (((smt__TLA______FunIsafcn smt__f) ∧ᶜ (smt__a = (smt__TLA______FunDom smt__f)))))) = (`∀ᶜ smt__a, `∀ᶜ smt__b, `∀ᶜ smt__f, ((¬ ((smt__TLA______Mem smt__f (smt__TLA______FunSet smt__a smt__b)))) ∨ᶜ ((smt__TLA______FunIsafcn smt__f) ∧ᶜ (smt__a = (smt__TLA______FunDom smt__f))))))
    ⟇ ▩) ≔ 
begin
admit;
end;

symbol t56 : π̇ (p_70 ⟇ ▩) ≔ 
begin
apply ∨ᶜᵢ₁;
rewrite (π̇ₗ t54);
rewrite (π̇ₗ t55);
reflexivity;
end;

symbol t57 : π̇ ((`∀ᶜ smt__a, `∀ᶜ smt__b, `∀ᶜ smt__f, ((¬ ((smt__TLA______Mem smt__f (smt__TLA______FunSet smt__a smt__b)))) ∨ᶜ ((smt__TLA______FunIsafcn smt__f) ∧ᶜ (smt__a = (smt__TLA______FunDom smt__f)))))
    ⟇ ▩) ≔ 
begin
have t53_t56 : π̇ ((¬ ((`∀ᶜ smt__a, `∀ᶜ smt__b, `∀ᶜ smt__f, (((smt__TLA______Mem smt__f (smt__TLA______FunSet smt__a smt__b))) ⇒ᶜ (((smt__TLA______FunIsafcn smt__f) ∧ᶜ ((smt__TLA______FunDom smt__f) = smt__a)))))))
         ⟇ (`∀ᶜ smt__a, `∀ᶜ smt__b, `∀ᶜ smt__f, ((¬ ((smt__TLA______Mem smt__f (smt__TLA______FunSet smt__a smt__b)))) ∨ᶜ ((smt__TLA______FunIsafcn smt__f) ∧ᶜ (smt__a = (smt__TLA______FunDom smt__f)))))
        ⟇ ▩) {
    apply resolutionᵣ _ _ _ t53 t56;
};
have t53_t56_FunSetElim1 : π̇ ((`∀ᶜ smt__a, `∀ᶜ smt__b, `∀ᶜ smt__f, ((¬ ((smt__TLA______Mem smt__f (smt__TLA______FunSet smt__a smt__b)))) ∨ᶜ ((smt__TLA______FunIsafcn smt__f) ∧ᶜ (smt__a = (smt__TLA______FunDom smt__f)))))
        ⟇ ▩) {
    apply resolutionᵣ _ _ _ t53_t56 FunSetElim1;
};
refine t53_t56_FunSetElim1;
end;

symbol t58 : π̇ (((¬ ((smt__TLA______Mem smt__VARIABLE___alloc___ (smt__TLA______FunSet smt__CONSTANT___Client___ (smt__TLA______Subset smt__CONSTANT___Resource___))))) ∨ᶜ ((smt__TLA______FunIsafcn smt__VARIABLE___alloc___) ∧ᶜ (smt__CONSTANT___Client___ = (smt__TLA______FunDom smt__VARIABLE___alloc___))))
    ⟇ ▩) ≔ 
begin
have t52_t57 : π̇ (((¬ ((smt__TLA______Mem smt__VARIABLE___alloc___ (smt__TLA______FunSet smt__CONSTANT___Client___ (smt__TLA______Subset smt__CONSTANT___Resource___))))) ∨ᶜ ((smt__TLA______FunIsafcn smt__VARIABLE___alloc___) ∧ᶜ (smt__CONSTANT___Client___ = (smt__TLA______FunDom smt__VARIABLE___alloc___))))
        ⟇ ▩) {
    apply resolutionᵣ _ _ _ t52 t57;
};
refine t52_t57;
end;

symbol t59 : π̇ (((smt__TLA______FunIsafcn smt__VARIABLE___alloc___) ∧ᶜ (smt__CONSTANT___Client___ = (smt__TLA______FunDom smt__VARIABLE___alloc___)))
    ⟇ ▩) ≔ 
begin
have t48_t50 : π̇ (((smt__TLA______FunIsafcn smt__VARIABLE___alloc___) ∧ᶜ (smt__CONSTANT___Client___ = (smt__TLA______FunDom smt__VARIABLE___alloc___)))
         ⟇ (¬ (((¬ ((smt__TLA______Mem smt__VARIABLE___alloc___ (smt__TLA______FunSet smt__CONSTANT___Client___ (smt__TLA______Subset smt__CONSTANT___Resource___))))) ∨ᶜ ((smt__TLA______FunIsafcn smt__VARIABLE___alloc___) ∧ᶜ (smt__CONSTANT___Client___ = (smt__TLA______FunDom smt__VARIABLE___alloc___))))))
        ⟇ ▩) {
    apply resolutionᵣ _ _ _ t48 t50;
};
have t48_t50_t58 : π̇ (((smt__TLA______FunIsafcn smt__VARIABLE___alloc___) ∧ᶜ (smt__CONSTANT___Client___ = (smt__TLA______FunDom smt__VARIABLE___alloc___)))
        ⟇ ▩) {
    have t48_t50' : (π̇ (((smt__TLA______FunIsafcn smt__VARIABLE___alloc___) ∧ᶜ (smt__CONSTANT___Client___ = (smt__TLA______FunDom smt__VARIABLE___alloc___)))
             ⟇ (¬ (((¬ ((smt__TLA______Mem smt__VARIABLE___alloc___ (smt__TLA______FunSet smt__CONSTANT___Client___ (smt__TLA______Subset smt__CONSTANT___Resource___))))) ∨ᶜ ((smt__TLA______FunIsafcn smt__VARIABLE___alloc___) ∧ᶜ (smt__CONSTANT___Client___ = (smt__TLA______FunDom smt__VARIABLE___alloc___))))))
            ⟇ ▩) → π̇ ((¬ (((¬ ((smt__TLA______Mem smt__VARIABLE___alloc___ (smt__TLA______FunSet smt__CONSTANT___Client___ (smt__TLA______Subset smt__CONSTANT___Resource___))))) ∨ᶜ ((smt__TLA______FunIsafcn smt__VARIABLE___alloc___) ∧ᶜ (smt__CONSTANT___Client___ = (smt__TLA______FunDom smt__VARIABLE___alloc___))))))
             ⟇ ((smt__TLA______FunIsafcn smt__VARIABLE___alloc___) ∧ᶜ (smt__CONSTANT___Client___ = (smt__TLA______FunDom smt__VARIABLE___alloc___)))
            ⟇ ▩)) {
        assume H2;
        apply ⟇ₑ H2 
        {
            assume H;
            apply ⟇ᵢ₂;
            apply H;
        }
        {
            assume H1;
            apply ⟇ᵢ₁;
            apply H1;
        };
    };
    apply resolutionᵣ _ _ _ (t48_t50' t48_t50) t58;
};
refine t48_t50_t58;
end;

symbol t60 : π̇ ((smt__CONSTANT___Client___ = (smt__TLA______FunDom smt__VARIABLE___alloc___)) ⟇ ▩) ≔ 
begin
have t46_t59 : π̇ ((smt__CONSTANT___Client___ = (smt__TLA______FunDom smt__VARIABLE___alloc___)) ⟇ ▩) {
    have t46' : (π̇ ((smt__CONSTANT___Client___ = (smt__TLA______FunDom smt__VARIABLE___alloc___))
             ⟇ (¬ (((smt__TLA______FunIsafcn smt__VARIABLE___alloc___) ∧ᶜ (smt__CONSTANT___Client___ = (smt__TLA______FunDom smt__VARIABLE___alloc___)))))
            ⟇ ▩) → π̇ ((¬ (((smt__TLA______FunIsafcn smt__VARIABLE___alloc___) ∧ᶜ (smt__CONSTANT___Client___ = (smt__TLA______FunDom smt__VARIABLE___alloc___)))))
             ⟇ (smt__CONSTANT___Client___ = (smt__TLA______FunDom smt__VARIABLE___alloc___))
            ⟇ ▩)) {
        assume H2;
        apply ⟇ₑ H2 
        {
            assume H;
            apply ⟇ᵢ₂;
            apply H;
        }
        {
            assume H1;
            apply ⟇ᵢ₁;
            apply H1;
        };
    };
    apply resolutionᵣ _ _ _ (t46' t46) t59;
};
refine t46_t59;
end;

symbol t61 : π̇ (((smt__TLA______FunDom smt__VARIABLE___alloc___) = smt__CONSTANT___Client___) ⟇ ▩) ≔ 
begin
apply ∨ᶜᵢ₁;
symmetry;
apply (π̇ₗ t60);
end;

symbol t62 : π̇ (((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)) = (smt__TLA______Mem smt__CONSTANT___c1___ smt__CONSTANT___Client___))
    ⟇ ▩) ≔ 
begin
apply ∨ᶜᵢ₁;
apply feq2ᶜ smt__TLA______Mem (π̇ₗ t44) (π̇ₗ t61);
end;

symbol t63 : π̇ ((((smt__TLA______Mem smt__CONSTANT___c1___ smt__CONSTANT___Client___) = ⊤) = (smt__TLA______Mem smt__CONSTANT___c1___ smt__CONSTANT___Client___))
    ⟇ ▩) ≔ 
begin
apply ∨ᶜᵢ₁;
try rewrite .[ x in x = _ ] equiv_simplify₁;
try rewrite .[ x in x = _ ] equiv_simplify₂;
try rewrite .[ x in x = _ ] equiv_simplify₃;
try rewrite .[ x in x = _ ] equiv_simplify₄;
try rewrite .[ x in x = _ ] equiv_simplify₅;
try rewrite .[ x in x = _ ] equiv_simplify₆;
try rewrite .[ x in x = _ ] equiv_simplify₇;
try rewrite .[ x in x = _ ] equiv_simplify₈;
reflexivity;
end;

symbol t64 : π̇ (p_65  ⟇ (¬ ((smt__TLA______Mem smt__CONSTANT___c1___ smt__CONSTANT___Client___))) ⟇ ▩) ≔ 
begin
apply equiv2 t63;
end;

symbol t65 : π̇ (((smt__TLA______Mem smt__CONSTANT___c1___ smt__CONSTANT___Client___) = ⊤) ⟇ ▩) ≔ 
begin
have t64_a22 : π̇ (((smt__TLA______Mem smt__CONSTANT___c1___ smt__CONSTANT___Client___) = ⊤) ⟇ ▩) {
    have t64' : (π̇ (((smt__TLA______Mem smt__CONSTANT___c1___ smt__CONSTANT___Client___) = ⊤)
             ⟇ (¬ ((smt__TLA______Mem smt__CONSTANT___c1___ smt__CONSTANT___Client___)))
            ⟇ ▩) → π̇ ((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ smt__CONSTANT___Client___)))
             ⟇ ((smt__TLA______Mem smt__CONSTANT___c1___ smt__CONSTANT___Client___) = ⊤)
            ⟇ ▩)) {
        assume H2;
        apply ⟇ₑ H2 
        {
            assume H;
            apply ⟇ᵢ₂;
            apply H;
        }
        {
            assume H1;
            apply ⟇ᵢ₁;
            apply H1;
        };
    };
    apply resolutionᵣ _ _ _ (t64' t64) a22;
};
refine t64_a22;
end;

symbol t66 : π̇ (p_64 ⟇ ▩) ≔ 
begin
apply ∨ᶜᵢ₁;
rewrite (π̇ₗ t62);
rewrite (π̇ₗ t65);
reflexivity;
end;

symbol t67 : π̇ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)) ⟇ ▩) ≔ 
begin
have t43_t66 : π̇ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)) ⟇ ▩) {
    apply resolutionᵣ _ _ _ t43 t66;
};
refine t43_t66;
end;

symbol t68 : π̇ ((¬ (((((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))) ⇒ᶜ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___))))))) = (((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))) ⇒ᶜ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))))))))))
     ⟇ (¬ ((((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))) ⇒ᶜ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))))))))
     ⟇ p_57
    ⟇ ▩) ≔ 
begin
apply equiv_pos2;
end;

symbol t69 : π̇ (((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z)))))) = (`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z)))))))
    ⟇ ▩) ≔ 
begin
apply ∨ᶜᵢ₁;
reflexivity;
end;

symbol t70 : π̇ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) = (¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))))
    ⟇ ▩) ≔ 
begin
apply ∨ᶜᵢ₁;
reflexivity;
end;

symbol t71 : π̇ ((((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) = ((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))))
    ⟇ ▩) ≔ 
begin
apply ∨ᶜᵢ₁;
reflexivity;
end;

symbol t72 : π̇ (((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) = (smt__CONSTANT___clt___ = smt__CONSTANT___c1___))
    ⟇ ▩) ≔ 
begin
apply ∨ᶜᵢ₁;
reflexivity;
end;

symbol t73 : π̇ ((((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)) = ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___)))
    ⟇ ▩) ≔ 
begin
apply ∨ᶜᵢ₁;
rewrite eq-symm (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___);
reflexivity;
end;

symbol t74 : π̇ ((((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___))) = ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))))
    ⟇ ▩) ≔ 
begin
apply ∨ᶜᵢ₁;
rewrite .[ x in x ∨ᶜ _ ] (π̇ₗ t72);
rewrite .[ x in _ ∨ᶜ x ] (π̇ₗ t73);
reflexivity;
end;

symbol t75 : π̇ (((((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))) = (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___)))))
    ⟇ ▩) ≔ 
begin
apply ∨ᶜᵢ₁;
rewrite .[ x in x ∧ᶜ _ ] (π̇ₗ t71);
rewrite .[ x in _ ∧ᶜ x ] (π̇ₗ t74);
reflexivity;
end;

symbol t76 : π̇ ((((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___))))) = ((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))))))
    ⟇ ▩) ≔ 
begin
apply ∨ᶜᵢ₁;
rewrite .[ x in x ∨ᶜ _ ] (π̇ₗ t70);
rewrite .[ x in _ ∨ᶜ x ] (π̇ₗ t75);
reflexivity;
end;

symbol t77 : π̇ (p_63 ⟇ ▩) ≔ 
begin
apply ∨ᶜᵢ₁;
apply (feq2ᶜ (⇒ᶜ) (π̇ₗ t69) (π̇ₗ t76));
end;

symbol t78 : π̇ (p_62
     ⟇ (`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))
    ⟇ ▩) ≔ 
begin
apply implies_neg1;
end;

symbol t79 : π̇ ((¬ ((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))))
     ⟇ ((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))))
    ⟇ ▩) ≔ 
begin
have t79_a0 : π̇ ((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))
        ⟇ ▩) {
    admit;
};
have t79_t0 : π̇ (((¬ ((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z)))))))) ∨ᶜ ((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___))))))
        ⟇ ▩) {
    apply ∨ᶜᵢ₁;
    apply imply_to_or;
    apply ⇒ᶜᵢ;
    assume H;
    apply  (∀ᶜₑ smt__CONSTANT___c1___ (∀ᶜₑ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) (∀ᶜₑ smt__CONSTANT___clt___ (∀ᶜₑ smt__VARIABLE___alloc___ H))));
};
have t79_t1 : π̇ (p_56  ⟇ p_61 ⟇ ▩) {
    admit;
};
have t79_t2 : π̇ ((¬ (((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, (((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f))) ⇒ᶜ (((((smt__z = smt__x)) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = smt__y))) ∧ᶜ (((distinct 2 (cons _  smt__z (cons _  smt__x □)))) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z)))))))) = (`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z)))))))))
         ⟇ (¬ ((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, (((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f))) ⇒ᶜ (((((smt__z = smt__x)) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = smt__y))) ∧ᶜ (((distinct 2 (cons _  smt__z (cons _  smt__x □)))) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))))))
         ⟇ (`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))
        ⟇ ▩) {
    apply equiv_pos2;
};
have t79_t3 : π̇ (((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, (((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f))) ⇒ᶜ (((((smt__z = smt__x)) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = smt__y))) ∧ᶜ (((distinct 2 (cons _  smt__z (cons _  smt__x □)))) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z)))))))) = (`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, (((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f))) ⇒ᶜ (((((smt__x = smt__z)) ⇒ᶜ ((smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z)))) ∧ᶜ (((¬ ((smt__x = smt__z)))) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z)))))))))
        ⟇ ▩) {
    apply ∨ᶜᵢ₁;
    apply bind_∀;
    assume smt__f;
    apply bind_∀;
    assume smt__x;
    apply bind_∀;
    assume smt__y;
    apply bind_∀;
    assume smt__z;
    have t79_t3_t0 : π̇ (((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)) = (smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))
            ⟇ ▩) {
        apply ∨ᶜᵢ₁;
        reflexivity;
    };
    have t79_t3_t1 : π̇ (((smt__z = smt__x) = (smt__x = smt__z)) ⟇ ▩) {
        apply ∨ᶜᵢ₁;
        rewrite eq-symm smt__z smt__x;
        reflexivity;
    };
    have t79_t3_t2 : π̇ ((((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = smt__y) = (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z)))
            ⟇ ▩) {
        apply ∨ᶜᵢ₁;
        rewrite eq-symm (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) smt__y;
        reflexivity;
    };
    have t79_t3_t3 : π̇ (((((smt__z = smt__x)) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = smt__y))) = (((smt__x = smt__z)) ⇒ᶜ ((smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z)))))
            ⟇ ▩) {
        apply ∨ᶜᵢ₁;
        apply (feq2ᶜ (⇒ᶜ) (π̇ₗ t79_t3_t1) (π̇ₗ t79_t3_t2));
    };
    have t79_t3_t4 : π̇ (((distinct 2 (cons _  smt__z (cons _  smt__x □))) = (¬ ((smt__z = smt__x)))) ⟇ ▩) {
        apply ∨ᶜᵢ₁;
        rewrite distinct-binary-elim smt__z smt__x;
        reflexivity;
    };
    have t79_t3_t5 : π̇ (((¬ ((smt__z = smt__x))) = (¬ ((smt__x = smt__z)))) ⟇ ▩) {
        apply ∨ᶜᵢ₁;
        apply feqᶜ (¬) (π̇ₗ t79_t3_t1);
    };
    have t79_t3_t6 : π̇ (((distinct 2 (cons _  smt__z (cons _  smt__x □))) = (¬ ((smt__x = smt__z)))) ⟇ ▩) {
        apply ∨ᶜᵢ₁;
        rewrite (π̇ₗ t79_t3_t4);
        rewrite (π̇ₗ t79_t3_t5);
        reflexivity;
    };
    have t79_t3_t7 : π̇ ((((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z)) = ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z)))
            ⟇ ▩) {
        apply ∨ᶜᵢ₁;
        reflexivity;
    };
    have t79_t3_t8 : π̇ (((((distinct 2 (cons _  smt__z (cons _  smt__x □)))) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z)))) = (((¬ ((smt__x = smt__z)))) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z)))))
            ⟇ ▩) {
        apply ∨ᶜᵢ₁;
        apply (feq2ᶜ (⇒ᶜ) (π̇ₗ t79_t3_t6) (π̇ₗ t79_t3_t7));
    };
    have t79_t3_t9 : π̇ ((((((smt__z = smt__x)) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = smt__y))) ∧ᶜ (((distinct 2 (cons _  smt__z (cons _  smt__x □)))) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))) = ((((smt__x = smt__z)) ⇒ᶜ ((smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z)))) ∧ᶜ (((¬ ((smt__x = smt__z)))) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))
            ⟇ ▩) {
        apply ∨ᶜᵢ₁;
        rewrite .[ x in x ∧ᶜ _ ] (π̇ₗ t79_t3_t3);
        rewrite .[ x in _ ∧ᶜ x ] (π̇ₗ t79_t3_t8);
        reflexivity;
    };
    have t79_t3_t10 : π̇ (((((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f))) ⇒ᶜ (((((smt__z = smt__x)) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = smt__y))) ∧ᶜ (((distinct 2 (cons _  smt__z (cons _  smt__x □)))) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))) = (((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f))) ⇒ᶜ (((((smt__x = smt__z)) ⇒ᶜ ((smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z)))) ∧ᶜ (((¬ ((smt__x = smt__z)))) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))))
            ⟇ ▩) {
        apply ∨ᶜᵢ₁;
        apply (feq2ᶜ (⇒ᶜ) (π̇ₗ t79_t3_t0) (π̇ₗ t79_t3_t9));
    };
    apply π̇ₗ t79_t3_t10;
};
have t79_t4 : π̇ (((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, (((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f))) ⇒ᶜ (((((smt__x = smt__z)) ⇒ᶜ ((smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z)))) ∧ᶜ (((¬ ((smt__x = smt__z)))) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z)))))))) = (`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z)))))))
        ⟇ ▩) {
    admit;
};
have t79_t5 : π̇ (p_39 ⟇ ▩) {
    apply ∨ᶜᵢ₁;
    rewrite (π̇ₗ t79_t3);
    rewrite (π̇ₗ t79_t4);
    reflexivity;
};
have t79_t6 : π̇ ((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))
        ⟇ ▩) {
    have t79_t2_t79_t5 : π̇ ((¬ ((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, (((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f))) ⇒ᶜ (((((smt__z = smt__x)) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = smt__y))) ∧ᶜ (((distinct 2 (cons _  smt__z (cons _  smt__x □)))) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))))))
             ⟇ (`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))
            ⟇ ▩) {
        apply resolutionᵣ _ _ _ t79_t2 t79_t5;
    };
    have t79_t2_t79_t5_FunExceptAppDef2 : π̇ ((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))
            ⟇ ▩) {
        apply resolutionᵣ _ _ _ t79_t2_t79_t5 FunExceptAppDef2;
    };
    refine t79_t2_t79_t5_FunExceptAppDef2;
};
have t79_t7 : π̇ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))))
        ⟇ ▩) {
    have t79_t1_t79_t6 : π̇ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))))
            ⟇ ▩) {
        apply resolutionᵣ _ _ _ t79_t1 t79_t6;
    };
    refine t79_t1_t79_t6;
};
apply subproof1 (π̇ₗ t79_a0) (π̇ₗ t79_t7);
end;

symbol t80 : π̇ ((((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))) ⇒ᶜ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))))))
     ⟇ ((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))))
    ⟇ ▩) ≔ 
begin
have t78_t79 : π̇ ((((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))) ⇒ᶜ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))))))
         ⟇ ((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))))
        ⟇ ▩) {
    have t78' : (π̇ ((((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))) ⇒ᶜ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))))))
             ⟇ (`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))
            ⟇ ▩) → π̇ ((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))
             ⟇ (((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))) ⇒ᶜ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))))))
            ⟇ ▩)) {
        assume H2;
        apply ⟇ₑ H2 
        {
            assume H;
            apply ⟇ᵢ₂;
            apply H;
        }
        {
            assume H1;
            apply ⟇ᵢ₁;
            apply H1;
        };
    };
    apply resolutionₗ _ _ _ (t78' t78) t79;
};
refine t78_t79;
end;

symbol t81 : π̇ (p_62
     ⟇ (¬ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))))))
    ⟇ ▩) ≔ 
begin
apply implies_neg2;
end;

symbol t82 : π̇ ((((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))) ⇒ᶜ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))))))
     ⟇ (((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))) ⇒ᶜ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))))))
    ⟇ ▩) ≔ 
begin
have t80_t81 : π̇ ((((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))) ⇒ᶜ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))))))
         ⟇ (((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))) ⇒ᶜ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))))))
        ⟇ ▩) {
    have t80' : (π̇ ((((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))) ⇒ᶜ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))))))
             ⟇ ((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))))
            ⟇ ▩) → π̇ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))))
             ⟇ (((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))) ⇒ᶜ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))))))
            ⟇ ▩)) {
        assume H2;
        apply ⟇ₑ H2 
        {
            assume H;
            apply ⟇ᵢ₂;
            apply H;
        }
        {
            assume H1;
            apply ⟇ᵢ₁;
            apply H1;
        };
    };
    have t81' : (π̇ ((((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))) ⇒ᶜ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))))))
             ⟇ (¬ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))))))
            ⟇ ▩) → π̇ ((¬ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))))))
             ⟇ (((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))) ⇒ᶜ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))))))
            ⟇ ▩)) {
        assume H2;
        apply ⟇ₑ H2 
        {
            assume H;
            apply ⟇ᵢ₂;
            apply H;
        }
        {
            assume H1;
            apply ⟇ᵢ₁;
            apply H1;
        };
    };
    apply resolutionₗ _ _ _ (t80' t80) (t81' t81);
};
refine t80_t81;
end;

symbol t83 : π̇ (p_62 ⟇ ▩) ≔ 
begin
admit;
end;

symbol t84 : π̇ ((((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))) ⇒ᶜ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___)))))))
    ⟇ ▩) ≔ 
begin
have t68_t77 : π̇ ((¬ ((((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))) ⇒ᶜ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))))))))
         ⟇ (((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))) ⇒ᶜ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___)))))))
        ⟇ ▩) {
    apply resolutionᵣ _ _ _ t68 t77;
};
have t68_t77_t83 : π̇ ((((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))) ⇒ᶜ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___)))))))
        ⟇ ▩) {
    apply resolutionᵣ _ _ _ t68_t77 t83;
};
refine t68_t77_t83;
end;

symbol t85 : π̇ (p_56  ⟇ p_38 ⟇ ▩) ≔ 
begin
apply implies (π̇ₗ t84);
end;

symbol t86 : π̇ ((¬ (((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, (((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f))) ⇒ᶜ (((((smt__z = smt__x)) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = smt__y))) ∧ᶜ (((distinct 2 (cons _  smt__z (cons _  smt__x □)))) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z)))))))) = (`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z)))))))))
     ⟇ (¬ ((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, (((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f))) ⇒ᶜ (((((smt__z = smt__x)) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = smt__y))) ∧ᶜ (((distinct 2 (cons _  smt__z (cons _  smt__x □)))) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))))))
     ⟇ (`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))
    ⟇ ▩) ≔ 
begin
apply equiv_pos2;
end;

symbol t87 : π̇ (((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, (((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f))) ⇒ᶜ (((((smt__z = smt__x)) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = smt__y))) ∧ᶜ (((distinct 2 (cons _  smt__z (cons _  smt__x □)))) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z)))))))) = (`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, (((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f))) ⇒ᶜ (((((smt__x = smt__z)) ⇒ᶜ ((smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z)))) ∧ᶜ (((¬ ((smt__x = smt__z)))) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z)))))))))
    ⟇ ▩) ≔ 
begin
apply ∨ᶜᵢ₁;
apply bind_∀;
assume smt__f;
apply bind_∀;
assume smt__x;
apply bind_∀;
assume smt__y;
apply bind_∀;
assume smt__z;
have t87_t0 : π̇ (((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)) = (smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))
        ⟇ ▩) {
    apply ∨ᶜᵢ₁;
    reflexivity;
};
have t87_t1 : π̇ (((smt__z = smt__x) = (smt__x = smt__z)) ⟇ ▩) {
    apply ∨ᶜᵢ₁;
    rewrite eq-symm smt__z smt__x;
    reflexivity;
};
have t87_t2 : π̇ ((((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = smt__y) = (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z)))
        ⟇ ▩) {
    apply ∨ᶜᵢ₁;
    rewrite eq-symm (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) smt__y;
    reflexivity;
};
have t87_t3 : π̇ (((((smt__z = smt__x)) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = smt__y))) = (((smt__x = smt__z)) ⇒ᶜ ((smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z)))))
        ⟇ ▩) {
    apply ∨ᶜᵢ₁;
    apply (feq2ᶜ (⇒ᶜ) (π̇ₗ t87_t1) (π̇ₗ t87_t2));
};
have t87_t4 : π̇ (((distinct 2 (cons _  smt__z (cons _  smt__x □))) = (¬ ((smt__z = smt__x)))) ⟇ ▩) {
    apply ∨ᶜᵢ₁;
    rewrite distinct-binary-elim smt__z smt__x;
    reflexivity;
};
have t87_t5 : π̇ (((¬ ((smt__z = smt__x))) = (¬ ((smt__x = smt__z)))) ⟇ ▩) {
    apply ∨ᶜᵢ₁;
    apply feqᶜ (¬) (π̇ₗ t87_t1);
};
have t87_t6 : π̇ (((distinct 2 (cons _  smt__z (cons _  smt__x □))) = (¬ ((smt__x = smt__z)))) ⟇ ▩) {
    apply ∨ᶜᵢ₁;
    rewrite (π̇ₗ t87_t4);
    rewrite (π̇ₗ t87_t5);
    reflexivity;
};
have t87_t7 : π̇ ((((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z)) = ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z)))
        ⟇ ▩) {
    apply ∨ᶜᵢ₁;
    reflexivity;
};
have t87_t8 : π̇ (((((distinct 2 (cons _  smt__z (cons _  smt__x □)))) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z)))) = (((¬ ((smt__x = smt__z)))) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z)))))
        ⟇ ▩) {
    apply ∨ᶜᵢ₁;
    apply (feq2ᶜ (⇒ᶜ) (π̇ₗ t87_t6) (π̇ₗ t87_t7));
};
have t87_t9 : π̇ ((((((smt__z = smt__x)) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = smt__y))) ∧ᶜ (((distinct 2 (cons _  smt__z (cons _  smt__x □)))) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))) = ((((smt__x = smt__z)) ⇒ᶜ ((smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z)))) ∧ᶜ (((¬ ((smt__x = smt__z)))) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))
        ⟇ ▩) {
    apply ∨ᶜᵢ₁;
    rewrite .[ x in x ∧ᶜ _ ] (π̇ₗ t87_t3);
    rewrite .[ x in _ ∧ᶜ x ] (π̇ₗ t87_t8);
    reflexivity;
};
have t87_t10 : π̇ (((((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f))) ⇒ᶜ (((((smt__z = smt__x)) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = smt__y))) ∧ᶜ (((distinct 2 (cons _  smt__z (cons _  smt__x □)))) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))) = (((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f))) ⇒ᶜ (((((smt__x = smt__z)) ⇒ᶜ ((smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z)))) ∧ᶜ (((¬ ((smt__x = smt__z)))) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))))
        ⟇ ▩) {
    apply ∨ᶜᵢ₁;
    apply (feq2ᶜ (⇒ᶜ) (π̇ₗ t87_t0) (π̇ₗ t87_t9));
};
apply π̇ₗ t87_t10;
end;

symbol t88 : π̇ (((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, (((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f))) ⇒ᶜ (((((smt__x = smt__z)) ⇒ᶜ ((smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z)))) ∧ᶜ (((¬ ((smt__x = smt__z)))) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z)))))))) = (`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z)))))))
    ⟇ ▩) ≔ 
begin
admit;
end;

symbol t89 : π̇ (p_39 ⟇ ▩) ≔ 
begin
apply ∨ᶜᵢ₁;
rewrite (π̇ₗ t87);
rewrite (π̇ₗ t88);
reflexivity;
end;

symbol t90 : π̇ ((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))
    ⟇ ▩) ≔ 
begin
have t86_t89 : π̇ ((¬ ((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, (((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f))) ⇒ᶜ (((((smt__z = smt__x)) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = smt__y))) ∧ᶜ (((distinct 2 (cons _  smt__z (cons _  smt__x □)))) ⇒ᶜ (((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))))))
         ⟇ (`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))
        ⟇ ▩) {
    apply resolutionᵣ _ _ _ t86 t89;
};
have t86_t89_FunExceptAppDef2 : π̇ ((`∀ᶜ smt__f, `∀ᶜ smt__x, `∀ᶜ smt__y, `∀ᶜ smt__z, ((¬ ((smt__TLA______Mem smt__z (smt__TLA______FunDom smt__f)))) ∨ᶜ (((¬ ((smt__x = smt__z))) ∨ᶜ (smt__y = (smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z))) ∧ᶜ ((smt__x = smt__z) ∨ᶜ ((smt__TLA______FunApp (smt__TLA______FunExcept smt__f smt__x smt__y) smt__z) = (smt__TLA______FunApp smt__f smt__z))))))
        ⟇ ▩) {
    apply resolutionᵣ _ _ _ t86_t89 FunExceptAppDef2;
};
refine t86_t89_FunExceptAppDef2;
end;

symbol t91 : π̇ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___)))))
    ⟇ ▩) ≔ 
begin
have t85_t90 : π̇ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___)))))
        ⟇ ▩) {
    apply resolutionᵣ _ _ _ t85 t90;
};
refine t85_t90;
end;

symbol t92 : π̇ ((((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))))
    ⟇ ▩) ≔ 
begin
have t41_t67 : π̇ ((((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))))
         ⟇ (¬ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___)))))))
        ⟇ ▩) {
    apply resolutionᵣ _ _ _ t41 t67;
};
have t41_t67_t91 : π̇ ((((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))))
        ⟇ ▩) {
    have t41_t67' : (π̇ ((((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))))
             ⟇ (¬ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___)))))))
            ⟇ ▩) → π̇ ((¬ (((¬ ((smt__TLA______Mem smt__CONSTANT___c1___ (smt__TLA______FunDom smt__VARIABLE___alloc___)))) ∨ᶜ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___)))))))
             ⟇ (((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))))
            ⟇ ▩)) {
        assume H2;
        apply ⟇ₑ H2 
        {
            assume H;
            apply ⟇ᵢ₂;
            apply H;
        }
        {
            assume H1;
            apply ⟇ᵢ₁;
            apply H1;
        };
    };
    apply resolutionᵣ _ _ _ (t41_t67' t41_t67) t91;
};
refine t41_t67_t91;
end;

symbol t93 : π̇ (((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___)))
    ⟇ ▩) ≔ 
begin
have t39_t92 : π̇ (((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___)))
        ⟇ ▩) {
    have t39' : (π̇ (((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___)))
             ⟇ (¬ ((((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))))))
            ⟇ ▩) → π̇ ((¬ ((((¬ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___))) ∨ᶜ ((smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))) ∧ᶜ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))))))
             ⟇ ((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___)))
            ⟇ ▩)) {
        assume H2;
        apply ⟇ₑ H2 
        {
            assume H;
            apply ⟇ᵢ₂;
            apply H;
        }
        {
            assume H1;
            apply ⟇ᵢ₁;
            apply H1;
        };
    };
    apply resolutionᵣ _ _ _ (t39' t39) t92;
};
refine t39_t92;
end;

symbol t94 : π̇ (((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))
    ⟇ ▩) ≔ 
begin
have t16_t37 : π̇ (((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))
         ⟇ (¬ (((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___)))))
        ⟇ ▩) {
    apply resolutionₗ _ _ _ t16 t37;
};
have t16_t37_t93 : π̇ (((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))
        ⟇ ▩) {
    have t16_t37' : (π̇ (((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))
             ⟇ (¬ (((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___)))))
            ⟇ ▩) → π̇ ((¬ (((smt__CONSTANT___clt___ = smt__CONSTANT___c1___) ∨ᶜ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___)))))
             ⟇ ((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))
            ⟇ ▩)) {
        assume H2;
        apply ⟇ₑ H2 
        {
            assume H;
            apply ⟇ᵢ₂;
            apply H;
        }
        {
            assume H1;
            apply ⟇ᵢ₁;
            apply H1;
        };
    };
    apply resolutionᵣ _ _ _ (t16_t37' t16_t37) t93;
};
refine t16_t37_t93;
end;

symbol t95 : π̇ (p_27  ⟇ p_17  ⟇ p_25 ⟇ ▩) ≔ 
begin
apply equiv_pos1;
end;

symbol t96 : π̇ (p_17  ⟇ p_25  ⟇ p_27 ⟇ ▩) ≔ 
begin
admit;
end;

symbol t97 : π̇ (((¬ ((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y))))) ∨ᶜ ((smt__TLA______TrigEq___Idv (smt__TLA______FunApp smt__VARIABLE___alloc______prime smt__CONSTANT___c1___) (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)) = ((smt__TLA______FunApp smt__VARIABLE___alloc______prime smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___))))
    ⟇ ▩) ≔ 
begin
apply ∨ᶜᵢ₁;
apply imply_to_or;
apply ⇒ᶜᵢ;
assume H;
apply  (∀ᶜₑ (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) (∀ᶜₑ (smt__TLA______FunApp smt__VARIABLE___alloc______prime smt__CONSTANT___c1___) H));
end;

symbol t98 : π̇ (p_21  ⟇ p_26 ⟇ ▩) ≔ 
begin
admit;
end;

symbol t99 : π̇ (((smt__TLA______TrigEq___Idv (smt__TLA______FunApp smt__VARIABLE___alloc______prime smt__CONSTANT___c1___) (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)) = ((smt__TLA______FunApp smt__VARIABLE___alloc______prime smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))
    ⟇ ▩) ≔ 
begin
have t98_ExtTrigEqDefIdv : π̇ (((smt__TLA______TrigEq___Idv (smt__TLA______FunApp smt__VARIABLE___alloc______prime smt__CONSTANT___c1___) (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)) = ((smt__TLA______FunApp smt__VARIABLE___alloc______prime smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))
        ⟇ ▩) {
    apply resolutionᵣ _ _ _ t98 ExtTrigEqDefIdv;
};
refine t98_ExtTrigEqDefIdv;
end;

symbol t100 : π̇ ((¬ (((smt__TLA______FunApp smt__VARIABLE___alloc______prime smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___))))
    ⟇ ▩) ≔ 
begin
have t96_Goal : π̇ ((¬ (((smt__TLA______FunApp smt__VARIABLE___alloc______prime smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___))))
         ⟇ (¬ (((smt__TLA______TrigEq___Idv (smt__TLA______FunApp smt__VARIABLE___alloc______prime smt__CONSTANT___c1___) (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)) = ((smt__TLA______FunApp smt__VARIABLE___alloc______prime smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))))
        ⟇ ▩) {
    apply resolutionₗ _ _ _ t96 Goal;
};
have t96_Goal_t99 : π̇ ((¬ (((smt__TLA______FunApp smt__VARIABLE___alloc______prime smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___))))
        ⟇ ▩) {
    have t96_Goal' : (π̇ ((¬ (((smt__TLA______FunApp smt__VARIABLE___alloc______prime smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___))))
             ⟇ (¬ (((smt__TLA______TrigEq___Idv (smt__TLA______FunApp smt__VARIABLE___alloc______prime smt__CONSTANT___c1___) (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)) = ((smt__TLA______FunApp smt__VARIABLE___alloc______prime smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))))
            ⟇ ▩) → π̇ ((¬ (((smt__TLA______TrigEq___Idv (smt__TLA______FunApp smt__VARIABLE___alloc______prime smt__CONSTANT___c1___) (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)) = ((smt__TLA______FunApp smt__VARIABLE___alloc______prime smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___)))))
             ⟇ (¬ (((smt__TLA______FunApp smt__VARIABLE___alloc______prime smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___))))
            ⟇ ▩)) {
        assume H2;
        apply ⟇ₑ H2 
        {
            assume H;
            apply ⟇ᵢ₂;
            apply H;
        }
        {
            assume H1;
            apply ⟇ᵢ₁;
            apply H1;
        };
    };
    apply resolutionᵣ _ _ _ (t96_Goal' t96_Goal) t99;
};
refine t96_Goal_t99;
end;

symbol t101 : π̇ (p_23  ⟇ p_22  ⟇ p_19 ⟇ ▩) ≔ 
begin
apply equiv_pos2;
end;

symbol t102 : π̇ (p_22  ⟇ p_19  ⟇ p_23 ⟇ ▩) ≔ 
begin
admit;
end;

symbol t103 : π̇ (((¬ ((`∀ᶜ smt__x, `∀ᶜ smt__y, ((smt__TLA______TrigEq___Idv smt__x smt__y) = (smt__x = smt__y))))) ∨ᶜ ((smt__TLA______TrigEq___Idv smt__VARIABLE___alloc______prime (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___))) = (smt__VARIABLE___alloc______prime = (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)))))
    ⟇ ▩) ≔ 
begin
apply ∨ᶜᵢ₁;
apply imply_to_or;
apply ⇒ᶜᵢ;
assume H;
apply  (∀ᶜₑ (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) (∀ᶜₑ smt__VARIABLE___alloc______prime H));
end;

symbol t104 : π̇ (p_21  ⟇ p_20 ⟇ ▩) ≔ 
begin
admit;
end;

symbol t105 : π̇ (((smt__TLA______TrigEq___Idv smt__VARIABLE___alloc______prime (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___))) = (smt__VARIABLE___alloc______prime = (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___))))
    ⟇ ▩) ≔ 
begin
have t104_ExtTrigEqDefIdv : π̇ (((smt__TLA______TrigEq___Idv smt__VARIABLE___alloc______prime (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___))) = (smt__VARIABLE___alloc______prime = (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___))))
        ⟇ ▩) {
    apply resolutionᵣ _ _ _ t104 ExtTrigEqDefIdv;
};
refine t104_ExtTrigEqDefIdv;
end;

symbol t106 : π̇ ((smt__VARIABLE___alloc______prime = (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)))
    ⟇ ▩) ≔ 
begin
have t102_a26 : π̇ ((smt__VARIABLE___alloc______prime = (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)))
         ⟇ (¬ (((smt__TLA______TrigEq___Idv smt__VARIABLE___alloc______prime (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___))) = (smt__VARIABLE___alloc______prime = (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___))))))
        ⟇ ▩) {
    apply resolutionᵣ _ _ _ t102 a26;
};
have t102_a26_t105 : π̇ ((smt__VARIABLE___alloc______prime = (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)))
        ⟇ ▩) {
    have t102_a26' : (π̇ ((smt__VARIABLE___alloc______prime = (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)))
             ⟇ (¬ (((smt__TLA______TrigEq___Idv smt__VARIABLE___alloc______prime (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___))) = (smt__VARIABLE___alloc______prime = (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___))))))
            ⟇ ▩) → π̇ ((¬ (((smt__TLA______TrigEq___Idv smt__VARIABLE___alloc______prime (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___))) = (smt__VARIABLE___alloc______prime = (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___))))))
             ⟇ (smt__VARIABLE___alloc______prime = (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)))
            ⟇ ▩)) {
        assume H2;
        apply ⟇ₑ H2 
        {
            assume H;
            apply ⟇ᵢ₂;
            apply H;
        }
        {
            assume H1;
            apply ⟇ᵢ₁;
            apply H1;
        };
    };
    apply resolutionᵣ _ _ _ (t102_a26' t102_a26) t105;
};
refine t102_a26_t105;
end;

symbol t107 : π̇ ▩ ≔ 
begin
have t14_t94 : π̇ ((¬ ((smt__VARIABLE___alloc______prime = (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)))))
         ⟇ ((smt__TLA______FunApp smt__VARIABLE___alloc______prime smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___))
        ⟇ ▩) {
    have t14' : (π̇ ((¬ ((smt__VARIABLE___alloc______prime = (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)))))
             ⟇ ((smt__TLA______FunApp smt__VARIABLE___alloc______prime smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___))
             ⟇ (¬ (((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))))
            ⟇ ▩) → π̇ ((¬ (((smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___) = (smt__TLA______FunApp (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)) smt__CONSTANT___c1___))))
             ⟇ (¬ ((smt__VARIABLE___alloc______prime = (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)))))
             ⟇ ((smt__TLA______FunApp smt__VARIABLE___alloc______prime smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___))
            ⟇ ▩)) {
        assume H3;
        apply ⟇ₑ H3 
        {
            assume H;
            apply ⟇ᵢ₂;
            apply ⟇ᵢ₁;
            apply H;
        }
        {
            assume H2;
            apply ⟇ₑ H2 
            {
                assume H;
                apply ⟇ᵢ₂;
                apply ⟇ᵢ₂;
                apply H;
            }
            {
                assume H1;
                apply ⟇ᵢ₁;
                apply H1;
            };
        };
    };
    apply resolutionᵣ _ _ _ (t14' t14) t94;
};
have t14_t94_t100 : π̇ ((¬ ((smt__VARIABLE___alloc______prime = (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)))))
        ⟇ ▩) {
    have t14_t94' : (π̇ ((¬ ((smt__VARIABLE___alloc______prime = (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)))))
             ⟇ ((smt__TLA______FunApp smt__VARIABLE___alloc______prime smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___))
            ⟇ ▩) → π̇ (((smt__TLA______FunApp smt__VARIABLE___alloc______prime smt__CONSTANT___c1___) = (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___c1___))
             ⟇ (¬ ((smt__VARIABLE___alloc______prime = (smt__TLA______FunExcept smt__VARIABLE___alloc___ smt__CONSTANT___clt___ (smt__TLA______Cup (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__CONSTANT___clt___) smt__CONSTANT___S___)))))
            ⟇ ▩)) {
        assume H2;
        apply ⟇ₑ H2 
        {
            assume H;
            apply ⟇ᵢ₂;
            apply H;
        }
        {
            assume H1;
            apply ⟇ᵢ₁;
            apply H1;
        };
    };
    apply resolutionₗ _ _ _ (t14_t94' t14_t94) t100;
};
have t14_t94_t100_t106 : π̇ ▩ {
    apply resolutionᵣ _ _ _ t14_t94_t100 t106;
};
refine t14_t94_t100_t106;
end;