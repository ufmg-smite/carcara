require open Stdlib.Prop;
require open Stdlib.FOL;
require open Stdlib.Eq;
require open Stdlib.Nat;
require Stdlib.Bool;
require open Stdlib.Set;

require open lambdapi.Classic;
require open lambdapi.Alethe;
require open Stdlib.List;

inductive prop: TYPE ≔
|pTrue: prop
| pFalse: prop
| pAnd: prop → prop → prop
| pOr: prop → prop → prop
| pImpl: prop → prop → prop
;

symbol propS: Set;

rule τ propS ↪ prop;

print prop;

symbol ind_propᶜ : Π p0: (prop → Prop), 
    πᶜ (p0 pTrue) → 
    πᶜ (p0 pFalse) →
    (Π x0: prop, πᶜ (p0 x0) → Π x1: prop, πᶜ (p0 x1) → πᶜ (p0 (pAnd x0 x1)))
    → (Π x0: prop, πᶜ (p0 x0) → Π x1: prop, πᶜ (p0 x1) → πᶜ (p0 (pOr x0 x1)))
    → (Π x0: prop, πᶜ (p0 x0) → Π x1: prop, πᶜ (p0 x1) → πᶜ (p0 (pImpl x0 x1)))
    → Π x: prop, πᶜ (p0 x);


symbol o: Set;
rule τ o ↪ Prop;

symbol not_found: Prop; // Just a simple opaque definition to represent an error message.

// A denotation function converts our syntax into a semantic value
// The σ is the context which contains the mapping from variables to Props.
symbol propD (σ: 𝕃 o) (p: prop): Prop;
rule propD _ pTrue ↪ ⊤
with propD _ pFalse ↪ ⊥
with propD $ctx (pAnd $x $y) ↪  (propD $ctx $x) ∧ᶜ (propD $ctx $y)
with propD $ctx (pOr $x $y) ↪  (propD $ctx $x) ∨ᶜ (propD $ctx $y)
with propD $ctx (pImpl $x $y) ↪  (propD $ctx $x) ⇒ᶜ (propD $ctx $y)
;

open Stdlib.Bool;

symbol prop_eq (l r: prop): τ bool;
rule prop_eq pTrue pTrue ↪ true
with prop_eq pTrue pFalse ↪ false
with prop_eq pTrue (pAnd _ _) ↪ false
with prop_eq pTrue (pOr _ _) ↪ false
with prop_eq pTrue (pImpl _ _) ↪ false
//with prop_eq pTrue (pOther _) ↪ false

with prop_eq pFalse pFalse ↪ true
with prop_eq pFalse pTrue ↪ false
with prop_eq pFalse (pAnd _ _) ↪ false
with prop_eq pFalse (pOr _ _) ↪ false
with prop_eq pFalse (pImpl _ _) ↪ false
//with prop_eq pFalse (pOther _) ↪ false

with prop_eq (pAnd $a $b) (pAnd $c $d) ↪ (prop_eq $a $c) and (prop_eq $b $d)
with prop_eq (pAnd _ _) pFalse ↪ false
with prop_eq (pAnd _ _) pTrue ↪ false
with prop_eq (pAnd _ _) (pOr _ _) ↪ false
with prop_eq (pAnd _ _) (pImpl _ _) ↪ false
//with prop_eq (pAnd _ _) (pOther _) ↪ false

with prop_eq (pOr $a $b) (pOr $c $d) ↪ (prop_eq $a $c) and (prop_eq $b $d)
with prop_eq (pOr _ _) pFalse ↪ false
with prop_eq (pOr _ _) pTrue ↪ false
with prop_eq (pOr _ _) (pAnd _ _) ↪ false
with prop_eq (pOr _ _) (pImpl _ _) ↪ false
//with prop_eq (pOr _ _) (pOther _) ↪ false

with prop_eq (pImpl $a $b) (pImpl $c $d) ↪ (prop_eq $a $c) and (prop_eq $b $d)
with prop_eq (pImpl _ _) pFalse ↪ false
with prop_eq (pImpl _ _) pTrue ↪ false
with prop_eq (pImpl _ _) (pAnd _ _) ↪ false
with prop_eq (pImpl _ _) (pOr _ _) ↪ false
with prop_eq (pImpl _ _) (pImpl _ _) ↪ false
//with prop_eq (pImpl _ _) (pOther _) ↪ false


// with prop_eq (pOther $i) (pOther $j) ↪ (eqn $i $j)
// with prop_eq (pOther $i) pFalse ↪ false
// with prop_eq (pOther $i) pTrue ↪ false
// with prop_eq (pOther $i) (pAnd _ _) ↪ false
// with prop_eq (pOther $i) (pOr _ _) ↪ false
// with prop_eq (pOther $i) (pImpl _ _) ↪ false
// with prop_eq (pOther $i) (pOther _) ↪ false
;

symbol knows (p: prop) (c: 𝕃 propS): 𝔹 ≔ ∈ prop_eq p c;

sequential symbol learn (p: prop) (c: 𝕃 propS) : 𝕃 propS;
rule learn pTrue $c ↪ $c
with learn pFalse $c ↪ pFalse ⸬ □
with learn (pAnd $l $r) $c ↪ learn $l (learn $r $c)
with learn $p $c ↪ $p ⸬ $c; //HACK: for simplicity

symbol provable (goal: prop) (known: 𝕃 propS) : 𝔹;
rule provable pTrue _ ↪ true
with provable pFalse $known ↪ knows pFalse $known
with provable (pAnd $l $r) $known ↪ (provable $l $known) and (provable $r $known)
with provable (pOr $l $r) $known ↪ (provable $l $known) or (provable $r $known)
with provable (pImpl $l $r) $known ↪ provable $r (learn $l $known)
;

symbol foldr [a b: Set] : (τ a → τ b → τ b) → τ b → 𝕃 a → τ b;
rule foldr $f $z □ ↪ $z
with foldr $f $z ($x ⸬ $xs) ↪ $f $x (foldr $f $z $xs);

symbol All: 𝕃 propS → prop ≔ foldr (pAnd) pTrue;

symbol I: π ⊤;

symbol prop_eq_sound [p q] : πᶜ (prop_eq p q) → πᶜ (p = q);

opaque symbol learn_sound (ctx: 𝕃 o) (p: prop) (c: 𝕃 propS): πᶜ (propD ctx (All c)) → πᶜ ( propD ctx p) → πᶜ ( propD ctx (All (learn p c)))
≔ begin
    admit
end;

print 𝕃;

symbol ind_𝕃ᶜ : Π a0: Set, Π p0: (𝕃 a0 → Prop), πᶜ (p0 □) → (Π x0: τ a0, Π x1: 𝕃 a0, πᶜ (p0 x1) → πᶜ (p0 (x0 ⸬ x1))) → Π x: 𝕃 a0, πᶜ (p0 x);

symbol ∧ᶜ_istrue [p q : 𝔹] : πᶜ(p and q) → πᶜ(p ∧ᶜ q);

symbol ∨ᶜ_istrue [p q : 𝔹] : πᶜ(p or q) → πᶜ(p ∨ᶜ q);


opaque symbol knows_sound2 (σ: 𝕃 o) (c: 𝕃 propS) : πᶜ (`∀ᶜ p, (knows p c) ⇒ᶜ propD σ (All c) ⇒ᶜ propD σ p) ≔
begin 
    assume σ;
    refine ind_𝕃ᶜ propS (λ u, `∀ᶜ p, istrue (∈ prop_eq p u) ⇒ᶜ (propD σ (All u) ⇒ᶜ propD σ p)) _ _
    {
        apply ∀ᶜᵢ; assume p;
        simplify;
        apply ⇒ᶜᵢ;
        assume contra;
        apply ⊥ᶜₑ contra
    }
    {
        assume h tl IH; 
        apply ∀ᶜᵢ; assume p;
        simplify;
        apply ⇒ᶜᵢ;
        assume H;
        have g: πᶜ ((prop_eq p h) ∨ᶜ (∈ prop_eq p tl)) {
            refine ∨ᶜ_istrue H
        };
        apply ∨ᶜₑ g
        {
            assume H2; apply ⇒ᶜᵢ; assume H3;
            have p=h: πᶜ (p = h) { refine prop_eq_sound H2 };
            rewrite p=h;
            apply ∧ᶜₑ₁ H3
        }
        {
            assume H2; apply ⇒ᶜᵢ; assume H3;
            refine ⇒ᶜₑ (⇒ᶜₑ (@∀ᶜₑ propS _ p IH) H2) (∧ᶜₑ₂ H3);
        }
    }
end;

opaque symbol knows_sound (σ: 𝕃 o) (c: 𝕃 propS) (p: prop) : πᶜ ((knows p c)) → πᶜ (propD σ (All c))  → πᶜ (propD σ p) ≔
begin 
    assume σ ctx p H1 H2;
    refine ⇒ᶜₑ (⇒ᶜₑ (∀ᶜₑ p (@knows_sound2 σ ctx)) H1) H2;
end;


opaque symbol provable_sound: Π (goal: prop), πᶜ (`∀ᶜ ( hyps: 𝕃 propS),
    (provable goal hyps) ⇒ᶜ
    (`∀ᶜ  (ctx: 𝕃 o),  (propD ctx (All hyps)) ⇒ᶜ
     propD ctx goal)) ≔
begin
    refine ind_propᶜ (λ u, `∀ᶜ hyps, (provable u hyps) ⇒ᶜ (`∀ᶜ ctx, propD ctx (All hyps) ⇒ᶜ propD ctx u))
    _ _ _ _ _
    {
        apply ∀ᶜᵢ; assume ctx; apply ⇒ᶜᵢ;  assume H; apply ∀ᶜᵢ; assume σ;  apply ⇒ᶜᵢ;  assume H2;
        apply trivial
    }
    {
        apply ∀ᶜᵢ; assume ctx; apply ⇒ᶜᵢ;  assume H; apply ∀ᶜᵢ; assume σ;  apply ⇒ᶜᵢ;  assume H2;
        apply (knows_sound σ ctx pFalse H);
        refine H2
    }
    {
        assume a IHa; assume b IHb;
        apply ∀ᶜᵢ; assume ctx; apply ⇒ᶜᵢ;  assume H; apply ∀ᶜᵢ; assume σ;  apply ⇒ᶜᵢ;  assume H2;
        have G: πᶜ ((provable a ctx) ∧ᶜ (provable b ctx) ) {
            refine (@∧ᶜ_istrue (provable a ctx) (provable b ctx)) H; 
        };
        apply ∧ᶜᵢ 
        { refine ⇒ᶜₑ (∀ᶜₑ σ (⇒ᶜₑ (∀ᶜₑ ctx IHa) (∧ᶜₑ₁ G))) H2; }
        { refine ⇒ᶜₑ (∀ᶜₑ σ (⇒ᶜₑ (∀ᶜₑ ctx IHb) (∧ᶜₑ₂ G))) H2; }
    }
    {
        assume a IHa; assume b IHb;
        apply ∀ᶜᵢ; assume ctx; apply ⇒ᶜᵢ;  assume H; apply ∀ᶜᵢ; assume σ;  apply ⇒ᶜᵢ;  assume H2;
        have G: πᶜ ((provable a ctx) ∨ᶜ (provable b ctx) ) {
            refine (@∨ᶜ_istrue (provable a ctx) (provable b ctx)) H; 
        };
        apply ∨ᶜₑ G
        {
            assume Ha;
            apply ∨ᶜᵢ₁;
            refine ⇒ᶜₑ (∀ᶜₑ σ (⇒ᶜₑ (∀ᶜₑ ctx IHa) Ha)) H2;
        }
        {
            assume Hb;
            apply ∨ᶜᵢ₂;
            refine ⇒ᶜₑ (∀ᶜₑ σ (⇒ᶜₑ (∀ᶜₑ ctx IHb) Hb)) H2;
        }
    }
    {
        assume p IH1 q IH2;
        apply ∀ᶜᵢ; assume ctx;
        apply ⇒ᶜᵢ;  assume H;
        apply ∀ᶜᵢ; assume σ;
        apply ⇒ᶜᵢ;  assume H2;
        apply ⇒ᶜᵢ;  assume Hp;
        refine ⇒ᶜₑ (∀ᶜₑ σ (⇒ᶜₑ (∀ᶜₑ (p ⸬ ctx) IH2) H)) _;
        apply ∧ᶜᵢ
        { apply Hp }
        { refine H2 }
    }
end;
