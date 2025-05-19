require open Stdlib.Prop;
require open Stdlib.FOL;
require open Stdlib.Eq;
require open Stdlib.Nat;
require Stdlib.Bool;
require open Stdlib.Set;
require open Stdlib.List;
require open lambdapi.Alethe;
require open lambdapi.Classic;
open Stdlib.Bool;

inductive prop: TYPE ≔
| pTrue: prop
| pFalse: prop
| pAnd: prop → prop → prop
| pOr: prop → prop → prop
| pImpl: prop → prop → prop
// | pNeg: prop → prop
;


symbol imp : 𝔹 → 𝔹 → 𝔹;
notation imp infix left 20;
rule true imp true ↪ true
with true imp false ↪ false
with false imp true ↪ true
with false imp false ↪ true
;

symbol propS: Set;

rule τ propS ↪ prop;
// 
print prop;
symbol ind_propᶜ : Π p0: (prop → Prop), 
  πᶜ (p0 pTrue) → 
  πᶜ (p0 pFalse) → 
  (Π x0: prop, πᶜ (p0 x0) → Π x1: prop, πᶜ (p0 x1) → πᶜ (p0 (pAnd x0 x1))) → 
  (Π x0: prop, πᶜ (p0 x0) → Π x1: prop, πᶜ (p0 x1) → πᶜ (p0 (pOr x0 x1)))  →
  //(Π x0: prop, πᶜ (p0 x0) → πᶜ (p0 (pNeg x0))) →
  πᶜ (`∀ᶜ x: prop, p0 x);

// A denotation function converts our syntax into a semantic value
// The σ is the context which contains the mapping from variables to Props.
symbol prop_denote (p: prop): Prop;
rule prop_denote pTrue ↪ ⊤
with prop_denote pFalse ↪ ⊥
// with prop_denote (pNeg $x) ↪ ¬ (prop_denote $x)
with prop_denote (pAnd $x $y) ↪  (prop_denote $x) ∧ᶜ (prop_denote $y)
with prop_denote (pOr $x $y) ↪  (prop_denote $x) ∨ᶜ (prop_denote $y)
;

sequential symbol prop_reify: Prop → prop;
rule prop_reify ⊤ ↪ pTrue
with prop_reify ⊥ ↪ pFalse
//with prop_reify (¬ $x) ↪  pNeg (prop_reify $x)
with prop_reify ($x ∧ᶜ $y) ↪  pAnd (prop_reify $x) (prop_reify $y)
with prop_reify ($x ∨ᶜ $y) ↪  pOr (prop_reify $x) (prop_reify $y)
;




symbol provable (goal: prop) : 𝔹;
rule provable pTrue ↪ true
with provable pFalse  ↪ false
with provable (pAnd $l $r)  ↪ (provable $l ) and (provable $r )
with provable (pOr $l $r)  ↪ (provable $l ) or (provable $r )
//with provable (pNeg $x)  ↪ not (provable $x)
;



opaque symbol false≠true : πᶜ (false = true) → πᶜ ⊥ ≔
begin
  admit
end;

opaque symbol true≠false : πᶜ (true = false) → πᶜ ⊥ ≔
begin
  admit
end;

opaque symbol true=not_false : πᶜ (true = not false)  ≔
begin
  reflexivity
end;

opaque symbol not_true=false : πᶜ (not true = false)  ≔
begin
  reflexivity
end;


opaque symbol case_𝔹2 b : πᶜ ((b = true) ∨ᶜ (b = false)) ≔
begin
    admit
end;

opaque symbol ind_𝔹_eq p b:
 (πᶜ(b = true) → πᶜ(p b)) → (πᶜ(b = false) → πᶜ(p b)) → πᶜ(p b) ≔
begin
  admit
end;

opaque symbol ∧ᶜ_istrue [p q : 𝔹] : πᶜ(p and q) → πᶜ(p ∧ᶜ q) ≔
begin
  admit
end;

opaque symbol ∨ᶜ_istrue [p q : 𝔹] : πᶜ(p or q) → πᶜ(p ∨ᶜ q) ≔
begin
  admit
end;

opaque symbol ¬ᶜ_istrue [p: 𝔹] : πᶜ (not p) → πᶜ (¬ p) ≔
begin
  admit
end;

symbol ⇒_istrue [p q : 𝔹] : πᶜ (p imp q) → πᶜ (p ⇒ q);

opaque symbol provable_sound2: πᶜ (`∀ᶜ g, (provable g) ⇒ᶜ prop_denote g) ≔
begin
refine ind_propᶜ (λ x, (provable x)  ⇒ᶜ prop_denote x) _ _ _ _
{
    simplify;
    apply ⇒ᶜᵢ;
    refine (λ x, x)
}
{
    apply ⇒ᶜᵢ;
    refine (λ x, x)
}
{
  assume x IHx;
  assume y IHy;
  apply ⇒ᶜᵢ; assume g;
  have g2: πᶜ (provable x ∧ᶜ (provable y)) { refine ∧ᶜ_istrue g  };
  apply ∧ᶜᵢ
  {
    apply ⇒ᶜₑ IHx;
    refine ∧ᶜₑ₁ g2
  }
  {
    apply ⇒ᶜₑ IHy;
    refine ∧ᶜₑ₂ g2
  }
}
{
  assume x IHx;
  assume y IHy;
  apply ⇒ᶜᵢ; assume g;
  have g2: πᶜ (provable x ∨ᶜ (provable y)) { refine ∨ᶜ_istrue g  };
  apply ∨ᶜₑ g2
  {
    assume gx;
    apply ∨ᶜᵢ₁;
    apply ⇒ᶜₑ IHx gx; 
  }
  {
    assume gy;
    apply ∨ᶜᵢ₂;
    apply ⇒ᶜₑ IHy gy; 
  }
}
// {
//   simplify;
//   assume x IHx;
//   apply ⇒ᶜᵢ; assume g;
//   have tmp: πᶜ (istrue (not (provable x))) { refine g };
//   have g2: πᶜ (¬ (provable x)) { refine  @¬ᶜ_istrue (provable x) g; };
//   have e: πᶜ (((provable x) = true) ∨ᶜ ((provable x) = false)) {admit};
//   apply ∨ᶜₑ e
//   {
//     assume Hv;
//     apply ⇒ᶜᵢ'; assume h;
//     have g3: πᶜ (¬ (istrue true)) { rewrite left Hv; refine g2 };
//     apply ⇒ᶜₑ' g3;
//     apply trivial
//   }
//   {
//     simplify;
//     assume Hv;
//     apply ⇒ᶜᵢ'; assume h;
//     remove e;
//     remove tmp;
//      apply ⇒ᶜₑ' g2;
//   }
// }
end;