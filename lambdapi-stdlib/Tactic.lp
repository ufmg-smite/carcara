// Lambdapi tactics as terms, built on top of Stdlib.Tactic.
//
// Lambdapi now type-checks every tactic builtin against a universe-polymorphic
// signature (Π [l] [a:U l], η a → Tactic), so the builtins themselves live in
// Stdlib.Tactic / Stdlib.Univ. This module only adds the spellings and helpers
// the Alethe library and the carcara translator rely on.

require open lambdapi.Alethe;
require open Stdlib.String Stdlib.Univ Stdlib.Tactic;

// Stdlib.Univ only coerces `Π x:τ b, π c` (one binder) into the universe
// encoding. Alethe lemmas passed to `#rewrite`/`#apply` as terms quantify over
// `Prop` directly and over several variables, so we add one rule per binder
// shape that occurs in this library. (A recursive rule with a fresh pattern
// variable under a binder crashes lambdapi dev-3.0.0-155.)
unif_rule @η $l $a ≡ Π x:Prop, π $c.[x] ↪
  [$l ≡ prop; $a ≡ @∀ o (λ x:Prop, $c.[x])];
unif_rule @η $l $a ≡ Π x:Prop, Π y:Prop, π $c.[x;y] ↪
  [$l ≡ prop; $a ≡ @∀ o (λ x:Prop, @∀ o (λ y:Prop, $c.[x;y]))];
unif_rule @η $l $a ≡ Π x:Prop, Π y:Prop, Π z:Prop, π $c.[x;y;z] ↪
  [$l ≡ prop; $a ≡ @∀ o (λ x:Prop, @∀ o (λ y:Prop, @∀ o (λ z:Prop, $c.[x;y;z])))];
unif_rule @η $l $a ≡ Π x:τ $s.[], Π y:τ $s.[], π $c.[x;y] ↪
  [$l ≡ prop; $a ≡ @∀ $s.[] (λ x:τ $s.[], @∀ $s.[] (λ y:τ $s.[], $c.[x;y]))];
unif_rule @η $l $a ≡ Π b:Prop, Π x:τ $s.[], Π y:τ $s.[], π $c.[b;x;y] ↪
  [$l ≡ prop; $a ≡ @∀ o (λ b:Prop, @∀ $s.[] (λ x:τ $s.[], @∀ $s.[] (λ y:τ $s.[], $c.[b;x;y])))];
unif_rule @η $l $a ≡ Π b:Prop, Π x:τ $s.[], Π y:τ $s.[], Π z:τ $s.[], π $c.[b;x;y;z] ↪
  [$l ≡ prop; $a ≡ @∀ o (λ b:Prop, @∀ $s.[] (λ x:τ $s.[], @∀ $s.[] (λ y:τ $s.[], @∀ $s.[] (λ z:τ $s.[], $c.[b;x;y;z]))))];

// A module that contains string literals must carry the "String" builtin itself:
// the .lpo loader (handle/compile.ml) looks it up in this module's builtin table.
builtin "String" ≔ Stdlib.String.String;

// Set-level codes so that lists of strings / tactics can be formed.

constant symbol string : Set;
rule τ string ↪ String;

symbol tactic : Set;
rule τ tactic ↪ Tactic;

// Tactic composition was historically spelled `and`.
symbol and : Tactic → Tactic → Tactic ≔ &;
notation and infix right 15;

notation #orelse infix left 10;
notation #repeat prefix 2;

// `#rewrite_gen "left" "pattern" h` and the short `#rewrite h` form.
symbol #rewrite_gen (dir pat : String) [l] [a:U l] (h : η a) : Tactic ≔
  Stdlib.Tactic.#rewrite dir pat h;

symbol #rewrite [l] [a:U l] (h : η a) : Tactic ≔ Stdlib.Tactic.#rewrite "" "" h;

/*****************************************************************************/

symbol #do : ℕ → Tactic → Tactic;

rule #do 0 _ ↪ nothing
with #do ($n +1)  $t ↪ $t and (#do $n $t);

// Used to remove trailing `⊥` due to usage of ⟇_to_∨_rw or disj
// in order to compare left and right term in simplification rule.
symbol #repeat_or_id_r : Tactic ≔ #repeat (#rewrite or_identity_r);

/******************************************************************************
*  Definition of Alethe meta tactic
******************************************************************************/

symbol applyAny : 𝕃 tactic → Tactic;
rule applyAny ($t0 ⸬ $tl) ↪ $t0 #orelse (applyAny $tl)
with applyAny Stdlib.List.□ ↪ #fail;
