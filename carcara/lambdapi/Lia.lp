require open Stdlib.Bool;
require open Stdlib.Eq;
require open Stdlib.Set;
require open Stdlib.Pos;
require open Stdlib.Prop;
require open Stdlib.Comp;
require open Stdlib.Z;
require open lambdapi.Classic;
require open lambdapi.Alethe;

symbol ≐_decides [x y: ℤ] : πᶜ ((x ≐ y)= Eq) →  πᶜ (x = y);

constant symbol Ring : TYPE;
symbol ring : Set;
rule τ ring ↪ Ring;

associative commutative symbol add : Ring → Ring → Ring;
constant symbol Z : Ring;
//symbol opp : Ring → Ring;
symbol const: ℤ → Ring;

symbol mul [a] : ℤ → τ a → Ring;

rule add Z $x ↪ $x
with add $x Z ↪ $x

// with add (opp $x) $x ↪ Z
// with add $x (opp $x) ↪ Z
// with add (opp $x) (add $x $y) ↪ $y
// with add $x (add (opp $x) $y) ↪ $y

with add (mul $k $x) (mul $l $x) ↪ mul ($k + $l) $x
with add (mul $k $x) (add (mul $l $x) $y) ↪ add (mul ($k + $l) $x) $y

with add (const $x) (const $y) ↪ (const ($x + $y))

// with opp Z ↪ Z
// with opp (opp $x) ↪ $x
// with opp (add $x $y) ↪ add (opp $x) (opp $y)

//with opp (mul $k $x) ↪ mul (~ $k) $x

with mul 0 _ ↪ Z
with mul (~ ~ $k) $a ↪ mul $k $a

with mul (Zpos $x) (Zpos $y) ↪ const ((Zpos $x) × (Zpos $y))
with mul (Zpos $x) (Zneg $y) ↪ const ((Zpos $x) × (Zneg $y))
with mul (Zneg $x) (Zpos $y) ↪ const ((Zneg $x) × (Zpos $y))
with mul (Zneg $x) (Zneg $y) ↪ const ((Zneg $x) × (Zneg $y))


with mul $c (Zpos $d × $x) ↪ mul ($c × Zpos $d) $x
with mul $c (Zneg $d × $x) ↪ mul ($c × Zneg $d) $x
with mul $c (~ $x) ↪ mul (~ $c) $x
with mul $c ($x + $y) ↪ add (mul $c $x) (mul $c $y)
;



// ====================

symbol f: τ (int ⤳ int);

symbol ≥? : τ ring → τ ring → 𝔹; notation ≥? infix 10;
symbol >? : τ ring → τ ring → 𝔹; notation >? infix 10;

rule const $x ≥? const $y ↪ isGt ($x ≐ $y) Stdlib.Bool.or (isEq ($x ≐ $y));
rule const $x >? const $y ↪ isGt ($x ≐ $y);

//symbol f: τ int;

// (not (= (* -1 (f 0)) (* -1 10)))
// (not (< (f 0) 5)) 
// (< (+ (* -1 (f 0)) (f 0)) (+ (* -1 10) 5))

// (not (< F 1))
// (<= F 0)


// (not (< F 1)) (<= F 0)
symbol F: τ int;

sequential symbol reify [a] : τ a → Ring;
rule @reify int Z0 ↪ Z
with @reify int ($x + $y) ↪ add (reify $x) (reify $y)
with reify $a ↪ mul 1 $a
;

compute (reify (((~ F - ~ 5) + ((F + (~ 1 × F)) - (5 + (~ 1 × 12)))) + (~ 1 × F)));
compute (reify (((~ 1) × F)));
compute (reify ((0 × F)));
compute (reify (~ 1 × (~ 1 × F)));
compute (reify (~  F));
compute (reify (3 × F));
compute (reify (3 × 12));

symbol x: τ int;
symbol y: τ int;
symbol z: τ int;

compute (reify (((2 × x) - y + z) + ((~ x) + y - z) + (~ y + z)));


notation ≥ infix 10;

// Lemma Zle_not_gt n m : n <= m -> ~ n > m.
symbol Zle_not_gt n m:  πᶜ ((n ≤ m) = ¬ (n > m));

symbol Zlt_not_ge n m:  πᶜ ((n < m) = ¬ (n ≥ m));

symbol Zge_not_lt : Π n: ℤ, Π m: ℤ, πᶜ ((n ≥ m) = ¬ (n < m));

symbol Zgt_not_le : Π n: ℤ, Π m: ℤ, πᶜ ((n > m) = ¬ (n ≤ m));

// Lemma Zmult_gt_compat_r n m p : p > 0 -> n > m -> n * p > m * p.
symbol Zmult_gt_compat c a b : π (c > 0) → π (a > b) → π (c × a > c × b) ;

// Lemma Zmult_ge_compat_r n m p : n >= m -> p >= 0 -> n * p >= m * p.
symbol Zmult_ge_compat c a b : π (c > 0) → π (a ≥ b) → π (c × a ≥ c × b);

symbol Zgt_le_succ_r a b: πᶜ (a > b) → πᶜ (a ≥ b + 1);

symbol Zinv_lt a b: πᶜ (a < b) → πᶜ (~ a > ~ b);

symbol Zsum_geq_s [a b c d]: πᶜ (a ≥ b) → πᶜ (c ≥ d) → πᶜ (a + c ≥ b + d);

symbol Z_diff_geq_Z0 a b: πᶜ (a ≥ b) → πᶜ (a - b ≥ 0);
symbol Z_diff_gt_Z0 a b: πᶜ (a > b) → πᶜ (a - b > 0);

symbol completude_lia a b: πᶜ (a ≥ b) → πᶜ (istrue ((reify a) ≥? (reify b)));

symbol Zgt_le_succ_r_eq a b: πᶜ ((a > b) = (a ≥ b + 1));

symbol Zinv_lt_eq a b: πᶜ ((a < b) = (~ a > ~ b));

symbol Zinv_le_eq a b: πᶜ ((a ≤ b) = (~ a ≥ ~ b));

symbol Z_diff_geq_Z0_eq a b: πᶜ ((a ≥ b) = (a - b ≥ 0));

symbol Z_diff_gt_Z0_eq a b: πᶜ ((a > b) = (a - b > 0));

symbol Z_diff_eq_Z0_eq a b: πᶜ ((a = b) = (a - b = 0));


//symbol Z_eq_antisym [a b: τ int]: πᶜ (a = b) → πᶜ ((a ≤ b) ∧ᶜ (a ≥ b));

//Axioms
symbol Z_eq_antisym (a b: τ int):  πᶜ ((¬ (a = b)) = ¬ (a ≥ b));

symbol Zmult_eq_compat_eq (c a b: τ int) : πᶜ ((¬ (a = b)) = ¬ (c × a = c × b));
symbol Zmult_gt_compat_eq c a b : πᶜ (¬ (a > b) = ¬ (c × a > c × b)) ;
symbol Zmult_ge_compat_eq c a b : πᶜ (¬ (a ≥ b) = ¬ (c × a ≥ c × b)) ;

opaque >;
opaque <;

symbol la4 : πᶜ (¬ ((~ 1) × F = (~ 1 × 10)) ∨ᶜ ¬ (F < 5) ∨ᶜ ((~ 1 × F) + F < (~ 1 × 10) + 5)) ≔
begin
// step 1
rewrite .[x in _ ∨ᶜ _ ∨ᶜ x ] Zlt_not_ge ;
// step 2
rewrite Zinv_lt_eq;
// step 3
rewrite Z_diff_geq_Z0_eq;
rewrite Z_diff_gt_Z0_eq;
// step 4
rewrite Zgt_le_succ_r_eq;
// step 5
rewrite (Zmult_eq_compat_eq (~ 1) (~ 1 × F) (~ 1 × 10));
rewrite (Zmult_ge_compat_eq 1 (~ F - ~ 5) (0 + 1));
rewrite (Zmult_ge_compat_eq 1 (((~ 1 × F) + F) - ((~ 1 × 10) + 5)) 0);
rewrite Z_eq_antisym;
//step 2
rewrite imp_eq_or;
apply ⇒ᶜᵢ; assume H1;
rewrite imp_eq_or;
apply ⇒ᶜᵢ; assume H2;
apply ¬ᶜᵢ; assume H3;
set H1l ≔ (~ 1 × (~ 1 × F));
set H1r ≔ (~ 1 × (~ 1 × 10));
set H2l ≔ (1 × (~ F - ~ 5));
set H2r ≔ ((0 + 1));
set H3l ≔ (1 × (((~ 1 × F) + F) - ((~ 1 × 10) + 5)));
set H3r ≔ (0);
//step 5
have Hsum: πᶜ (H1l + H2l + H3l ≥ H1r + H2r + H3r) {
    apply Zsum_geq_s (Zsum_geq_s H1 H2) H3;
};
refine @completude_lia (H1l + H2l + H3l) (H1r + H2r + H3r)  Hsum;
end;


compute reify (1 × (~ F - ~ 5));