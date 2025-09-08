require open Stdlib.Nat Stdlib.Z Stdlib.Prop;


inductive Mask: TYPE ≔
| IsNul : Mask
| IsPos : ℙ →  Mask
| IsNeg : Mask
;

symbol mask: Set;
rule τ mask ↪ Mask;

symbol sub': Mask → ℙ;
rule sub' (IsPos $p) ↪ $p
with sub' IsNeg ↪ H
with sub' IsNul ↪ H
;

// x -> 2*x
symbol double_mask: Mask → Mask;
rule double_mask IsNul ↪ IsNul
with double_mask IsNeg ↪ IsNeg
with double_mask (IsPos $x) ↪ IsPos (O $x)
;

// x -> 2*x-1
symbol pred_double : ℙ → ℙ;
rule pred_double (I $x) ↪ I (O $x)
with pred_double (O $x) ↪ I (pred_double $x)
with pred_double H ↪ H
;

compute val ((O (O (I H))));
compute val (pred_double (O (O (I H))));

//  x -> 2*x - 2
symbol double_pred_mask: ℙ → Mask;
rule double_pred_mask H ↪ IsNul
with double_pred_mask (I $x) ↪ IsPos (O (O $x))
with double_pred_mask (O $x) ↪ IsPos (O (pred_double $x))
;

// x -> 2 * x + 1
symbol suc_double_mask: Mask → Mask;
rule suc_double_mask IsNul ↪ IsPos H
with suc_double_mask IsNeg ↪ IsNeg
with suc_double_mask (IsPos $x) ↪ IsPos (I $x)
;

symbol sub_mask_carry :  ℙ → ℙ → Mask;
symbol sub_mask :  ℙ → ℙ → Mask;

rule sub_mask_carry (I $p) (I $q) ↪ suc_double_mask (sub_mask_carry $p $q)
with sub_mask_carry (I $p) (O $q) ↪ double_mask (sub_mask $p $q)
with sub_mask_carry (I $p) H ↪ IsPos (pred_double $p)
with sub_mask_carry (O $p) (I $q) ↪ double_mask (sub_mask_carry $p $q)
with sub_mask_carry (O $p) (O $q) ↪ suc_double_mask (sub_mask_carry $p $q)
with sub_mask_carry (O $p) H ↪ double_pred_mask $p
with sub_mask_carry H _ ↪ IsNeg
;

rule sub_mask (I $p) (I $q) ↪ double_mask (sub_mask $p $q)
with sub_mask (I $p) (O $q) ↪ suc_double_mask (sub_mask $p $q)
with sub_mask (I $p) H ↪ IsPos (O $p)
with sub_mask (O $p) (I $q) ↪ suc_double_mask (sub_mask_carry $p $q)
with sub_mask (O $p) (O $q) ↪ double_mask (sub_mask $p $q)
with sub_mask (O $p) H ↪ IsPos (pred_double $p)
with sub_mask H H ↪ IsNul
with sub_mask H _ ↪ IsNeg
;

symbol sub: ℙ → ℙ → ℙ;
rule sub $a $b ↪ sub' (sub_mask $a $b);

// https://coq.inria.fr/doc/V8.18.0/aclia/Coq.PArith.BinPosDef.html#Pos.gcdn
symbol Stein_gcd (a b: ℙ): ℙ;
rule Stein_gcd H _ ↪ H    // 1 / gcd(1, b) = 1
with Stein_gcd _ H ↪ H    // gcd(a, 1) = 1
with Stein_gcd (O $a) (O $b) ↪ O (Stein_gcd $a $b) // gcd(2a, 2b) = 2 * gcd(a,b) bc 2 is a common divisor
with Stein_gcd (I $a) (O $b) ↪ (Stein_gcd $a $b) // u is odd then 2 is not a common division
with Stein_gcd (O $a) (I $b) ↪ (Stein_gcd $a (I $b))
with Stein_gcd (I $a) (I $b) ↪
    let res ≔ (compare $a $b) in
        if (isEq res) 
            (I $a)  // Eq
            (if (isLt res)
                (Stein_gcd (sub $b $a) (I $a)) // Lt
                (Stein_gcd (sub $a $b) (I $b))) // Gt
;

// This function reduces the number `a` by the greatest
// common divisor of `a` and `b`, i.e.
//
//        ReduceA a b  =  a / gcd(a,b).
//
// It follows the control flow of Stein’s binary gcd
// algorithm, ensuring that the quotient is computed
// in lockstep with the gcd without explicitly dividing.
symbol red_by_Stein (a b: ℙ): ℙ;
rule red_by_Stein H _ ↪ H // 1 / gcd(1, b) = 1
with red_by_Stein $a H ↪ $a // gcd(a, 1) = 1 so return result = a
with red_by_Stein (O $a) (O $b) ↪ red_by_Stein $a $b // Both even, gcd(2a , 2b)= 2 * gcd (a, b) ⇒ (2 * a)/(2 * g) = a/g

with red_by_Stein (O $a) (I $b) ↪ O (red_by_Stein $a (I $b)) // a even, b odd: gcd(2a,odd)=g ⇒ (2a)/g = 2·(a/g)

/* a odd, b even: gcd(odd,2b)=g ⇒ a/g unchanged; just shrink b */
with red_by_Stein (I $a) (O $b) ↪ red_by_Stein (I $a) $b

/* both odd: compare the tails (since I $a = 2a+1) */
with red_by_Stein (I $a) (I $b) ↪
  let res ≔ (compare $a $b) in
    if (isEq res)
      H                                       // a == b ⇒ gcd = I a ⇒ (I a)/(I a) = 1
      (if (isLt res)
         (red_by_Stein (I $a) (sub (I $b) (I $a)))   // gcd(I a, I b) = gcd(I b − I a, I a)
         (red_by_Stein (I $a) (sub (I $a) (I $b))))  // symmetric case
;

symbol abs: ℤ → ℤ;
rule abs Z0 ↪ Z0
with abs (Zpos $x) ↪ Zpos $x
with abs (Zneg $x) ↪ Zpos $x
;

symbol sgn: ℤ → ℤ;
rule sgn Z0 ↪ Z0
with sgn (Zpos _) ↪ (Zpos H)
with sgn (Zneg _) ↪ (Zneg H);

// This function reduces the number `a` by the GCD compute with Stein algorithm
symbol Z_red_Stein: ℤ → ℤ → ℤ;
rule Z_red_Stein Z0 _ ↪ Z0 // 0 reduced by anything is 0 
with Z_red_Stein $a Z0 ↪ sign $a // gcd(|a|, 0)  = |a| => a / |a| = sign(a)
// Both nonzero: take gcd on ℙ payloads, keep sign of x
with Z_red_Stein (Zpos $a) (Zpos $b) ↪ Zpos (red_by_Stein $a $b)
with Z_red_Stein (Zpos $a) (Zneg $b) ↪ Zpos (red_by_Stein $a $b)
with Z_red_Stein (Zneg $a) (Zpos $b) ↪ Zneg (red_by_Stein $a $b)
with Z_red_Stein (Zneg $a) (Zneg $b) ↪ Zneg (red_by_Stein $a $b);
