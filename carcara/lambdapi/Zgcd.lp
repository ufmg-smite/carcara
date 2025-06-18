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
rule Stein_gcd H _ ↪ H
with Stein_gcd _ H ↪ H
// with Stein_gcd H H ↪ H
// with Stein_gcd (O _) H ↪ H
// with Stein_gcd (I _) H ↪ H
with Stein_gcd (O $a) (O $b) ↪ O (Stein_gcd $a $b)
with Stein_gcd (I $a) (O $b) ↪ (Stein_gcd (I $a) $b)
// with Stein_gcd H (O $b) ↪ (Stein_gcd H $b)
with Stein_gcd (O $a) (O $b) ↪ (Stein_gcd $a (O $b))
with Stein_gcd (O $a) (I $b) ↪ (Stein_gcd $a (I $b))
// with Stein_gcd (O $a) H ↪ (Stein_gcd $a H)
with Stein_gcd (I $a) (I $b) ↪
    let res ≔ (compare $a $b) in
        if (isEq res) 
            (I $a)  // Eq
            (if (isLt res)
                (Stein_gcd (sub $b $a) (I $a)) // Lt
                (Stein_gcd (sub $a $b) (I $b))) // Gt
;

compute val (Stein_gcd  (O (O (O (I (I (O (O H))))))) (O (O (I H))));

symbol abs: ℤ → ℤ;
rule abs Z0 ↪ Z0
with abs (Zpos $x) ↪ Zpos $x
with abs (Zneg $x) ↪ Zpos $x
;

//  Greatest Common Divisor 
symbol Z_gcd: ℤ → ℤ → ℤ;
rule Z_gcd Z0 $b ↪ abs $b
with Z_gcd $a Z0 ↪ abs $a
with Z_gcd (Zpos $a) (Zpos $b) ↪ Zpos (Stein_gcd $a $b)
with Z_gcd (Zpos $a) (Zneg $b) ↪ Zpos (Stein_gcd $a $b)
with Z_gcd (Zneg $a) (Zpos $b) ↪ Zpos (Stein_gcd $a $b)
with Z_gcd (Zneg $a) (Zneg $b) ↪ Zpos (Stein_gcd $a $b)
;


// Qc : A canonical representation of rational numbers. based on the setoid representation Q.

// (** A generalized gcd, also computing division of a and b by gcd. *)

// Fixpoint ggcdn (n : nat) (a b : positive) : (positive*(positive*positive)) :=
//   match n with
//     | O => (1,(a,b))
//     | S n =>
//       match a,b with
//         | 1, _ => (1,(1,b))
//         | _, 1 => (1,(a,1))
//         | a~0, b~0 =>
//            let (g,p) := ggcdn n a b in
//            (g~0,p)
//         | _, b~0 =>
//            let '(g,(aa,bb)) := ggcdn n a b in
//            (g,(aa, bb~0))
//         | a~0, _ =>
//            let '(g,(aa,bb)) := ggcdn n a b in
//            (g,(aa~0, bb))
//         | a'~1, b'~1 =>
//            match a' ?= b' with
//              | Eq => (a,(1,1))
//              | Lt =>
//                 let '(g,(ba,aa)) := ggcdn n (b'-a') a in
//                 (g,(aa, aa + ba~0))
//              | Gt =>
//                 let '(g,(ab,bb)) := ggcdn n (a'-b') b in
//                 (g,(bb + ab~0, bb))
//            end
//       end
//   end.
sequential symbol pos_ggcd (a b: ℙ): τ (pos × (pos × pos));
rule pos_ggcd H $b ↪ (H ‚ (H ‚ $b))
with pos_ggcd $a H ↪ (H ‚ ($a ‚ H))
with pos_ggcd (O $a) (O $b) ↪ let r ≔ pos_ggcd $a $b in (O (r ₁) ‚ r ₂)
with pos_ggcd $a (O $b) ↪ let r ≔ pos_ggcd $a $b in ((r ₁) ‚ (r ₂ ₁ ‚ O ((r ₂) ₂)))
with pos_ggcd (O $a) $b ↪ let r ≔ pos_ggcd $a $b in ((r ₁) ‚ (O (r ₂ ₁) ‚ ((r ₂) ₂)))
with pos_ggcd (I $a) (I $b) ↪ 
  let res ≔ (compare $a $b) in
  if (isEq res) 
      ((I $a) ‚ (H ‚ H))  // Eq
      (if (isLt res)
        (let r ≔ pos_ggcd (sub $b $a) (I $a) in
          let ba ≔  ((r ₂) ₁) in
          let aa ≔  ((r ₂) ₂) in
            r ₁ ‚ ( aa ‚ (add aa (O ba)))
        ) // Lt
        (
          let r ≔ pos_ggcd (sub $a $b) (I $b) in
          let ab ≔  ((r ₂) ₁) in
          let bb ≔  ((r ₂) ₂) in
            r ₁ ‚ ((add bb (O ab)) ‚ bb)
        )
      ) // Gt
;

compute (pos_ggcd (O (O (O (I (I (O (O H))))))) (O (O (I H))));
// Definition sgn z :=
//   match z with
//     | 0 => 0
//     | pos p => 1
//     | neg p => -1
//   end.

symbol sgn: ℤ → ℤ;
rule sgn Z0 ↪ Z0
with sgn (Zpos _) ↪ (Zpos H)
with sgn (Zneg _) ↪ (Zneg H);


// Definition ggcd a b : Z*(Z*Z) :=
//   match a,b with
//     | 0, _ => (abs b,(0, sgn b))
//     | _, 0 => (abs a,(sgn a, 0))
//     | pos a, pos b =>
//        let '(g,(aa,bb)) := Pos.ggcd a b in (pos g, (pos aa, pos bb))
//     | pos a, neg b =>
//        let '(g,(aa,bb)) := Pos.ggcd a b in (pos g, (pos aa, neg bb))
//     | neg a, pos b =>
//        let '(g,(aa,bb)) := Pos.ggcd a b in (pos g, (neg aa, pos bb))
//     | neg a, neg b =>
//        let '(g,(aa,bb)) := Pos.ggcd a b in (pos g, (neg aa, neg bb))
//   end.
symbol Zggcd (a b: ℤ): τ (int × (int × int));
rule Zggcd Z0 $b ↪ (abs $b ‚ (Z0 ‚ sgn $b))
with Zggcd $a Z0 ↪ (abs $a ‚ (sgn $a ‚ Z0))
with Zggcd (Zpos $a) (Zpos $b) ↪ 
  let r ≔ pos_ggcd $a $b in
    ((Zpos (r ₁)) ‚  (Zpos (r ₂ ₁) ‚  Zpos (r ₂ ₂)))
with Zggcd (Zpos $a) (Zneg $b) ↪ 
  let r ≔ pos_ggcd $a $b in
    ((Zpos (r ₁)) ‚  (Zpos (r ₂ ₁) ‚  Zneg (r ₂ ₂)))
with Zggcd (Zneg $a) (Zpos $b) ↪ 
  let r ≔ pos_ggcd $a $b in
    ((Zpos (r ₁)) ‚  (Zneg (r ₂ ₁) ‚  Zpos (r ₂ ₂)))
with Zggcd (Zneg $a) (Zneg $b) ↪ 
  let r ≔ pos_ggcd $a $b in
    ((Zpos (r ₁)) ‚  (Zneg (r ₂ ₁) ‚  Zneg (r ₂ ₂)))
;

compute Zggcd (Zpos (O (O (O (I (I (O (O H)))))))) (Zpos (O (O (I H))));

compute Zggcd (Zpos (Stdlib.Pos._8)) (Zpos (Stdlib.Pos._6));

compute Zggcd (Zpos (Stdlib.Pos._4)) (Zpos (Stdlib.Pos._8));

// Definition to_pos (z:Z) : positive :=
//   match z with
//     | pos p => p
//     | _ => 1%positive
//   end.
symbol to_pos: ℤ → ℙ;
rule to_pos (Zpos $p) ↪ $p
with to_pos (Zneg _) ↪ H
with to_pos Z0 ↪ H
;
