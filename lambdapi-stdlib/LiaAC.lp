/**********
The standard library use this rewrites rules in Z and Pos that has been prove confluent.

(VAR
  a: Z
  b: Z
  x : P
  q : P
  y : P
)
(THEORY (AC addG))
(RULES
  —(Z0) -> Z0
  —(Zpos(p)) -> Zneg(p)
  —(Zneg(p)) -> Zpos(p)
  —(—(a)) -> a

  double(Z0) -> Z0
  double(Zpos(p)) -> Zpos(O(p))
  double(Zneg(p)) -> Zneg(O(p))
  
  succ_double(Z0) -> Zpos(H)
  succ_double(Zpos(p)) -> Zpos(I(p))
  succ_double(Zneg(p)) -> Zneg(pos_pred_double(p))
  
  pred_double(Z0) -> Zneg(H)
  pred_double(Zpos(p)) -> Zpos(pos_pred_double(p))
  pred_double(Zneg(p)) -> Zneg(I(p))

  sub(I(p), I(q)) -> double(sub(p, q))
  sub(I(p), O(q)) -> succ_double(sub(p, q))
  sub(I(p), H) -> Zpos(O(p))
  sub(O(p), I(q)) -> pred_double(sub(p, q))
  sub(O(p), O(q)) -> double(sub(p, q))
  sub(O(p), H) -> Zpos(pos_pred_double(p))
  sub(H, I(q)) -> Zneg(O(q))
  sub(H, O(q)) -> Zneg(pos_pred_double(q))
  sub(H, H) -> Z0

  +(Z0,a) -> a
  +(a,Z0) -> a
  +(Zpos(x), Zpos(y)) -> Zpos(add(x, y))
  +(Zpos(x), Zneg(y)) -> sub(x, y)
  +(Zneg(x), Zpos(y)) -> sub(y, x)
  +(Zneg(x), Zneg(y)) -> Zneg(add(x, y))
  
  mult(Z0, a) -> Z0
  mult(a, Z0) -> Z0
  mult(Zpos(x), Zpos(y)) -> Zpos(mul(x, y))
  mult(Zpos(x), Zneg(y)) -> Zneg(mul(x, y))
  mult(Zneg(x), Zpos(y)) -> Zneg(mul(x, y))
  mult(Zneg(x), Zneg(y)) -> Zpos(mul(x, y))


  succ(I(x)) -> O(succ(x))
  succ(O(x)) -> I(x)
  succ(H) -> O(H)
  add(I(x), I(q)) -> O(addcarry(x, q))
  add(I(x), O(q)) -> I(add(x, q))
  add(O(x), I(q)) -> I(add(x, q))
  add(O(x), O(q)) -> O(add(x, q))
  add(x, H) -> succ(x)
  add(H, y) -> succ(y)

  addcarry(I(x), I(q)) -> I(addcarry(x, q))
  addcarry(I(x), O(q)) -> O(addcarry(x, q))
  addcarry(O(x), I(q)) -> O(addcarry(x, q))
  addcarry(O(x), O(q)) -> I(add(x, q))
  addcarry(x, H) -> add(x, O(H))
  addcarry(H, y) -> add(O(H), y)
  
  pos_pred_double(I(x)) -> I(O(x))
  pos_pred_double(O(x)) -> I(pos_pred_double(x))
  pos_pred_double(H) -> H
  
  mul(I(x), y) -> add(x, O(mul(x,y)))
  mul(O(x), y) -> O(mul(x, y))
  mul(H, y) -> y

  add(var(k,x), var(l,x)) -> var(+(k,l), x)
  add(var(k,x), add(var(l,x),y)) -> add(var(+(k,l),x), y)
  add(cst(k), cst(l)) -> cst(+(k,l))
  add(cst(k), add(cst(l), y)) -> add(cst(+(k,l)), y)
  add(cst(Z0), x) -> x
  add(x, cst(Z0)) -> x
)
***********/

require open Stdlib.Nat Stdlib.Z Stdlib.List;

notation ≥ infix 10;

constant symbol R : TYPE;
constant symbol ring: Set;
rule τ ring ↪ R;

constant symbol cst: ℤ → R;

symbol var : ℤ → ℤ → R;
/* semantics: [var k x] = k * x
note that the second argument could be any type that has a ring structure
(we then would take R : TYPE → TYPE) */
symbol opp:R → R;
right associative commutative symbol add:R → R → R;
symbol mul: ℤ → R → R;

symbol R_ind: Π p: (R → Prop), 
  (Π x0: ℤ, π ( p (cst x0))) →
  (Π x0: R, π ( p (opp x0))) →
  (Π x0: ℤ, Π y0: ℤ, π (p (var x0 y0))) →
  (Π x0: R, Π y0: R, π (p (add x0 y0))) →
  (Π x0: ℤ, Π y0: R, π (p (mul x0 y0))) →
  π (`∀ x: R, p x);


rule opp (var $k $x) ↪ var (— $k) $x 
with opp (cst $k) ↪ cst (— $k)
with opp (opp $x) ↪ $x
with opp (add $x $y) ↪ add (opp $x) (opp $y)
// // // note that opp is totally defined on terms built with var, cst, opp and add, i.e. no normal form contains opp
with add (var $k $x) (var $c $x) ↪ var ($k + $c) $x
with add (var $k $x) (add (var $l $x) $y) ↪ add (var ($k + $l) $x) $y
with add (cst $k) (cst $l) ↪ cst ($k + $l)
with add (cst $k) (add (cst $l) $y) ↪ add (cst ($k + $l)) $y
with add (cst 0) $x ↪ $x
with add $x (cst 0) ↪ $x

//multiplication by a constant (optional)
with mul $k (var $c $x) ↪ var ($k * $c) $x
with mul $k (opp $r) ↪ mul (— $k) $r
with mul $k (add $r $s) ↪ add (mul $k $r) (mul $k $s)
with mul $k (cst $z) ↪ cst ($k * $z)
with mul $k (mul $l $z) ↪ mul ($k * $l) $z

with var _ 0 ↪ cst 0;
// // note that mul is totally defined on terms built from var, cst, opp, add and mul, i.e. no normal form contains mul

// // reification
// // WARNING: this symbol is declared as sequential
// // and the reduction relation is not stable by substitution
sequential symbol reify : ℤ → R;
rule reify 0 ↪ cst 0
with reify (Zpos $x) ↪ cst (Zpos $x)
with reify (Zneg $x) ↪ cst (Zneg $x)
with reify (— $x) ↪ opp (reify $x)
with reify ($x + $y) ↪ add (reify $x) (reify $y)

with reify (0 * $y) ↪ mul 0 (reify $y)
with reify (Zpos $x * $y) ↪ mul (Zpos $x) (reify $y)
with reify (Zneg $x * $y) ↪ mul (Zneg $x) (reify $y)
with reify ($y * 0) ↪ mul 0 (reify $y)
with reify ($y * Zpos $x) ↪ mul (Zpos $x) (reify $y)
with reify ($y * Zneg $x) ↪ mul (Zneg $x) (reify $y)

with reify $x ↪ var 1 $x; // must be the last rule for reify

print eq_refl;

// eval function
symbol denote: R → ℤ;
rule denote (var $k $i) ↪ $k * $i
with denote (cst $k) ↪ $k
with denote (opp $x) ↪ — (denote $x)
with denote (add $x $y) ↪ (denote $x) + (denote $y)
;

// Lemma Zle_not_gt n m : n <= m -> — n > m.
symbol Zle_not_gt n m:  π ((n ≤ m) = ¬ (n > m));

symbol Zlt_not_ge n m:  π ((n < m) = ¬ (n ≥ m));

symbol Zge_not_lt : Π n: ℤ, Π m: ℤ, π ((n ≥ m) = ¬ (n < m));

symbol Zgt_not_le : Π n: ℤ, Π m: ℤ, π ((n > m) = ¬ (n ≤ m));

// Lemma Zmult_gt_compat_r n m p : p > 0 -> n > m -> n * p > m * p.
symbol Zmult_gt_compat c a b : π (c > 0) → π (a > b) → π (c * a > c * b) ;

// Lemma Zmult_ge_compat_r n m p : n >= m -> p >= 0 -> n * p >= m * p.
symbol Zmult_ge_compat c a b : π (c > 0) → π (a ≥ b) → π (c * a ≥ c * b);

symbol Zgt_le_succ_r a b: π (a > b) → π (a ≥ b + 1);

symbol Zinv_lt a b: π (a < b) → π (— a > — b);

symbol Zsum_geq_s a b c d : π (a ≥ b) → π (c ≥ d) → π (a + c ≥ b + d);

symbol Z_diff_geq_Z0 a b: π (a ≥ b) → π (a - b ≥ 0);
symbol Z_diff_gt_Z0 a b: π (a > b) → π (a - b > 0);



opaque symbol neutral_H_* a : π (Zpos H * a = a) ≔
begin
induction
{ reflexivity }
{ reflexivity }
{ reflexivity }
end;

symbol ind_𝔹 x : Π p0: (𝔹 → Prop), π (p0 true) → π (p0 false) → π (p0 x);

opaque symbol ∨_istrue [p q] : π (istrue (p Stdlib.Bool.or q)) → π (istrue p ∨ istrue q) ≔
begin
admit
end;

symbol ind_Comp x : Π p0: (Comp → Prop), π (p0 Eq) → π (p0 Lt) → π (p0 Gt) → π (p0 x);

symbol Zgt_le_succ_r_eq a b: π ((a > b) = (a ≥ b + 1));

symbol Zinv_lt_eq a b: π ((a < b) = (— a > — b));

symbol Zinv_le_eq a b: π ((a ≤ b) = (— a ≥ — b));

symbol Z_diff_geq_Z0_eq a b: π ((a ≥ b) = (a - b ≥ 0));

symbol Z_diff_gt_Z0_eq a b: π ((a > b) = (a - b > 0));

symbol Z_diff_eq_Z0_eq a b: π ((a = b) = (a - b = 0));

//Axioms
symbol Z_eq_antisym (a b: τ int):  π ((¬ (a = b)) = ¬ (a ≥ b));

symbol Z_eq_implies_ge [a b: τ int]:  π (a = b) →  π (a ≥ b);

symbol Zmult_eq_compat_eq (c a b: τ int) : π ((¬ (a = b)) = ¬ (c * a = c * b));
symbol Zmult_gt_compat_eq c a b : π (¬ (a > b) = ¬ (c * a > c * b)) ;
symbol Zmult_ge_compat_eq c a b : π (¬ (a ≥ b) = ¬ (c * a ≥ c * b)) ;

symbol la_mult_neg_eq [t1 t2 t3] : π ((t1 < 0) ⇒ (t2 = t3) ⇒ (t1 * t2) = (t1 * t3)) ≔
begin
  assume t1 t2 t3; assume H H2; rewrite H2; reflexivity
end;

//FIXME: give proof
symbol la_mult_neg_lt t1 t2 t3 : π (t1 < 0) → π (t2 < t3) → π ((t1 * t2) > (t1 * t3));
symbol la_mult_neg_leq [t1 t2 t3] : π ((t1 < 0) ⇒ (t2 ≤ t3) ⇒ (t1 * t2) ≥ (t1 * t3));

symbol ind_ℤ : Π p0: (ℤ → Prop), π (p0 0) → (Π x0: ℙ, π (p0 (Zpos x0))) → (Π x0: ℙ, π (p0 (Zneg x0))) → π (`∀ x, p0 x);

opaque symbol inj2 : π (`∀ x, (denote (reify x)) = x) ≔ begin
induction
{reflexivity}
{reflexivity}
{reflexivity}
end;

symbol inj: Π x: ℤ, π ((denote (reify  x)) = x);
