require Stdlib.Nat as Nat;
open Stdlib.Nat;
require open Stdlib.Z;
require open Stdlib.List;

symbol pos2nat : ℙ → ℕ;
rule pos2nat H ↪  Stdlib.Nat._1
with pos2nat (O $p) ↪ Stdlib.Nat.double (pos2nat $p)
with pos2nat (I $p)  ↪ (Stdlib.Nat.double (pos2nat $p)) Stdlib.Nat.+ Stdlib.Nat._1;

symbol int2nat n : π (0 < (n + 1)) → ℕ;
rule int2nat Z0 _  ↪ Stdlib.Nat._0
with int2nat (Zpos $n) _  ↪ pos2nat $n;

inductive G: TYPE ≔
| Cst: ℤ → G
| Var: ℕ → ℤ → G
;

symbol rec_G : Π p0: (G → Prop), (Π x0: ℤ, π (p0 (Cst x0))) → (Π x0: ℕ, Π x2: ℤ, π (p0 (Var x0 x2))) → Π x: G, π (p0 x);

constant symbol grp : Set;
rule τ grp ↪ G;

// multiplication by a constant

symbol mul: ℤ → 𝕃 grp → 𝕃 grp;

rule mul $k ((Cst $l) ⸬ $xs) ↪ Cst ($k * $l) ⸬ (mul $k $xs)
with mul $k ((Var $i $l) ⸬ $xs) ↪ Var $i ($k * $l) ⸬ (mul $k $xs)
with mul _ □ ↪ □;

// opposite

symbol opp ≔ mul (— 1);


/* evaluation of an arithmetic expression wrt a list of values for variables

variables with indexes not in the list are interpreted by 0 */

symbol nth ≔ nth 0;

symbol val_grp: τ grp →  𝕃 int → ℤ;
rule val_grp (Cst $k) _ ↪ $k
with val_grp (Var $i $k) $l ↪ (nth $l $i) * $k
;

symbol val: τ(list grp × list int) → ℤ;

rule val (□ ‚ _) ↪ 0
with val (($x ⸬ $xs) ‚ $l) ↪ (val_grp $x $l) + (val ($xs ‚ $l));

symbol va l x ≔ val (x ‚ l);

// some useful type (use inductive instead?)

constant symbol R : TYPE;
constant symbol Index : ℕ → R;
constant symbol New : ℕ → R;

symbol case [a] : R → (ℕ → τ a) → (ℕ → τ a) → τ a;

rule case (Index $i) $f _ ↪ $f $i
with case (New $i) _ $g ↪ $g $i;

/* index of a value in a list: returns New if the value is not
definitionally equivalent to some element of the list */

sequential symbol index: ℕ → Π [a], τ a → τ(list a) → R;

rule index $k _ □ ↪ New $k
with index $k $x ($x ⸬ _) ↪ Index $k
with index $k $x ($y ⸬ $l) ↪ index ($k +1) $x $l;

/* reification: given a Lambdapi term x of type ℤ, compute an
expression in G and a list of values whose evaluation is equal to
x. WARNING: rfy is sequential. */

sequential symbol rfy: τ(list int) → ℤ → τ(list grp × list int);

// addition
rule rfy $l ($x + $y) ↪
  let x ≔ rfy $l $x in let y ≔ rfy (x ₂) $y in ((x ₁) ++ (y ₁)) ‚ (y ₂)

// opposite
with rfy $l (— $x) ↪ let x ≔ rfy $l $x in opp (x ₁) ‚ (x ₂)

// substraction
with rfy $l ($x - $y) ↪ rfy $l ($x + — $y)

// constants
with rfy $l 0 ↪ (Cst 0 ⸬ □) ‚ $l
with rfy $l (Zpos $k) ↪ (Cst (Zpos $k) ⸬ □) ‚ $l
with rfy $l (Zneg $k) ↪ (Cst (Zneg $k) ⸬ □) ‚ $l

// multiplication by a constant
with rfy $l (0 * _) ↪ (Cst 0 ⸬ □) ‚ $l
with rfy $l (Zpos $k * $x) ↪ let x ≔ rfy $l $x in (mul (Zpos $k) (x ₁)) ‚ (x ₂)
with rfy $l (Zneg $k * $x) ↪ let x ≔ rfy $l $x in (mul (Zneg $k) (x ₁)) ‚ (x ₂)
with rfy $l ($x * Zpos $k) ↪ let x ≔ rfy $l $x in (mul (Zpos $k) (x ₁)) ‚ (x ₂)
with rfy $l ($x * Zneg $k) ↪ let x ≔ rfy $l $x in (mul (Zneg $k) (x ₁)) ‚ (x ₂)

//other cases are abstracted by a variable
with rfy $l $x ↪
  case (index _0 $x $l) (λ i, (Var i 1 ⸬ □) ‚ $l) (λ i, (Var i 1 ⸬ □) ‚ ($l ++ ($x ⸬ □)))
;

symbol reify ≔ rfy □;

symbol compN : ℕ → ℕ → Comp;

rule compN _0 _0 ↪ Eq
with compN _0 (_ +1) ↪ Lt
with compN (_ +1) _0 ↪ Gt
with compN ($x +1) ($y +1) ↪ compN $x $y;

symbol compG : G → G → Comp;
rule compG (Var $i $k) (Var $j $k2) ↪ compN $i $j
with compG (Var _ _) (Cst _) ↪ Gt
with compG (Cst _) (Var _ _)  ↪ Lt
with compG (Cst $c1) (Cst $c2)  ↪ $c1 ≐ $c2;


symbol split [a: Set] (l : τ (list a)): τ(list a × list a);
rule split □ ↪ (□ ‚ □)
with split ($x ⸬ □) ↪ (($x ⸬ □) ‚ □)
with split ($x ⸬ $y ⸬ $l) ↪  
    let res ≔  (split $l) in
        ($x ⸬ (res ₁)) ‚ ($y ⸬ (res ₂));

symbol list_ind2_principle [A : Set]  :
  Π (P : τ (list A) → Prop),
    π (P □) →
    (Π (a: τ A), π (P (a ⸬ □))) →
    (Π (a b : τ A) (l : τ (list A)), π (P l) →  π (P (a ⸬ b ⸬ l))) →
    Π (l : τ (list A)), π (P l);

opaque symbol ++_eq_+ l x y : π (val ((x ++ y) ‚ l) =  val (x ‚ l) + val (y ‚ l)) ≔
begin
assume l;
induction
{
  assume y;
  reflexivity
}
{
  assume x xs ih;
  simplify;
  assume y;
  rewrite ih y;
  rewrite +_assoc;
  reflexivity
}
end;

opaque symbol split_correct l gs : π (val (((split gs ₁) ++ (split gs ₂)) ‚ l) = val (gs ‚ l)) ≔
begin
assume l;
refine list_ind2_principle (λ u, (val (((split u ₁) ++ (split u ₂)) ‚ l) = val (u ‚ l))) _ _ _
{reflexivity}
{reflexivity}
{
  assume a b tl ih;
  simplify;
  rewrite left ih;
  rewrite ++_eq_+;
  rewrite ++_eq_+;
  simplify;
  rewrite left .[in x in (_ + x ) = _] +_assoc;
  rewrite  .[in x in (_ + (x + _) ) = _] +_com;
  rewrite .[in x in (_ + x ) = _] +_assoc;
  reflexivity
}
end;


symbol merge  (l1 l2 : τ (list grp)): τ (list grp);
rule merge □ □ ↪ □
with merge □ $l2 ↪ $l2
with merge $l1 □ ↪ $l1
with merge (Cst $c1 ⸬ $l1') (Cst $c2 ⸬ $l2') ↪ (Cst ($c1 + $c2) ⸬ merge $l1' $l2')
with merge (Cst $c ⸬ $l1') (Var $i $k ⸬ $l2') ↪ (Cst $c ⸬ merge $l1' (Var $i $k ⸬ $l2'))
with merge (Var $i $k ⸬ $l1') (Cst $c ⸬ $l2') ↪ (Cst $c ⸬ merge (Var $i $k ⸬ $l1') $l2')
with merge ((Var $i $k1) ⸬ $l1') ((Var $j $k2) ⸬ $l2') ↪
    case_Comp (compN $i $j)
        (Var $i ($k1 + $k2) ⸬ merge $l1' $l2')
        ((Var $i $k1) ⸬ merge $l1' (Var $j $k2 ⸬ $l2'))
        ((Var $j $k2) ⸬ merge (Var $i $k1 ⸬ $l1') $l2')
;

// to be moved to Nat
opaque symbol distr*+ x y z : π(x * (y + z) = x * y + x * z) ≔
begin
admitted;

opaque symbol compN_correct x y : π (compN x y = Eq ⇒ x = y) ≔
begin
induction
{ induction
  {assume h; reflexivity}
  {assume y hy h; apply ⊥ₑ; apply Lt≠Eq h}
}
{ assume x hx; induction
  {assume h; apply ⊥ₑ; apply Gt≠Eq h}
  {assume y hy h; apply feq (+1); apply hx y h }
}
end;

opaque symbol merge_correct l g1 g2 : π (val ((merge  g1 g2) ‚ l ) = val (g1 ‚ l) + val (g2 ‚ l)) ≔
begin
    assume l;
    induction
    { simplify; reflexivity }
    {
      induction
      {
        assume k1 xs ih1;
        induction
        {
          reflexivity
        }
        {
          induction
          {
            assume k2 ys ih2;
            simplify; rewrite ih1;
            rewrite +_assoc;
            rewrite  left .[x in _ + x = _] +_assoc;
            rewrite +_com k2;
            rewrite  .[x in _ + x = _] +_assoc;
            rewrite left +_assoc;
            reflexivity
          }
          {
            assume i k2 ys ih2;
            simplify; rewrite ih1;
            simplify;
            rewrite left +_assoc;
            reflexivity
          }
        }
      }
      {
        assume i k1 xs ih1;
        induction
        {reflexivity}
        {
          induction
          {
            assume K ys ih2;
            simplify;
            rewrite ih2;
            simplify;
            rewrite +_com;
            rewrite +_assoc;
            rewrite +_com K;
            reflexivity
          }
          {
            assume j k2 ys ih2;
            simplify;
            refine ind_Comp (λ u, (compN i j) = u ⇒ val (case_Comp (compN i j) (Var i (k1 + k2) ⸬ merge xs ys) (Var i k1 ⸬ merge xs (Var j k2 ⸬ ys)) (Var j k2 ⸬ merge (Var i k1 ⸬ xs) ys) ‚ l) = (((nth l i * k1) + val (xs ‚ l)) + ((nth l j * k2) + val (ys ‚ l)))) _ _ _ (compN i j) _
            {
              simplify;
              assume heq;
              rewrite heq;
              simplify;
              rewrite compN_correct i j heq;
              rewrite distr*+;
              rewrite ih1;
              rewrite +_assoc;              
              set XS ≔ val (xs ‚ l);
              set YS ≔ val (ys ‚ l);
              rewrite  left .[x in _ + x = _] +_assoc;
              rewrite .[x in _ + (x + _) = _] +_com; 
              rewrite .[x in _ + x = _] +_assoc;
              rewrite left .[x in x = _] +_assoc;
              reflexivity
            }
            {
              simplify;
              assume hlt;
              rewrite hlt;
              simplify;
              rewrite ih1;
              simplify;
              rewrite +_assoc;
              rewrite left +_assoc;
              reflexivity
            }
            {
              assume hgt;
              rewrite hgt;
              simplify;
              rewrite ih2;
              simplify;
              rewrite +_com;
              rewrite +_assoc;
              rewrite +_com (val (ys ‚ l));
              reflexivity
            }
            {reflexivity}
          }
        }
      }  
  }
end;


symbol mergesort:  τ (list grp) →  τ (list grp);
rule mergesort □ ↪ □
with mergesort ($x ⸬ □) ↪ ($x ⸬ □)
with mergesort ($x ⸬ $y ⸬ $l) ↪ 
    let s ≔ split ($x ⸬ $y ⸬ $l) in
    let l1 ≔ s ₁ in
    let l2 ≔ s ₂ in
        merge (mergesort l1) (mergesort l2);


      

// print 𝕃;

opaque symbol rec_𝕃 : Π [a: Set], Π l: 𝕃 a, Π p: (𝕃 a → Prop), π (p □) → (Π x0: τ a, Π l': 𝕃 a, π (p (x0 ⸬ l'))) → π (p l) ≔ 
begin
  assume a l P H1 H2;
  refine @ind_𝕃 a P H1 (λ x l' ih, H2 x l') l
end;

opaque symbol case_l [a] x (l: 𝕃 a) n : π ((size (x ⸬ l)) Nat.≤ (n +1)) → π (size l Nat.≤ n) ≔
begin
  assume a x l n;
  refine λ x, x;
end;

opaque symbol size_split [a] (l: 𝕃 a) : π (size ((split l) ₁) Nat.≤ size l) ≔
begin
  assume a;
  refine list_ind2_principle (λ u, istrue (size (split u ₁) Nat.≤ size u)) _ _ _
  {apply ⊤ᵢ}
  {assume y; apply ⊤ᵢ}
  {
    simplify;
    assume x y l ih;
    apply @leq_trans (size (split l ₁)) (size l) (size l +1) ih _;
    refine leqnSn (size l)
  }
end;

opaque symbol size_split2 [a] (l: 𝕃 a) : π (size ((split l) ₂) Nat.≤ size l) ≔
begin
  assume a;
  refine list_ind2_principle (λ u, istrue (size (split u ₂) Nat.≤ size u)) _ _ _
  {apply ⊤ᵢ}
  {assume y; apply ⊤ᵢ}
  {
    simplify;
    assume x y l ih;
    apply @leq_trans (size (split l ₂)) (size l) (size l +1) ih _;
    refine leqnSn (size l)
  }
end;

opaque symbol mergesort_correct_aux n l g : π (size g Nat.≤ n)  →  π (val ((mergesort g) ‚ l ) = val ( g ‚ l)) ≔
begin
    induction
    {
        assume l;
        assume g h;
        type ≤0 (size g) h;
        rewrite size0nil g (≤0 (size g) h);
        reflexivity
    }
    {
      assume n ihn l g;
      refine rec_𝕃 g (λ u, (size u Nat.≤ (n +1)) ⇒ ((val ( (mergesort u) ‚ l) = val ( u ‚ l)))) _ _
      {
        simplify;
        reflexivity
      }
      {
        assume x g';
        refine rec_𝕃 g' (λ u, (size (x ⸬ u) Nat.≤ (n +1)) ⇒ ((val ( (mergesort (x ⸬ u)) ‚ l) = val ( (x ⸬ u) ‚ l)))) _ _
        {reflexivity}
        {
          assume y g'' inv1;
          simplify;
          rewrite (merge_correct l (mergesort (x ⸬ ((split g'') ₁))) (mergesort (y ⸬ ((split g'') ₂))));
          have tmp3x: π (istrue (size (x ⸬ (split g'' ₁)) Nat.≤ n)) {
            apply @leq_trans
            (size (split g'' ₁) +1)
            (size g'' +1)
            n
            _
            inv1;
            apply size_split g''
          };
          rewrite ihn l (x ⸬ (split g'' ₁)) tmp3x;
          have tmp3y: π (istrue (size (y ⸬ (split g'' ₂)) Nat.≤ n)) {
            simplify;
            apply @leq_trans
            (size (split g'' ₂) +1)
            (size g'' +1)
            n
            _
            inv1;
            simplify;
            apply size_split2 g''
          };
          rewrite ihn l (y ⸬ (split g'' ₂)) tmp3y;
          simplify;
          rewrite +_assoc;
          rewrite left .[x in (_ + x) = _] +_assoc;
          rewrite +_com  (val ((split g'' ₁) ‚ l)) (val_grp y l);
          rewrite  +_assoc;
          rewrite left ++_eq_+ l (split g'' ₁) (split g'' ₂);
          rewrite split_correct;
          reflexivity
        }
      }
    }
end;

symbol mergesort_correct l g ≔ mergesort_correct_aux (size g) l g (Nat.≤_refl (size g));

symbol remove0 : τ(list grp) → τ(list grp);

rule remove0 □ ↪ □
with remove0 (Cst 0 ⸬ $l) ↪ remove0 $l
with remove0 (Cst (Zpos $k) ⸬ $l) ↪ Cst (Zpos $k) ⸬ remove0 $l
with remove0 (Cst (Zneg $k) ⸬ $l) ↪ Cst (Zneg $k) ⸬ remove0 $l
with remove0 (Var _ 0 ⸬ $l) ↪ remove0 $l
with remove0 (Var $i (Zpos $k) ⸬ $l) ↪ Var $i (Zpos $k) ⸬ remove0 $l
with remove0 (Var $i (Zneg $k) ⸬ $l) ↪ Var $i (Zneg $k) ⸬ remove0 $l
;

opaque symbol remove0_correct l gs : π (val ((remove0 gs) ‚ l) = val (gs ‚ l)) ≔
begin
  assume l;
  induction // on l
  {
    reflexivity
  }
  {
    induction // on g
    {
      // Case Cst k
      induction 
      // Case Z0
      { assume  gs ih;  simplify; apply ih }
      // Case Zpos
      { assume c gs ih; simplify; rewrite ih; reflexivity }
      // Case Zneg
      { assume c gs ih; simplify;  rewrite ih; reflexivity }
    }
    {
      // Case Var i k
      assume i;
      induction // on k
      {assume gs ih; simplify; rewrite ih; reflexivity} // Case Z0
      { assume c gs ih; simplify; rewrite ih; reflexivity } // Case Zpos
      { assume c gs ih; simplify; rewrite ih; reflexivity } // Case Zneg
    }
  }
end;

//compute mergesort ((Var Nat._3 2) ⸬ (Var Nat._2 2) ⸬ (Var Nat._1 2) ⸬ Cst 10 ⸬ □);

symbol norm_speed x ≔ (remove0 (mergesort x));

symbol varmax : 𝕃 grp → ℕ;

rule varmax ((Cst _) ⸬ $xs) ↪ (varmax $xs)
with varmax ((Var $k _) ⸬ $xs) ↪ max $k (varmax $xs)
with varmax □ ↪ _0;

opaque symbol eq_trans [a] (x y z:τ a) : π(x = y ⇒ y = z ⇒ x = z) ≔
begin
assume a x y z xy yz; rewrite xy; refine yz
end;

opaque symbol norm_correct (x: 𝕃 grp) l : π(val((norm_speed x) ‚ l) = val(x ‚ l)) ≔
begin
  assume x l; simplify; apply eq_trans (val (remove0 (mergesort x) ‚ l)) (val (mergesort x ‚ l)) (val (x ‚ l))
  { apply remove0_correct l (mergesort x) }
  {
    apply eq_trans (val ((mergesort (x)) ‚ l)) (val (( x) ‚ l)) (val (x ‚ l))
    {apply mergesort_correct l x}
    {reflexivity}
  }
end;

symbol ≐_decides_neq [x y] : π (x ≐ y ≠ Eq ⇒ x ≠ y) ≔
begin
assume x y h h2;
apply h;
rewrite h2;
remove h; remove h2; remove x;
generalize y;
induction
{reflexivity}
{
  induction
  {assume x ih; simplify; rewrite left .[x in _ = x] ih; simplify; reflexivity }
  {assume x ih; simplify; rewrite left .[x in _ = x] ih; simplify; reflexivity }
  {reflexivity}
}
{
  induction
  {assume x ih; simplify; rewrite left .[x in _ = x] ih; simplify; reflexivity }
  {assume x ih; simplify; rewrite left .[x in _ = x] ih; simplify; reflexivity }
  {reflexivity}
}
end;

opaque symbol reify_correct x: π(val(reify x) = x) ≔
begin
induction
{reflexivity}
{reflexivity}
{reflexivity}
end;

opaque symbol reify_correct_withenv l x: π(val(rfy l x) = x) ≔
begin
assume l;
induction
{reflexivity}
{reflexivity}
{reflexivity}
end;

symbol eta_prod [a b] (x:τ(a × b)): π(x = (x ₁) ‚ (x ₂));

// symbol l1 x y : π(((2 * x) + y) - ((2 * x) + y) ≠ 1) ≔
// begin
//   assume x y;
//   refine ≐_decides_neq _;
//   rewrite left .[z in z ≐ _] reify_correct;
//   set e ≔ reify (((2 * x) + y) - ((2 * x) + y));
//   rewrite .[z in val z] eta_prod;
//   rewrite left norm_correct (e ₁) (e ₂);
//   refine Lt≠Eq
// end;


require open Stdlib.PropExt;

symbol Zle_not_gt n m:  π ((n ≤ m) = ¬ (n > m)) ≔
begin
assume n m;
rewrite left iff_equiv_eq;
apply ∧ᵢ
{
  simplify;
  assume h;
  change π (¬ ¬ ¬ istrue (isGt (n ≐ m)));
  rewrite ¬¬ₑ_eq;
  refine h
}
{
  simplify;
  assume h1 h2;
  apply h1;
  change π (¬ ¬ istrue (isGt (n ≐ m)));
  rewrite ¬¬ₑ_eq;
  refine h2
}
end;

symbol Zlt_not_ge n m:  π ((n < m) = ¬ (n ≥ m)) ≔
begin
  assume n m;
  simplify ≥;
  simplify rule off;
  rewrite ¬¬ₑ_eq;
  reflexivity
end;

symbol Zge_not_lt : Π n: ℤ, Π m: ℤ, π ((n ≥ m) = ¬ (n < m)) ≔
begin
  assume n m;
  simplify ≥;
  simplify rule off;
  reflexivity
end;

symbol Zgt_not_le : Π n: ℤ, Π m: ℤ, π ((n > m) = ¬ (n ≤ m)) ≔
begin
  assume n m;
  simplify ≤;
  simplify rule off;
  reflexivity
end;

symbol Zmult_gt_compat c a b : π (c > 0) → π (a > b) → π (c * a > c * b) ;

symbol Zmult_ge_compat c a b : π (c > 0) → π (a ≥ b) → π (c * a ≥ c * b);

symbol Zsum_geq_s a b c d : π (a ≥ b) → π (c ≥ d) → π (a + c ≥ b + d) ≔
begin
  assume a b c d hab hcd;
  admit
end;

symbol Zgt_le_succ_r_eq a b: π ((a > b) = (a ≥ b + 1)) ≔
begin
  assume a b;
  simplify >;
  simplify rule off;
  simplify ≥;
  simplify rule off;
  refine feq (¬) _;
  rewrite left iff_equiv_eq;
  apply ∧ᵢ
  { admit}
  { admit }
end;


symbol Zinv_lt_eq a b: π ((a < b) = (— a > — b)) ≔
begin
  assume a b; rewrite left iff_equiv_eq; generalize a;
  admit
end;


symbol Zinv_le_eq a b: π ((a ≤ b) = (— a ≥ — b));
symbol Z_diff_geq_Z0_eq a b: π ((a ≥ b) = (a - b ≥ 0));
symbol Z_diff_gt_Z0_eq a b: π ((a > b) = (a - b > 0));

symbol Z_diff_eq_Z0_eq a b: π ((a = b) = (a - b = 0)) ≔
begin
  assume a b;
  rewrite left iff_equiv_eq;
  apply ∧ᵢ
  {
    assume h; rewrite h; simplify;
    apply -_same b;
  }
  {
      assume h;
      have g: π (((a - b) + b) = (0 + b)) { refine =_add_compat (a - b) 0 b h };
      have g2: π ((a + (— b + b)) = b) { rewrite left +_assoc; refine g };
      have g3: π ((a + 0) = b) { rewrite left -_same b; rewrite +_com b (— b); refine g2 };
      refine g3
    }
end;

//FIXME:
symbol Z_eq_antisym (a b: τ int):  π ((¬ (a = b)) = ¬ (a ≥ b));

symbol Zmult_eq_compat_eq (c a b: τ int) : π ((¬ (a = b)) = ¬ (c * a = c * b)) ≔
begin
 assume c a b;
 apply feq (¬);
 rewrite left iff_equiv_eq;
 apply ∧ᵢ
  { assume heq; rewrite heq; reflexivity }
  {
    assume h;
    have g2: π ((c * a) - (c * b) = 0) { rewrite h; simplify;  rewrite -_same (c * b); reflexivity };
    have g3: π (c * (a - b) = 0) { simplify;  rewrite *_distr_+; rewrite left neg_mul_r; refine g2 };
    admit
  }
end;

symbol Zmult_gt_compat_eq c a b : π (¬ (a > b) = ¬ (c * a > c * b)) ;
symbol Zmult_ge_compat_eq c a b : π (¬ (a ≥ b) = ¬ (c * a ≥ c * b)) ;

// symbol la_mult_neg_eq [t1 t2 t3] : π ((t1 < 0) ⇒ (t2 = t3) ⇒ (t1 * t2) = (t1 * t3));
// symbol la_mult_neg_lt t1 t2 t3 : π (t1 < 0) → π (t2 < t3) → π ((t1 * t2) > (t1 * t3));
// symbol la_mult_neg_leq [t1 t2 t3] : π ((t1 < 0) ⇒ (t2 ≤ t3) ⇒ (t1 * t2) ≥ (t1 * t3));
// symbol la_mult_neg_gt [t1 t2 t3] : π ((t1 < 0) ⇒ (t2 > t3) ⇒ (t1 * t2) < (t1 * t3));
// symbol la_mult_neg_ge [t1 t2 t3] : π ((t1 < 0) ⇒ (t2 ≥ t3) ⇒ (t1 * t2) ≤ (t1 * t3));

symbol foo (X : τ int) :  π ((— _1 * (— _1 + X)) = (_1 + (— _1 * X))) ≔
begin
  assume X;
  rewrite left  .[x in x = _] reify_correct;
  rewrite left  .[x in _ = x] reify_correct;
  set l ≔ (reify ((— 1) * ((— 1) + (X))));
  set r ≔ (reify (1 + ((— 1) * (X))));
  rewrite .[x in val x = _] eta_prod;
  rewrite .[x in _ = val x] eta_prod;
  rewrite left  norm_correct ((l ₁)) ((l ₂));
  rewrite left  norm_correct ((r ₁)) ((r ₂));
  reflexivity
end;
