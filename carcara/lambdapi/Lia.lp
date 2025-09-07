require Stdlib.Nat as Nat;
open Stdlib.Nat;
require open Stdlib.Z Stdlib.List Stdlib.propExt;

// type for arithmetic expressions

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
| Add: G → G → G
; 

constant symbol grp : Set;
rule τ grp ↪ G;

// multiplication by a constant

symbol mul: ℤ → G → G;

rule mul $k (Cst $l) ↪ Cst ($k * $l)
with mul $k (Var $i $l) ↪ Var $i ($k * $l)
with mul $k (Add $x $y) ↪ Add (mul $k $x) (mul $k $y);

// opposite

symbol opp ≔ mul (— 1);

// highest variable index in a term

symbol varmax : G → ℕ;

rule varmax (Cst _) ↪ _0
with varmax (Var $k _) ↪ $k
with varmax (Add $x $y) ↪ max (varmax $x) (varmax $y);

/* evaluation of an arithmetic expression wrt a list of values for variables

variables with indexes not in the list are interpreted by 0 */

symbol nth ≔ Stdlib.List.nth 0;

symbol val: τ(grp × list int) → ℤ;

rule val (Cst $k ‚ _) ↪ $k
with val (Var $i $k ‚ $l) ↪ (nth $l $i) * $k
with val (Add $x $y ‚ $l) ↪ val ($x ‚ $l) + val ($y ‚ $l);

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

sequential symbol rfy: τ(list int) → ℤ → τ(grp × list int);

// addition
rule rfy $l ($x + $y) ↪
  let x ≔ rfy $l $x in let y ≔ rfy (x ₂) $y in Add (x ₁) (y ₁) ‚ (y ₂)

// opposite
with rfy $l (— $x) ↪ let x ≔ rfy $l $x in opp (x ₁) ‚ (x ₂)

// substraction
with rfy $l ($x - $y) ↪ rfy $l ($x + — $y)

// constants
with rfy $l 0 ↪ Cst 0 ‚ $l
with rfy $l (Zpos $k) ↪ Cst (Zpos $k) ‚ $l
with rfy $l (Zneg $k) ↪ Cst (Zneg $k) ‚ $l

// multiplication by a constant
with rfy $l (0 * _) ↪ Cst 0 ‚ $l
with rfy $l (Zpos $k * $x) ↪ let x ≔ rfy $l $x in mul (Zpos $k) (x ₁) ‚ (x ₂)
with rfy $l (Zneg $k * $x) ↪ let x ≔ rfy $l $x in mul (Zneg $k) (x ₁) ‚ (x ₂)
with rfy $l ($x * Zpos $k) ↪ let x ≔ rfy $l $x in mul (Zpos $k) (x ₁) ‚ (x ₂)
with rfy $l ($x * Zneg $k) ↪ let x ≔ rfy $l $x in mul (Zneg $k) (x ₁) ‚ (x ₂)

// other cases are abstracted by a variable
with rfy $l $x ↪
  case (index _0 $x $l) (λ i, Var i 1 ‚ $l) (λ i, Var i 1 ‚ ($x ⸬ $l))
;

symbol reify ≔ rfy □;

opaque symbol reify_correct x: π(val(reify x) = x) ≔
begin
induction
{reflexivity}
{reflexivity}
{reflexivity}
end;

// aliens (constants and variables) of an arithmetic expression

symbol aliens: G → τ(list grp);

rule aliens (Cst $k) ↪ Cst $k ⸬ □
with aliens (Var $i $k) ↪ Var $i $k ⸬ □
with aliens (Add $x $y) ↪ aliens $x ++ aliens $y;

symbol isNotAdd: τ grp → Prop; //FIXME: replace Prop by 𝔹

rule isNotAdd (Cst _) ↪ ⊤
with isNotAdd (Var _ _ ) ↪ ⊤
with isNotAdd (Add _ _ ) ↪ ⊥;

symbol no_Add : τ(list grp) → Prop;

rule no_Add □ ↪ ⊤
with no_Add ($g ⸬ $gs) ↪  isNotAdd $g ∧ no_Add $gs;

opaque symbol no_Add_++ ys xs : π(no_Add xs ⇒ no_Add ys ⇒ no_Add(xs ++ ys)) ≔
begin
assume ys; induction
{assume h1 h2; refine h2}
{assume x xs IH h1 h2; simplify; apply ∧ᵢ {refine ∧ₑ₁ h1} {apply IH {refine ∧ₑ₂ h1} {refine h2}}}
end;

opaque symbol no_Add_aliens x : π(no_Add (aliens x)) ≔
begin
induction
{assume k; simplify; apply ∧ᵢ ⊤ᵢ ⊤ᵢ}
{assume i ki; simplify; apply ∧ᵢ ⊤ᵢ ⊤ᵢ}
{assume x hx y hy; simplify; apply no_Add_++ (aliens y) (aliens x) hx hy; }
end;

// ordering of natural numbers
// move to Nat
symbol compN : ℕ → ℕ → Comp;

rule compN _0 _0 ↪ Eq
with compN _0 (_ +1) ↪ Lt
with compN (_ +1) _0 ↪ Gt
with compN ($x +1) ($y +1) ↪ compN $x $y;

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

// normalization of arithmetic expressions

/*
symbol merge : τ(list grp) → τ(list grp);

rule merge □ ↪ □
with merge ($x ⸬ □) ↪ $x ⸬ □
with merge (Cst $k ⸬ Cst $k' ⸬ $l) ↪ merge (Cst ($k + $k') ⸬ $l)
with merge (Cst $k ⸬ Var $i $ki ⸬ $l) ↪ Cst $k ⸬ merge (Var $i $ki ⸬ $l)
with merge (Var $i $ki ⸬ Var $j $kj ⸬ $l) ↪
  case_Comp (compN $i $j)
            (merge (Var $i ($ki + $kj) ⸬ $l))
            (Var $i $ki ⸬ merge (Var $j $kj ⸬ $l))
            (Var $i $ki ⸬ merge (Var $j $kj ⸬ $l))
;
*/

symbol remove0 : τ(list grp) → τ(list grp);

rule remove0 □ ↪ □
with remove0 (Cst 0 ⸬ $l) ↪ remove0 $l
with remove0 (Cst (Zpos $k) ⸬ $l) ↪ Cst (Zpos $k) ⸬ remove0 $l
with remove0 (Cst (Zneg $k) ⸬ $l) ↪ Cst (Zneg $k) ⸬ remove0 $l
with remove0 (Var _ 0 ⸬ $l) ↪ remove0 $l
with remove0 (Var $i (Zpos $k) ⸬ $l) ↪ Var $i (Zpos $k) ⸬ remove0 $l
with remove0 (Var $i (Zneg $k) ⸬ $l) ↪ Var $i (Zneg $k) ⸬ remove0 $l
;

symbol sum: τ(list grp) → τ grp;

rule sum □ ↪ Cst 0
with sum ($x ⸬ $l) ↪ Add $x (sum $l);

symbol vas l xs ≔ va l (sum xs);

opaque symbol remove0_correct l gs : π (no_Add gs) →  π (val (sum (remove0 gs) ‚ l) = val (sum gs ‚ l)) ≔
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
      { assume gs IH H;  apply IH;  refine (∧ₑ₂ H) }
      // Case Zpos
      { assume c gs IH H; simplify; rewrite (IH (∧ₑ₂ H)); reflexivity }
      // Case Zneg
      { assume c gs IH H; simplify;  rewrite (IH (∧ₑ₂ H)); reflexivity }
    }
    {
      // Case Var i k
      assume i;
      induction // on k
      {assume gs IH H;  apply IH; refine (∧ₑ₂ H)} // Case Z0
      { assume c gs IH H; simplify;  rewrite (IH (∧ₑ₂ H)); reflexivity } // Case Zpos
      { assume c gs IH H; simplify;  rewrite (IH (∧ₑ₂ H)); reflexivity } // Case Zneg
    }
    {
      // Case Add g1 g2
      // That violate the invariant: no_Add gs
      simplify;
      assume g1 IHg1 g2 IHg2 gs IHg H;
      refine ⊥ₑ (∧ₑ₁ H)
    }
  }
end;

opaque symbol case_Comp_prop [a] (p:τ a → Prop) eq lt gt c :
  π(p eq ⇒ p lt ⇒ p gt ⇒ p (case_Comp c eq lt gt)) ≔
begin
assume a p eq lt gt; induction
{assume peq plt pgt; refine peq}
{assume peq plt pgt; refine plt}
{assume peq plt pgt; refine pgt}
end;

symbol insert: G → τ(list grp) → τ(list grp);

/*
rule insert (Cst $k) (Cst $k' ⸬ $l) ↪ Cst $k ⸬ Cst $k' ⸬ $l
with insert (Cst $k) (Var $i $k' ⸬ $l) ↪ Cst $k ⸬ Var $i $k' ⸬ $l
with insert (Var $i $k) (Cst $k' ⸬ $l) ↪ Cst $k' ⸬ insert (Var $i $k) $l
with insert (Var $i $ki) (Var $j $kj ⸬ $l) ↪
     case_Comp (compN $i $j)
            (Var $i $ki ⸬ Var $j $kj ⸬ $l)
            (Var $i $ki ⸬ Var $j $kj ⸬ $l)
            (Var $j $kj ⸬ insert (Var $i $ki) $l);
*/

rule insert $x □ ↪ $x ⸬ □
with insert (Cst $k) (Cst $k' ⸬ $l) ↪ Cst ($k + $k') ⸬ $l
with insert (Cst $k) (Var $i $k' ⸬ $l) ↪ Cst $k ⸬ Var $i $k' ⸬ $l
with insert (Var $i $k) (Cst $k' ⸬ $l) ↪ Cst $k' ⸬ insert (Var $i $k) $l
with insert (Var $i $ki) (Var $j $kj ⸬ $l) ↪
     case_Comp (compN $i $j)
            (Var $i ($ki + $kj) ⸬ $l) // Eq
            (Var $i $ki ⸬ Var $j $kj ⸬ $l) // Lt
            (Var $j $kj ⸬ insert (Var $i $ki) $l); // i > j

opaque symbol no_Add_insert xs y : π(isNotAdd y) → π(no_Add xs) → π(no_Add(insert y xs)) ≔
begin
induction
{ assume x h i; simplify; apply ∧ᵢ { refine h } { apply ⊤ᵢ } }
{ induction
  { assume k xs IH; induction
    { assume k' h1 h2; simplify; apply ∧ᵢ {apply ⊤ᵢ} {apply ∧ₑ₂ h2} }
    { assume ki i h1 h2; simplify; apply ∧ᵢ {apply ⊤ᵢ}
      {apply IH (Var ki i) {apply ⊤ᵢ} {apply ∧ₑ₂ h2}} }
    { assume x1 H1 x2 H2 h1 h2; apply ⊥ₑ; refine h1}
  }
  { assume j kj xs IH; induction
    { assume k h1 h2; simplify; apply ∧ᵢ {apply ⊤ᵢ} {apply ∧ᵢ {apply ⊤ᵢ} {apply ∧ₑ₂ h2}}}
    { assume i ki h1 h2; simplify;
      apply case_Comp_prop no_Add (Var i (ki + kj) ⸬ xs) (Var i ki ⸬ (Var j kj ⸬ xs)) (Var j kj ⸬ insert (Var i ki) xs) (compN i j)
         {refine h2}
         {simplify; apply ∧ᵢ {refine ⊤ᵢ}{refine h2}}
         {simplify; apply ∧ᵢ{apply ⊤ᵢ}{apply IH (Var i ki) {apply ⊤ᵢ} {apply ∧ₑ₂ h2}}}
    }
    { assume x1 H1 x2 H2 h1 h2; apply ⊥ₑ; refine h1}
  }
  { assume x1 H1 x2 H2 xs IH y h i; apply ⊥ₑ; refine ∧ₑ₁ i}
}
end;

// to be moved to Nat
opaque symbol distr*+ x y z : π(x * (y + z) = x * y + x * z) ≔
begin
admitted;

symbol insert_correct l gs g : π (no_Add (g ⸬ gs)) → π (val (sum (insert g gs) ‚ l) =  val (g ‚ l) +  val (sum gs ‚ l)) ≔
begin
assume l;
induction
{ reflexivity }
{
  // /assume g' gs IH g Haliens;
  induction
  {
    // Cst k
    assume k gs IH;
    induction
    // Cst k
    { assume k2 H; simplify; rewrite +_assoc; reflexivity }
    // Var i j
    {
      assume i c H;
      simplify;
      have g: π (no_Add (Var i c ⸬ gs)) { 
        apply ∧ᵢ
        { refine ∧ₑ₁ H; }
        { refine ∧ₑ₂ (∧ₑ₂ H); }
       };
      rewrite IH (Var i c) g;
      rewrite left +_assoc k (val (Var i c ‚ l)) (val (sum gs ‚ l));
      rewrite +_com k;
      rewrite +_assoc;
      reflexivity
    }
    // Case Add
    { assume g1 h2 g2 h4 contradiction; refine ⊥ₑ (∧ₑ₁ contradiction) }
  }
  {
    // Case Var i k
    assume i k gs IH;
    induction
    { assume c H; reflexivity }
    {
      assume j k2 Haliens;
      simplify insert;
      refine ind_Comp (λ u, (compN j i) = u ⇒ val (sum (case_Comp u (Var j (k2 + k) ⸬ gs) (Var j k2 ⸬ (Var i k ⸬ gs)) (Var i k ⸬ insert (Var j k2) gs)) ‚ l) = (val (Var j k2 ‚ l) + val (sum (Var i k ⸬ gs) ‚ l))) _ _ _ (compN j i) _
      {
        assume Hi_eq_j;
        simplify case_Comp;
        rewrite compN_correct j i Hi_eq_j;
        simplify; rewrite distr*+; rewrite +_assoc; reflexivity
      }
      {
        assume Hcomp;
        simplify case_Comp;
        reflexivity
      }
      {
        assume Hcomp;
        simplify case_Comp;
        simplify;
        type IH (Var j k2);
        have g: π (no_Add (Var j k2 ⸬ gs)) {
          simplify;
          apply ∧ᵢ
          { refine ∧ₑ₁ Haliens }
          { refine ∧ₑ₂ (∧ₑ₂ Haliens) }
        };
        rewrite IH (Var j k2) g;
        simplify;
        set GS ≔ val (sum gs ‚ l);
        rewrite left +_assoc;
        // rewrite left +_assoc (nth l i * k) (nth l j * k2) (val (sum gs ‚ l));
        rewrite .[x in (x + _) = _] +_com;
        rewrite +_assoc;
        reflexivity
      }
      {reflexivity}
    }
    { assume g IH1 g' IH2 contradiction; refine ⊥ₑ (∧ₑ₁ contradiction) }
  }
  { assume g1  IH g2 IH2 gs H g contradiction; refine ⊥ₑ (∧ₑ₁ (∧ₑ₂ contradiction)); }
}
end;

// to be moved to List
symbol sort: τ(list grp) → τ(list grp);

rule sort □ ↪ □
with sort ($x ⸬ $xs) ↪ insert $x (sort $xs);

opaque symbol no_Add_sort xs : π(no_Add xs) → π(no_Add (sort xs)) ≔
begin
induction
{ assume h; apply ⊤ᵢ }
{ assume x xs IH h; simplify; apply no_Add_insert (sort xs) x
  {refine ∧ₑ₁ h}
  {apply IH; refine ∧ₑ₂ h}
}
end;

opaque symbol sort_correct l gs : π(no_Add gs) → π (val (sum (sort gs) ‚ l) =  val (sum gs ‚ l)) ≔
begin
assume l;
induction
{ assume h; reflexivity }
{ assume g gs IH h;
  have e: π(val (sum (sort gs) ‚ l) = val (sum gs ‚ l))
    { apply IH; apply ∧ₑ₂ h };
  simplify; rewrite left e; apply insert_correct l (sort gs) g;
  simplify; apply ∧ᵢ { apply ∧ₑ₁ h } { apply no_Add_sort gs; apply ∧ₑ₂ h }
}
end;

symbol norm x ≔ sum (remove0 (sort (aliens x)));

// to be moved to Nat
opaque symbol max_leq m n1 n2 :
  π (max n1 n2 Nat.≤ m ⇒ n1 Nat.≤ m ∧ n2 Nat.≤ m) ≔
begin
assume m n1 n2 h; apply ∧ᵢ
{ refine @leq_trans n1 (max n1 n2) m _ _ { apply leq_maxl n1 n2 } { refine h } }
{ refine @leq_trans n2 (max n1 n2) m _ _ { apply leq_maxr n1 n2 } { refine h } }
end;

// moved to Eq
opaque symbol eq_trans [a] (x y z:τ a) : π(x = y ⇒ y = z ⇒ x = z) ≔
begin
assume a x y z xy yz; rewrite xy; refine yz
end;

opaque symbol sum++ l ys xs : π(val(sum(xs ++ ys) ‚ l) = val(sum xs ‚ l) + val(sum ys ‚ l)) ≔
begin
assume l ys; induction
{ reflexivity }
{ assume x xs IH; simplify; rewrite IH; rewrite +_assoc; reflexivity }
end;

opaque symbol aliens_correct l x : π (val (sum (aliens x) ‚ l) = val (x ‚ l)) ≔
begin
assume l; induction
{assume k; reflexivity }
{assume i ki; reflexivity}
{assume x hx y hy; simplify; rewrite sum++; rewrite hx; rewrite hy; reflexivity}
end;

opaque symbol norm_correct (x: G) l :
  π(varmax x Nat.≤ size l) → π(val(norm x ‚ l) = val(x ‚ l)) ≔
begin
assume x l h; simplify; apply eq_trans (val (sum (remove0 (sort (aliens x))) ‚ l)) (val (sum (sort (aliens x)) ‚ l)) (val (x ‚ l))
{ apply remove0_correct l (sort(aliens x));
  apply no_Add_sort (aliens x); apply no_Add_aliens x }
{ apply eq_trans (val (sum (sort (aliens x)) ‚ l)) (val (sum (aliens x) ‚ l)) (val (x ‚ l))
  { apply sort_correct l (aliens x); apply no_Add_aliens x }
  { apply aliens_correct l x}
}
end;

// move to Prod ?
symbol eta_prod [a b] (x:τ(a × b)): π(x = (x ₁) ‚ (x ₂));

// to be moved to Comp
symbol ≐_decides_neq [x y] : π (x ≐ y ≠ Eq ⇒ x ≠ y) ≔
begin
admitted;

symbol l1 x y : π((x + y) - (x + y) ≠ 1) ≔
begin
  assume x y;
  refine ≐_decides_neq _;
  rewrite left .[z in z ≐ _] reify_correct;
  set e ≔ reify ((x + y) - (x + y));
  rewrite .[z in val z] eta_prod;
  compute e;
  rewrite left norm_correct (e ₁) (e ₂) _ { refine ⊤ᵢ } { refine Lt≠Eq }
end;

symbol ≱ : τ int → τ int → Prop ≔ λ x y, ¬ (x ≥ y);
notation ≱ infix 10;

symbol ≐_decides_ngeq [x y] : π (x ≐ y ≠ Gt ∧ x ≐ y ≠ Eq ⇒ x ≱ y) ≔
begin
admitted;

require open Stdlib.propExt;

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

symbol Zlt_not_ge n m:  π ((n < m) = ¬ (n ≥ m));
symbol Zge_not_lt : Π n: ℤ, Π m: ℤ, π ((n ≥ m) = ¬ (n < m));
symbol Zgt_not_le : Π n: ℤ, Π m: ℤ, π ((n > m) = ¬ (n ≤ m));
symbol Zmult_gt_compat c a b : π (c > 0) → π (a > b) → π (c * a > c * b) ;
symbol Zmult_ge_compat c a b : π (c > 0) → π (a ≥ b) → π (c * a ≥ c * b);
symbol Zgt_le_succ_r a b: π (a > b) → π (a ≥ b + 1);
symbol Zinv_lt a b: π (a < b) → π (— a > — b);
symbol Zsum_geq_s a b c d : π (a ≥ b) → π (c ≥ d) → π (a + c ≥ b + d);
symbol Z_diff_geq_Z0 a b: π (a ≥ b) → π (a - b ≥ 0);
symbol Z_diff_gt_Z0 a b: π (a > b) → π (a - b > 0);
symbol Zgt_le_succ_r_eq a b: π ((a > b) = (a ≥ b + 1));
symbol Zinv_lt_eq a b: π ((a < b) = (— a > — b));
symbol Zinv_le_eq a b: π ((a ≤ b) = (— a ≥ — b));
symbol Z_diff_geq_Z0_eq a b: π ((a ≥ b) = (a - b ≥ 0));
symbol Z_diff_gt_Z0_eq a b: π ((a > b) = (a - b > 0));
symbol Z_diff_eq_Z0_eq a b: π ((a = b) = (a - b = 0));
symbol Z_eq_antisym (a b: τ int):  π ((¬ (a = b)) = ¬ (a ≥ b));
symbol Zmult_eq_compat_eq (c a b: τ int) : π ((¬ (a = b)) = ¬ (c * a = c * b));
symbol Zmult_gt_compat_eq c a b : π (¬ (a > b) = ¬ (c * a > c * b)) ;
symbol Zmult_ge_compat_eq c a b : π (¬ (a ≥ b) = ¬ (c * a ≥ c * b)) ;
symbol la_mult_neg_eq [t1 t2 t3] : π ((t1 < 0) ⇒ (t2 = t3) ⇒ (t1 * t2) = (t1 * t3));
symbol la_mult_neg_lt t1 t2 t3 : π (t1 < 0) → π (t2 < t3) → π ((t1 * t2) > (t1 * t3));
symbol la_mult_neg_leq [t1 t2 t3] : π ((t1 < 0) ⇒ (t2 ≤ t3) ⇒ (t1 * t2) ≥ (t1 * t3));
symbol la_mult_neg_gt [t1 t2 t3] : π ((t1 < 0) ⇒ (t2 > t3) ⇒ (t1 * t2) < (t1 * t3));
symbol la_mult_neg_ge [t1 t2 t3] : π ((t1 < 0) ⇒ (t2 ≥ t3) ⇒ (t1 * t2) ≤ (t1 * t3));
