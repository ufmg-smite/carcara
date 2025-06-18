require Stdlib.Nat as Nat;
open Stdlib.Nat;
require open Stdlib.Z;
require open lambdapi.Lia;

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

opaque symbol split_correct l gs : π (val (Add (sum (split gs ₁)) (sum (split gs ₂)) ‚ l) = val (sum gs ‚ l)) ≔
begin
assume l;
refine list_ind2_principle (λ u, (val (Add (sum (split u ₁)) (sum (split u ₂)) ‚ l) = val (sum u ‚ l))) _ _ _
{reflexivity}
{reflexivity}
{
  assume a b tl ih;
  simplify;
  rewrite left ih;
  simplify;
  rewrite +_assoc;
  rewrite left .[in x in (_ + x ) = _] +_assoc;
  rewrite +_com (val (sum (split tl ₁) ‚ l)) (val (b ‚ l));
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

opaque symbol merge_correct l g1 g2 : π (no_Add g1) →  π (no_Add g2) →  π (val ( sum (merge  g1 g2) ‚ l ) = val (sum g1 ‚ l) + val (sum g2 ‚ l)) ≔
begin
  assume l;
  induction
  { simplify; reflexivity }
  {
    induction
    {
      assume k g1' IH;
      induction
      {
        assume h_nodaddg1 h_nodaddg2;
        reflexivity;
      }
      {
        induction
        {
          assume k2 g2' IH2 h2 h3;
          simplify;
          rewrite left +_assoc;
          rewrite .[in x in _ = (x + _) ] +_assoc;
          rewrite .[in x in _ = ((_ + x) + _) ] +_com;
          rewrite left .[in x in _ = (x + _) ] +_assoc;
          rewrite IH (g2') _ _ { refine ∧ₑ₂ h2 } { refine ∧ₑ₂ h3 } { rewrite .[in x in _ = x] +_assoc; reflexivity };
        }
        {
          assume i c g2' IH2 hnoadd1 hnoadd2;
          simplify; rewrite IH (Var i c ⸬ g2') _ _ { refine ∧ₑ₂ hnoadd1 } { refine hnoadd2 } { simplify; rewrite +_assoc; reflexivity };
        }
        {
          simplify; assume g1 ih1 g2 ih2 g2' h5 h6 contradiction;
          refine ⊥ₑ (∧ₑ₁ contradiction);
        }
      }
    }
    {
      assume i k1 g1' ih1;
      induction
      { reflexivity; }
      {
        induction
        {
          assume c g2' ih2 hnoadd hnoadd2; simplify;
          rewrite ih2 hnoadd (∧ₑ₂ hnoadd2);
          rewrite left .[in x in _ = x ] +_assoc;
          simplify;
          rewrite .[in x in _ = x + _ ] +_com;
          rewrite  .[in x in _ = x ] +_assoc;
          reflexivity
        }
        {
          assume j k2 g2' ih2 hnoadd1 hnoadd2;
          simplify;
          refine ind_Comp (λ u, (compN i j) = u ⇒ val (sum (case_Comp u (Var i (k1 + k2) ⸬ merge g1' g2') (Var i k1 ⸬ merge g1' (Var j k2 ⸬ g2')) (Var j k2 ⸬ merge (Var i k1 ⸬ g1') g2')) ‚ l) = (((nth l i * k1) + val (sum g1' ‚ l)) + ((nth l j * k2) + val (sum g2' ‚ l)))) _ _ _ (compN i j) _
          {
            simplify; assume hieqj;
            rewrite compN_correct i j hieqj;
            rewrite distr*+; rewrite ih1 g2'  (∧ₑ₂ hnoadd1) (∧ₑ₂ hnoadd2);
            rewrite left .[in x in _ = x ] +_assoc;
            rewrite  .[in x in _ = (x + _) ] +_com;
            rewrite left .[in x in _ = (x + _) ] +_assoc;
            rewrite  +_com (nth l j * k2) (nth l j * k1);
            rewrite .[in x in _ = x ] +_assoc; reflexivity
          }
          {
            simplify; assume hieqj;
            rewrite ih1 (Var j k2 ⸬ g2')  (∧ₑ₂ hnoadd1) hnoadd2;
            simplify; rewrite  +_assoc; reflexivity
          }
          {
            assume hGt;
            simplify;  
            rewrite ih2 hnoadd1 (∧ₑ₂ hnoadd2);
            simplify;
            rewrite left .[ in x in _ = x] +_assoc;
            rewrite .[ in x in _ = (x + _)] +_com;
            rewrite .[ in x in _ = x] +_assoc; reflexivity
          }
          { reflexivity }
        }
        {
          simplify;
          assume x1 ih x2 ih2 g2 h1 hnoadd1 hnoadd2;
          refine ⊥ₑ (∧ₑ₁ hnoadd2 )
        }
      }
    }
    {
      assume g1 ih g2 ih2 g1' h g2' hnoadd1 hnoadd2;
      refine ⊥ₑ (∧ₑ₁ hnoadd1)
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

print 𝕃;

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

opaque symbol mergesort_correct_aux n l g : π (size g Nat.≤ n) →  π (no_Add g) →  π (val ( sum (mergesort g) ‚ l ) = val (sum g ‚ l)) ≔
begin
  //assume n l;
  induction
  {
    assume l;
    assume g h inv;
    type ≤0 (size g) h;
    rewrite size0nil g (≤0 (size g) h);
    reflexivity
  }
  {
    assume n;
    assume ihn l g;
    refine rec_𝕃 g (λ u, istrue (size u Nat.≤ (n +1)) ⇒ (no_Add u ⇒ (val (sum (mergesort u) ‚ l) = val (sum u ‚ l)))) _ _
    {
      assume h1 h2; reflexivity
    }
    {
      assume x g';
      refine rec_𝕃 g' (λ u, istrue (size (x ⸬ u) Nat.≤ (n +1)) ⇒ (no_Add (x ⸬ u) ⇒ (val (sum (mergesort (x ⸬ u)) ‚ l) = val (sum (x ⸬ u) ‚ l)))) _ _
      {
        assume h1 inv; reflexivity;
      }
      {
        assume y g'' inv1 inv2;
        simplify;
        have tmp: π (no_Add (mergesort (x ⸬ (split g'' ₁)))) { admit};
        have tmp2: π (no_Add (mergesort (y ⸬ (split g'' ₂)))) { admit};
        rewrite (merge_correct l (mergesort (x ⸬ ((split g'') ₁))) (mergesort (y ⸬ ((split g'') ₂)))) tmp tmp2;
        type ihn l (x ⸬ (split g'' ₁)) ;
        have tmp3x: π (istrue (size (x ⸬ (split g'' ₁)) Nat.≤ n)) {
          generalize inv1;
          assume inv1 h1 h2 h3;
          apply @leq_trans
          (size (split g'' ₁) +1)
          (size g'' +1)
          n
          _
          inv1;
          apply size_split g''
        };
        have tmp4x: π (no_Add (x ⸬ (split g'' ₁))) {admit};
        rewrite ihn l (x ⸬ (split g'' ₁)) tmp3x tmp4x;
        have tmp3y: π (istrue (size (y ⸬ (split g'' ₂)) Nat.≤ n)) {
          generalize inv1;
          simplify;
          assume  inv1 h1 h2 h3 h4 h5;
          apply @leq_trans
          (size (split g'' ₂) +1)
          (size g'' +1)
          n
          _
          inv1;
          simplify;
          apply size_split2 g''
        };
        have tmp4y: π (no_Add (y ⸬ (split g'' ₂))) {admit};
        rewrite ihn l (y ⸬ (split g'' ₂)) tmp3y tmp4y;
        simplify;
        rewrite +_assoc;
        refine @feq2 int int int (+) (val (x ‚ l)) (val (x ‚ l)) (eq_refl (val (x ‚ l)))
        (val (sum (split g'' ₁) ‚ l) + (val (y ‚ l) + val (sum (split g'' ₂) ‚ l)))
        (val (y ‚ l) + val (sum g'' ‚ l)) _
        ;
        rewrite left +_assoc;
        rewrite .[in x in (x + _) = _ ] +_com;
        rewrite  +_assoc;
        refine @feq2 int int int (+) (val (y ‚ l)) (val (y ‚ l)) (eq_refl (val (y ‚ l)))
        (val (sum (split g'' ₁) ‚ l) + val (sum (split g'' ₂) ‚ l))
        (val (sum g'' ‚ l))
        _
        ;
        apply split_correct l g''     
      }
    };
  }
end;

symbol mergesort_correct l g ≔ mergesort_correct_aux (size g) l g (Nat.≤_refl (size g));

compute mergesort ((Var Nat._3 2) ⸬ (Var Nat._2 2) ⸬ (Var Nat._1 2) ⸬ Cst 10 ⸬ □);

symbol norm_speed x ≔ sum (remove0 (mergesort (aliens x)));


opaque symbol no_Add_mergesort xs : π(no_Add xs) → π(no_Add (mergesort xs)) ≔
begin
admitted;

opaque symbol norm_with_mergesort_correct (x: G) l :
  π(varmax x Nat.≤ size l) → π(val(norm_speed x ‚ l) = val(x ‚ l)) ≔
begin
assume x l h; simplify; apply eq_trans (val (sum (remove0 (mergesort (aliens x))) ‚ l)) (val (sum (mergesort (aliens x)) ‚ l)) (val (x ‚ l))
{ apply remove0_correct l (mergesort(aliens x));
  apply no_Add_mergesort (aliens x); apply no_Add_aliens x }
{ apply eq_trans (val (sum (mergesort (aliens x)) ‚ l)) (val (sum (aliens x) ‚ l)) (val (x ‚ l))
  { apply mergesort_correct l (aliens x);
    apply no_Add_aliens x }
  { apply aliens_correct l x}
}
end;

symbol l1 x y : π((x + y) - (x + y) ≠ 1) ≔
begin
  assume x y;
  refine ≐_decides_neq _;
  rewrite left .[z in z ≐ _] reify_correct;
  set e ≔ reify ((x + y) - (x + y));
  rewrite .[z in val z] eta_prod;
  rewrite left norm_with_mergesort_correct (e ₁) (e ₂) _ { refine ⊤ᵢ } { refine Lt≠Eq }
end;