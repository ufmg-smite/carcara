require open lambdapi.Alethe;
require open Stdlib.Comp;



protected symbol compN : ℕ → ℕ → Comp;

rule compN _0 _0 ↪ Eq
with compN _0 (_ +1) ↪ Lt
with compN (_ +1) _0 ↪ Gt
with compN ($x +1) ($y +1) ↪ compN $x $y;

protected opaque symbol compN_correct x y : π (compN x y = Eq ⇒ x = y) ≔
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

inductive ClauseAlg : TYPE ≔
| p : ℕ → ClauseAlg;

symbol cl : Set;
rule τ cl ↪ ClauseAlg;


symbol compCl : ClauseAlg → ClauseAlg → Comp;
rule compCl (p $i) (p $j) ↪ compN $i $j
;

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


symbol den: 𝕃 o → 𝕃 cl → Prop;
rule den $σ □ ↪ ⊥
with den $σ ((p $i) ⸬ $xs) ↪ (nth ⊥ $σ $i) ∨ (den $σ $xs)
;



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

//compute case (New Stdlib.Nat._0) (λ i, (p i) ‚ (□)) (λ i, (p i) ‚ (⊤ ⸬ □));

symbol rfy_cl: 𝕃 o → Clause → τ (list cl × list o);
rule rfy_cl $l ▩ ↪ (□ ‚ $l)
with rfy_cl $l ($x ⟇ $xs) ↪ 
  let X ≔  case (index 0 $x $l) (λ i, (p i) ‚ $l) (λ i, (p i) ‚ ($l Stdlib.List.++ ($x ⸬ □))) in
  let x ≔ X ₁ in
  let l' ≔ X ₂ in
  let xs ≔ rfy_cl l' $xs in
    ((x ⸬ (xs ₁)) ‚ (xs ₂));

symbol reify_cl ≔ rfy_cl □;

symbol a: Prop;
symbol b: Prop;

compute reify_cl (a ⟇ b ⟇ ▩);

compute  den ((reify_cl (a ⟇ b ⟇ ▩)) ₂) ((reify_cl (a ⟇ b ⟇ ▩)) ₁);

assert a b ⊢ reify_cl (a ⟇ b ⟇ ▩) ≡ (((p 0) ⸬ (p 1) ⸬ □) ‚ (a ⸬ b ⸬ □));

assert a b ⊢ den ((reify_cl (a ⟇ b ⟇ ▩)) ₂) ((reify_cl (a ⟇ b ⟇ ▩)) ₁) ≡  ⟇_to_∨_rw (a ⟇ b ⟇ ▩);

opaque symbol ++_eq_∨ l x y : π ((den l (x Stdlib.List.++ y)) = (den l x ∨ den l y)) ≔
begin
    assume l;
    induction
    {
        assume y;
        simplify;
        rewrite or_identity_l;
        reflexivity
    }
    {
        induction;
        assume i xs ih;
        assume y;
        simplify;
        rewrite ih;
        rewrite ∨_assoc;
        reflexivity
    }
end;

// symbol flat: τ(list cl) → τ cl;

// rule flat □ ↪ Cst 0
// with flat ($x ⸬ $l) ↪ Add $x (sum $l);

opaque symbol split_correct l gs : π (den l ((split gs ₁) Stdlib.List.++ (split gs ₂)) = den l gs) ≔
begin
assume l;
refine list_ind2_principle (λ u, den l ((split u ₁) Stdlib.List.++ (split u ₂)) = den l u) _ _ _
{ reflexivity }
{ reflexivity }
{
    induction;
    assume i;
    induction;
    assume j;
    assume tl ih;
    simplify;
    rewrite left ih;
    rewrite ++_eq_∨;
    rewrite ++_eq_∨;
    simplify;
    rewrite .[in x in (_ ∨ x ) = _] ∨_assoc;
    rewrite .[in x in (_ ∨ (x ∨ _) ) = _] ∨_com;
    rewrite left .[in x in (_ ∨ x ) = _] ∨_assoc;
    reflexivity
}
end;

symbol merge  (l1 l2 : τ (list cl)): τ (list cl);
rule merge □ □ ↪ □
with merge □ $l2 ↪ $l2
with merge $l1 □ ↪ $l1
with merge (p $i ⸬ $l1') (p $j ⸬ $l2') ↪
    case_Comp (compN $i $j)
        (p $i ⸬ p $j ⸬ merge $l1' $l2')
        ((p $i) ⸬ merge $l1' (p $j ⸬ $l2'))
        (p $j ⸬ merge (p $i ⸬ $l1') $l2')
;


opaque symbol merge_correct l g1 g2 :  π (den l (merge  g1 g2) = (den l g1  ∨ den l g2)) ≔
begin
  assume l;
  induction
  {
        simplify; assume g2;
        rewrite or_identity_l; reflexivity
  }
  {
        induction; assume i xs ih;
        induction
        {
            simplify;
            rewrite or_identity_r; reflexivity
        }
        {
            induction;
            assume j ys ih2;
            simplify;
            refine ind_Comp (λ u, (compN i j) = u ⇒  (den l (case_Comp u (p i ⸬ (p j ⸬ merge xs ys)) (p i ⸬ merge xs (p j ⸬ ys)) (p j ⸬ merge (p i ⸬ xs) ys)) = ((nth ⊥ l i ∨ den l xs) ∨ (nth ⊥ l j ∨ den l ys)))) _ _ _ (compN i j) _
            {
                simplify;
                assume heq;
                rewrite ih;
                rewrite left .[x in _ = x] ∨_assoc;
                rewrite  .[x in _ = ( _ ∨ x)] ∨_assoc;
                rewrite ∨_com (den l xs) (nth ⊥ l j);
                rewrite left  .[x in _ = ( _ ∨ x)] ∨_assoc;
                reflexivity
            }
            {
                simplify; assume hlt;
                rewrite ih;
                simplify;
                rewrite ∨_assoc;
                reflexivity
            }
            {
                simplify;
                assume hgt;
                rewrite ih2;
                simplify;
                rewrite .[x in (_ ∨ x) = _] ∨_com;
                rewrite ∨_assoc;
                rewrite ∨_com;
                reflexivity
            }
            {reflexivity}
        }
  }
end;


symbol mergesort:  τ (list cl) →  τ (list cl);
rule mergesort □ ↪ □
with mergesort ($x ⸬ □) ↪ ($x ⸬ □)
with mergesort ($x ⸬ $y ⸬ $l) ↪
    let s ≔ split ($x ⸬ $y ⸬ $l) in
    let l1 ≔ s ₁ in
    let l2 ≔ s ₂ in
        merge (mergesort l1) (mergesort l2);



opaque symbol rec_𝕃 : Π [a: Set], Π l: 𝕃 a, Π p: (𝕃 a → Prop), π (p □) → (Π x0: τ a, Π l': 𝕃 a, π (p (x0 ⸬ l'))) → π (p l) ≔
begin
  assume a l P H1 H2;
  refine @ind_𝕃 a P H1 (λ x l' ih, H2 x l') l
end;

opaque symbol case_l [a] x (l: 𝕃 a) n : π ((size (x ⸬ l)) ≤ (n +1)) → π (size l ≤ n) ≔
begin
  assume a x l n;
  refine λ x, x;
end;

opaque symbol size_split [a] (l: 𝕃 a) : π (size ((split l) ₁) ≤ size l) ≔
begin
  assume a;
  refine list_ind2_principle (λ u, istrue (size (split u ₁) ≤ size u)) _ _ _
  {apply ⊤ᵢ}
  {assume y; apply ⊤ᵢ}
  {
    simplify;
    assume x y l ih;
    apply @leq_trans (size (split l ₁)) (size l) (size l +1) ih _;
    refine leqnSn (size l)
  }
end;

opaque symbol size_split2 [a] (l: 𝕃 a) : π (size ((split l) ₂) ≤ size l) ≔
begin
  assume a;
  refine list_ind2_principle (λ u, istrue (size (split u ₂) ≤ size u)) _ _ _
  {apply ⊤ᵢ}
  {assume y; apply ⊤ᵢ}
  {
    simplify;
    assume x y l ih;
    apply @leq_trans (size (split l ₂)) (size l) (size l +1) ih _;
    refine leqnSn (size l)
  }
end;


opaque symbol mergesort_correct_aux n l g : π (size g ≤ n) →  π (den l (mergesort g) = den l g) ≔
begin
induction
{
    assume l g h;
    rewrite size0nil g (≤0 (size g) h);
    reflexivity
}
{
    assume n ihn l g;
    refine rec_𝕃 g (λ g, (istrue (size g ≤ (n +1))) ⇒ (den l (mergesort g) = den l g)) _ _
    { simplify; assume h; reflexivity }
    {
        induction; assume i gs;
        refine rec_𝕃 gs (λ gs, istrue (size (p i ⸬ gs) ≤ (n +1)) ⇒ (den l (mergesort (p i ⸬ gs)) = den l (p i ⸬ gs))) _ _
        {
            simplify;
            assume h;
            reflexivity
        }
        {
            induction;
            assume j xs inv;
            simplify;
            rewrite merge_correct;
            have h1:  π ((size (p i ⸬ (split xs ₁))) ≤ n) {
                apply @leq_trans
                (size (split xs ₁) +1)
                (size xs +1)
                n
                _
                inv;
                apply size_split xs;
            };
            have h2:  π ((size (p j ⸬ (split xs ₂))) ≤ n) {
                apply @leq_trans
                (size (split xs ₂) +1)
                (size xs +1)
                n
                _
                inv;
                apply size_split2 xs;
            };
            rewrite ihn l (p i ⸬ (split xs ₁)) h1;
            rewrite ihn l (p j ⸬ (split xs ₂)) h2;
            simplify;
            rewrite left ∨_assoc;
            rewrite .[x in (_ ∨ x) = _] ∨_assoc;
            rewrite ∨_com (den l (split xs ₁)) (nth ⊥ l j);
            rewrite left ∨_assoc;
            rewrite left ++_eq_∨ l (split xs ₁) (split xs ₂);
            rewrite split_correct;
            reflexivity
        }
    }
}
end;

symbol mergesort_correct l g ≔ mergesort_correct_aux (size g) l g (≤_refl (size g));

symbol remove_iden: τ (list cl) → τ (list cl);
rule remove_iden □ ↪ □
with remove_iden ((p $i) ⸬ □) ↪ (p $i) ⸬ □
with remove_iden ((p $i) ⸬ (p $j) ⸬ $tl) ↪ case_Comp (compN $i $j)
                                            (remove_iden ((p $j) ⸬ $tl))
                                            ((p $i) ⸬ (remove_iden ((p $j) ⸬ $tl)))
                                            ((p $i) ⸬ (remove_iden ((p $j) ⸬ $tl)));


// Rule contraction:
// 𝑖. ⊳ 𝑙1, ... , 𝑙n    (...)
// 𝑗. ⊳  𝑙𝑘1, ... , 𝑙kn (contraction i)
symbol contraction g ≔ remove_iden (mergesort g);

opaque symbol remove_iden_correct l g : π (den l (remove_iden g) = den l g) ≔
begin
  assume l;
  induction
  {simplify;reflexivity}
  {
    induction; assume i;
    induction
    {
      assume h; reflexivity
    }
    {
      induction; assume j gs ih1 ih2;
      simplify;
      refine ind_Comp (λ u, (compN i j) = u ⇒  den l (case_Comp u (remove_iden (p j ⸬ gs)) (p i ⸬ remove_iden (p j ⸬ gs)) (p i ⸬ remove_iden (p j ⸬ gs))) = (nth ⊥ l i ∨ (nth ⊥ l j ∨ den l gs))) _ _ _ (compN i j) _
      {
        simplify;
        assume heq;
        rewrite compN_correct i j heq;
        rewrite ∨_assoc;
        rewrite or_idempotent (nth ⊥ l j);
        rewrite ih2;
        reflexivity
      }
      {
        simplify;
        assume hlt;
        rewrite ih2;
        reflexivity
      }
      {
        simplify;
        assume hlt;
        rewrite ih2;
        reflexivity
      }
      {reflexivity}
    }
  }
end;

opaque symbol contraction_correct l g : π (den l (contraction g) = den l g) ≔
begin
  assume l g;
  simplify;
  rewrite remove_iden_correct;
  rewrite mergesort_correct;
  reflexivity
end;

opaque symbol contraction_correct_r l g : π (den l g = den l (contraction g)) ≔
begin
  assume l g;
  symmetry;
  refine contraction_correct l g
end;

private symbol example a b : π̇ (a ⟇ b ⟇ b ⟇ ▩) → π̇ (a ⟇ b ⟇ ▩) ≔
begin
  assume a b i;
  set X ≔ (a ⟇ (b ⟇ (b ⟇ ▩)));
  set Y ≔ (a ⟇ b ⟇ ▩);
  have g : π (⟇_to_∨_rw X = ⟇_to_∨_rw Y) {
    set r ≔ reify_cl X;
    change π (den (r ₂) (r ₁) = ⟇_to_∨_rw Y);
    rewrite left contraction_correct;
    reflexivity
  };
  refine subst_equiv_clause X Y  g i
end;
