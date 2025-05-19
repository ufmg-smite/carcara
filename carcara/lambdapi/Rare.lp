require open Stdlib.Prop;
require open Stdlib.FOL;
require open Stdlib.Set;
require open Stdlib.Eq;
require open Stdlib.Nat;
require open lambdapi.Classic;
require open lambdapi.Alethe;
require open lambdapi.Simplify;

notation ¬ prefix 35;


// (define-rule eq-refl ((t ?)) (= t t) true)
opaque symbol eq-refl [a] (t: τ a) : πᶜ ((t = t) = ⊤) ≔ equiv_simplify₂ t;

// (define-rule eq-symm ((t ?) (s ?)) (= t s) (= s t))
opaque symbol eq-symm [a] (t s: τ a) : πᶜ ((t = s) = (s = t)) ≔
begin
    assume a t s;
    apply prop_ext;
    apply ∧ᶜᵢ
    {
        apply ⇒ᶜᵢ; assume H;
        symmetry; apply H
    }
    {
        apply ⇒ᶜᵢ; assume H;
        symmetry; apply H
    }
end;

// (define-rule bool-impl-false1 ((t Bool)) (=> t false) (not t))
opaque symbol bool-impl-false1 t : πᶜ ((t ⇒ᶜ ⊥) = ¬ t) ≔ implies_simplify₅ t;

// (define-rule bool-impl-false2 ((t Bool)) (=> false t) true)
opaque symbol bool-impl-false2 t : πᶜ ((⊥ ⇒ᶜ t) = ⊤) ≔
begin
    assume t;
    apply prop_ext;
    apply ∧ᶜᵢ
    { apply ⇒ᶜᵢ; assume Htbot; apply trivial }
    { apply ⇒ᶜᵢ; assume Htop; apply ⇒ᶜᵢ; assume Ht; apply ⊥ᶜₑ Ht }
end;

// (define-rule bool-double-not-elim ((t Bool)) (not (not t)) t)
// Duplicate of Alethe
opaque symbol bool-double-not-elim t : πᶜ ((¬ (¬ t)) = t) ≔ not_simplify₁ t;


//(define-rule bool-impl-elim ((t Bool) (s Bool)) (=> t s) (or (not t) s))
opaque symbol bool-impl-elim s t: πᶜ ((s ⇒ᶜ t) = ((¬ s) ∨ᶜ t)) ≔
begin
  assume s t;
  apply prop_ext;
  apply ∧ᶜᵢ
  { apply ⇒ᶜᵢ; assume Himp; apply imply_to_or Himp }
  { apply ⇒ᶜᵢ; assume Hor; apply or_to_imply Hor }
end;

//(define-rule distinct-binary-elim ((t ?) (s ?)) (distinct t s) (not (= t s)))
opaque symbol distinct-binary-elim [a] (t s: τ a) : πᶜ (distinct (cons t (cons s □)) = ( t ≠ s)) ≔ eq_reflᶜ (distinct (cons t (cons s □)));

// (define-rule bool-impl-true2 ((t Bool)) (=> true t) t)
opaque symbol bool-impl-true2 t : πᶜ ((⊤ ⇒ᶜ t) = t) ≔
begin
    assume t;
    apply prop_ext;
    apply ∧ᶜᵢ
    { apply ⇒ᶜᵢ;  assume HTopt; apply ⇒ᶜₑ HTopt trivial }
    { apply ⇒ᶜᵢ; assume Ht; apply ⇒ᶜᵢ; assume Htop; apply Ht }
end;

// (define-rule bool-impl-true1 ((t Bool)) (=> t true) true)
opaque symbol bool-impl-true1 t : πᶜ ((t ⇒ᶜ ⊤) = ⊤) ≔
begin
    assume t;
    apply prop_ext;
    apply ∧ᶜᵢ
    { apply ⇒ᶜᵢ;  assume HTopt; apply trivial }
    { apply ⇒ᶜᵢ; assume Ht; apply ⇒ᶜᵢ; assume Htop; apply trivial }
end;


// (define-rule* bool-and-true ((xs Bool :list) (ys Bool :list)) (and xs true ys) (and xs ys))
opaque symbol bool-and-true xs ys : πᶜ ((xs ∧ᶜ ⊤ ∧ᶜ ys) = (xs ∧ᶜ ys)) ≔
begin
    assume xs ys;
    rewrite and_com ⊤ ys;
    rewrite and_identity_r;
    reflexivity
end;

// (define-rule bool-and-false ((xs Bool :list) (ys Bool :list)) (and xs false ys) false)
opaque symbol bool-and-false xs ys : πᶜ ((xs ∧ᶜ ⊥ ∧ᶜ ys) = ⊥) ≔
begin
    assume xs ys;
    rewrite and_com ⊥ ys;
    rewrite and_domination;
    rewrite and_domination;
    reflexivity
end;

// (define-rule* bool-or-false ((xs Bool :list) (ys Bool :list)) (or xs false ys) (or xs ys))
opaque symbol bool-or-false xs ys : πᶜ ((xs ∨ᶜ ⊥ ∨ᶜ ys) = (xs ∨ᶜ ys)) ≔
begin
    assume xs ys;
    rewrite or_com ⊥ ys;
    rewrite or_identity_r;
    reflexivity
end;

// (define-rule* bool-or-flatten ((xs Bool :list) (b Bool) (ys Bool :list) (zs Bool :list)) (or xs (or b ys) zs) (or xs b ys zs))
opaque symbol bool-or-flatten xs b ys zs : πᶜ ((xs ∨ᶜ (b ∨ᶜ ys) ∨ᶜ zs) = (xs ∨ᶜ b ∨ᶜ ys ∨ᶜ zs)) ≔
begin
    assume xs b ys zs;
    rewrite left ∨ᶜ_assoc_eq;
    reflexivity
end;


// Reviewed bool-or-flatten without `xs`
// (define-rule* bool-or-flatten ((b Bool) (ys Bool :list) (zs Bool :list)) (or (or b ys) zs) (or b ys zs))
opaque symbol bool-or-flatten' b ys zs : πᶜ (((b ∨ᶜ ys) ∨ᶜ zs) = (b ∨ᶜ ys ∨ᶜ zs)) ≔
begin
    assume b ys zs;
    symmetry;
    apply ∨ᶜ_assoc_eq;
end;

// (define-rule* bool-and-flatten ((xs Bool :list) (b Bool) (ys Bool :list) (zs Bool :list)) (and xs (and b ys) zs) (and xs b ys zs))
opaque symbol bool-and-flatten b [xs ys zs] : πᶜ ((xs ∧ᶜ (b ∧ᶜ ys) ∧ᶜ zs) = (xs ∧ᶜ b ∧ᶜ ys ∧ᶜ zs)) ≔
begin
    assume b xs ys zs;
    rewrite left ∧ᶜ_assoc_eq;
    reflexivity
end;

// Reviewed bool-and-flatten without `xs`
// (define-rule* bool-and-flatten ((b Bool) (ys Bool :list) (zs Bool :list)) (and (and b ys) zs) (and b ys zs))
opaque symbol bool-and-flatten' b ys zs : πᶜ (((b ∧ᶜ ys) ∧ᶜ zs) = (b ∧ᶜ ys ∧ᶜ zs)) ≔
begin
    assume b ys zs;
    symmetry;
    apply ∧ᶜ_assoc_eq;
end;

// (define-rule bool-eq-true ((t Bool)) (= t true) t)
opaque symbol bool-eq-true (t: τ o) : πᶜ ((t = ⊤) = t) ≔
begin
    assume t;
    apply prop_ext;
    apply ∧ᶜᵢ
    {
        apply ⇒ᶜᵢ;
        assume H;
        rewrite H;
        apply trivial
    }
    {
        apply ⇒ᶜᵢ;
        assume Ht;
        apply prop_ext;
        apply ∧ᶜᵢ
        { apply ⇒ᶜᵢ; assume Ht'; apply trivial }
        { apply ⇒ᶜᵢ; assume Ht';  apply Ht }
    }
end;

// (define-rule bool-eq-false ((t Bool)) (= t false) (not t))
opaque symbol bool-eq-false (t: τ o) : πᶜ ((t = ⊥) = ¬ t) ≔
begin
    assume t;
    apply prop_ext;
    apply ∧ᶜᵢ
    {
        apply ⇒ᶜᵢ;
        assume H;
        rewrite H;
        apply ¬ᶜᵢ;
        assume Hbot;
        apply Hbot
    }
    {
        apply ⇒ᶜᵢ;
        assume Hnt;
        apply prop_ext;
        apply ∧ᶜᵢ
        {  apply ⇒ᶜᵢ; assume Ht; apply (¬ᶜₑ Hnt Ht) }
        { apply ⇒ᶜᵢ; assume Ht';  apply (⊥ᶜₑ Ht') }
    }
end;

// (define-rule* bool-and-de-morgan ((x Bool) (y Bool) (zs Bool :list)) 
//   (not (and x y zs))
//   (not (and y zs))
//   (or (not x) _))
opaque symbol bool-and-de-morgan (x y zs: τ o): πᶜ ((¬ (x ∧ᶜ y ∧ᶜ zs)) = ((¬ x) ∨ᶜ (¬ y) ∨ᶜ (¬ zs))) ≔
begin
    assume x y zs;
    apply prop_ext;
    apply ∧ᶜᵢ
    { rewrite morgan₁; rewrite morgan₁; apply ⇒ᶜᵢ; assume H; refine H }
    { rewrite morgan₁; rewrite morgan₁; apply ⇒ᶜᵢ; assume H; refine H }
end;

// (define-rule* bool-or-de-morgan ((x Bool) (y Bool) (zs Bool :list)) 
//   (not (or x y zs))
//   (not (or y zs))
//   (and (not x) _))
opaque symbol bool-or-de-morgan (x y zs: τ o): πᶜ ((¬ (x ∨ᶜ y ∨ᶜ zs)) = ((¬ x) ∧ᶜ (¬ y) ∧ᶜ (¬ zs))) ≔
begin
    assume x y zs;
    apply prop_ext;
    apply ∧ᶜᵢ
    { rewrite morgan₂; rewrite morgan₂; apply ⇒ᶜᵢ; assume H; refine H }
    { rewrite morgan₂; rewrite morgan₂; apply ⇒ᶜᵢ; assume H; refine H }
end;


// Integer
require open Stdlib.Z;
require open Stdlib.Bool;
require open Stdlib.Comp;
require open Stdlib.Pos;

notation ≥ infix 10; //FIXME: fix notation in Stdlib

// (define-rule arith-elim-lt ((t ?) (s ?)) (< t s) (not (>= t s)))
opaque symbol arith-elim-lt t s : πᶜ ((t < s) = ¬ (t ≥ s)) ≔
begin
    assume t s;
    simplify;
    apply prop_ext;
    apply ∧ᶜᵢ
    {
        apply ⇒ᶜᵢ;
        assume H;
        apply meta-arr;
        assume H2;
        apply fold_⇒ᶜ H2;
        apply H  
    }
    {
        apply ⇒ᶜᵢ;
        assume H;
        have H2: πᶜ (¬ ¬ istrue (isLt (t ≐ s))) { refine H };
        rewrite left nnpp_eq;
        apply H2
    }
end;

symbol ind_ℤᶜ (p: (ℤ → Prop)) :
    Π x,  πᶜ (p 0) → 
    (Π (y: ℙ), πᶜ (p (Zpos y))) → 
    (Π (y: ℙ), πᶜ (p (Zneg y))) → 
    πᶜ (p x);


symbol ind_ℤᶜ₂ (p: (ℤ → Prop)) :
     πᶜ (p 0) → 
    (Π (y: ℙ), πᶜ (p (Zpos y))) → 
    (Π (y: ℙ), πᶜ (p (Zneg y))) → 
    Π x, πᶜ (p x);

symbol ind_ℙᶜ (p: ℙ → Prop):
    Π (x: ℙ), (Π y: ℙ, πᶜ (p y) → πᶜ (p (I y))) →
    (Π y: ℙ, πᶜ (p y) →
    πᶜ (p (O y))) →
    πᶜ (p H) → πᶜ (p x);

// (define-rule arith-geq-tighten ((t Int) (s Int)) (not (>= t s)) (>= s (+ t 1)))
opaque symbol arith-geq-tighten t s : πᶜ ((¬ (t ≥ s)) = (s ≥ (t + 1))) ≔
begin
admitted;

// (define-rule arith-geq-norm2 ((t ?) (s ?)) (>= t s) (<= (- t) (- s)))
opaque symbol arith-geq-norm2 t s : πᶜ ((t ≥ s) =  (— t ≤ — s)) ≔
begin 
    assume t s;
    apply prop_ext;
    apply ∧ᶜᵢ
    {
        apply IL_imp_Cl _; 
        apply ⇒ᶜ_in_IL;
        refine (∧ₑ₁ (opp_le_mono t s));
    }
    {
        apply IL_imp_Cl _; 
        apply ⇒ᶜ_in_IL;
        refine (∧ₑ₂ (opp_le_mono t s));
    }
end;

// (define-rule arith-geq-norm1 ((t ?) (s ?)) (>= t s) (>= (- t s) 0))
opaque symbol arith-geq-norm1 t s : πᶜ ((t ≥ s) = ((t - s) ≥ 0)) ≔
begin 
    assume t s;
    apply prop_ext;
    apply ∧ᶜᵢ
    {
        apply IL_imp_Cl _; 
        apply ⇒ᶜ_in_IL;
        refine ge_implies_diff_nonneg t s;
    }
    {
        apply IL_imp_Cl _; 
        apply ⇒ᶜ_in_IL;
        refine diff_nonneg_implies_ge t s;
    }
end;

// (define-rule arith-leq-norm ((t Int) (s Int)) (<= t s) (not (>= t (+ s 1))))
opaque symbol arith-leq-norm (t s: τ int) : πᶜ ((t ≤ s) = ¬ (t ≥ s + 1)) ≔
begin
    assume t s;
    apply prop_ext;
    apply ∧ᶜᵢ
    {
        apply IL_imp_Cl _;
        apply ⇒ᶜ_in_IL;
        refine ≤-norm t s
    }
    {
        admit //TODO: prove me
    }
end;

// (define-rule arith-elim-gt ((t ?) (s ?)) (> t s) (not (<= t s)))
opaque symbol arith-elim-gt (t s: τ int) : πᶜ ((t > s) = (¬ (t ≤ s))) ≔
begin 
assume t s;
apply prop_ext;
apply ∧ᶜᵢ
{
    apply IL_imp_Cl _;
    apply ⇒ᶜ_in_IL;
    refine >_neg_≤ t s
}
{
    apply IL_imp_Cl _;
    apply ⇒ᶜ_in_IL;
    refine (λ x, x);
}
end;

// (define-rule arith-elim-leq ((t ?) (s ?)) (<= t s) (>= s t))
opaque symbol arith-elim-leq (t s: τ int) : πᶜ ((t ≤ s) = (s ≥ t)) ≔
begin 
    assume t s;
    apply prop_ext;
    apply ∧ᶜᵢ
    {
        apply IL_imp_Cl _;
        apply ⇒ᶜ_in_IL;
        assume H;
        refine (∧ₑ₂ (≤_≥ s t)) H
    }
    {
        apply IL_imp_Cl _;
        apply ⇒ᶜ_in_IL;
        assume H;
        refine (∧ₑ₁ (≤_≥ s t)) H
    }
end;

// (define-rule arith-refl-leq ((t ?)) (<= t t) true)
opaque symbol arith-refl-leq (t: τ int) : πᶜ ((t ≤ t) = ⊤) ≔
begin
assume t;
apply prop_ext;
apply ∧ᶜᵢ
{ apply ⇒ᶜᵢ; assume H; apply trivial }
{
    apply ⇒ᶜᵢ; assume Htop;
    apply IL_imp_Cl _;
    refine (≤_refl t)
}
end;

// (define-rule arith-refl-lt ((t ?)) (< t t) false)
opaque symbol arith-refl-lt (t: τ int) : πᶜ ((t < t) = ⊥) ≔
begin
    assume t;
    apply prop_ext;
    apply ∧ᶜᵢ
    {
        generalize t;
        refine (@∀ᶜ_Π int (λ t, (t < t) ⇒ᶜ ⊥)) _;
        apply IL_imp_Cl2 _;
        assume t;
        apply ⇒ᶜ_in_IL ;
        refine <_no_refl t
    }
    {
        apply ⇒ᶜᵢ;
        assume Hbot;
        apply ⊥ᶜₑ Hbot 
    }
end;

// (define-rule arith-refl-geq ((t ?)) (>= t t) true)
opaque symbol arith-refl-geq (t: τ int) : πᶜ ((t ≥ t) = ⊤) ≔
begin
assume t;
apply prop_ext;
apply ∧ᶜᵢ
{ apply ⇒ᶜᵢ; assume H; apply trivial }
{
    apply ⇒ᶜᵢ; assume Htop;
    apply IL_imp_Cl _;
    refine (≥_refl t)
}
end;

// (define-rule arith-refl-gt ((t ?)) (> t t) false)
opaque symbol arith-refl-gt (t: τ int) : πᶜ ((t > t) = ⊥) ≔
begin 
assume t;
apply prop_ext;
apply ∧ᶜᵢ
{
    generalize t;
    refine (@∀ᶜ_Π int (λ t, (t > t) ⇒ᶜ ⊥)) _;
    apply IL_imp_Cl2 _;
    assume t;
    apply ⇒ᶜ_in_IL ;
    refine >_no_refl t;
}
{
    apply ⇒ᶜᵢ;
    assume Hbot;
    apply ⊥ᶜₑ Hbot 
};
end;

// (define-rule arith-int-eq-elim ((t Int) (s Int)) (= t s) (and (>= t s) (<= t s)))
opaque symbol arith-int-eq-elim (t s: τ int) : πᶜ ((t = s) = ((t ≥ s) ∧ᶜ (t ≤ s))) ≔
begin
assume t s;
apply prop_ext;
apply ∧ᶜᵢ
{
    apply ⇒ᶜᵢ; assume Heq;
    rewrite Heq;
    apply ∧ᶜᵢ 
    {
        apply IL_imp_Cl _;
        refine (≥_refl s)
    }
    {
        apply IL_imp_Cl _;
        refine (≤_refl s)
    }
}
{
    refine ⇒ᶜₑ (∧ᶜₑ₂ ∧ᶜ_⇒ᶜ) _;
    apply IL_imp_Cl _;
    apply ⇒ᶜ_in_IL;
    assume H1;
    apply ⇒ᶜ_in_IL;
    assume H2;
    have  H1bis: π (s ≤ t) { refine ∧ₑ₁ (≤_≥ t s) H1 };
    remove H1;
    apply (@eq_sym int s t);
    refine  ≤_antisym s t H1bis H2;
}
end;