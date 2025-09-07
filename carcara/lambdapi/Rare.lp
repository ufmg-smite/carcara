require open lambdapi.Alethe;
require open lambdapi.Simplify;

notation ¬ prefix 35;


// (define-rule eq-refl ((t ?)) (= t t) true)
opaque symbol eq-refl [a] (t: τ a) : π ((t = t) = ⊤) ≔ begin
    assume a p;
    apply prop_ext;
    apply ∧ᵢ
    { assume H; remove H; apply ⊤ᵢ  }
    { assume H⊤; remove H⊤; reflexivity } 
end;

// (define-rule eq-symm ((t ?) (s ?)) (= t s) (= s t))
opaque symbol eq-symm [a] (t s: τ a) : π ((t = s) = (s = t)) ≔
begin
    assume a t s;
    apply prop_ext;
    apply ∧ᵢ
    {
        assume H;
        symmetry; apply H
    }
    {
        assume H;
        symmetry; apply H
    }
end;

// (define-rule bool-impl-false1 ((t Bool)) (=> t false) (not t))
opaque symbol bool-impl-false1 t : π ((t ⇒ ⊥) = ¬ t) ≔ implies_simplify5 t;

// (define-rule bool-impl-false2 ((t Bool)) (=> false t) true)
opaque symbol bool-impl-false2 t : π ((⊥ ⇒ t) = ⊤) ≔
begin
    assume t;
    apply prop_ext;
    apply ∧ᵢ
    { assume Htbot; apply ⊤ᵢ  }
    { assume Htop;  assume Ht; apply ⊥ₑ Ht }
end;

// (define-rule bool-double-not-elim ((t Bool)) (not (not t)) t)
// Duplicate of Alethe
opaque symbol bool-double-not-elim t : π ((¬ (¬ t)) = t) ≔ not_simplify1 t;


//(define-rule bool-impl-elim ((t Bool) (s Bool)) (=> t s) (or (not t) s))
opaque symbol bool-impl-elim s t: π ((s ⇒ t) = ((¬ s) ∨ t)) ≔
begin
  assume s t;
  apply prop_ext;
  apply ∧ᵢ
  {  assume Himp; apply imply_to_or Himp }
  {  assume Hor; refine or_to_imply Hor }
end;

//(define-rule distinct-binary-elim ((t ?) (s ?)) (distinct t s) (not (= t s)))
opaque symbol distinct-binary-elim [a] (t s: τ a) : π (distinct (cons t (cons s ⧈)) = ( t ≠ s)) ≔ eq_refl (distinct (cons t (cons s ⧈)));

// (define-rule bool-impl-true2 ((t Bool)) (=> true t) t)
opaque symbol bool-impl-true2 t : π ((⊤ ⇒ t) = t) ≔
begin
    assume t;
    apply prop_ext;
    apply ∧ᵢ
    {   assume HTopt; apply HTopt ⊤ᵢ }
    {  assume Ht;  assume Htop; apply Ht }
end;

// (define-rule bool-impl-true1 ((t Bool)) (=> t true) true)
opaque symbol bool-impl-true1 t : π ((t ⇒ ⊤) = ⊤) ≔
begin
    assume t;
    apply prop_ext;
    apply ∧ᵢ
    {   assume HTopt; apply ⊤ᵢ }
    {  assume Ht;  assume Htop; apply ⊤ᵢ }
end;


// (define-rule* bool-and-true ((xs Bool :list) (ys Bool :list)) (and xs true ys) (and xs ys))
opaque symbol bool-and-true xs ys : π ((xs ∧ ⊤ ∧ ys) = (xs ∧ ys)) ≔
begin
    assume xs ys;
    rewrite ∧_com ⊤ ys;
    rewrite and_identity_r;
    reflexivity
end;

// (define-rule bool-and-false ((xs Bool :list) (ys Bool :list)) (and xs false ys) false)
opaque symbol bool-and-false xs ys : π ((xs ∧ ⊥ ∧ ys) = ⊥) ≔
begin
    assume xs ys;
    rewrite ∧_com ⊥ ys;
    rewrite and_domination;
    rewrite and_domination;
    reflexivity
end;

// (define-rule* bool-or-false ((xs Bool :list) (ys Bool :list)) (or xs false ys) (or xs ys))
opaque symbol bool-or-false xs ys : π ((xs ∨ ⊥ ∨ ys) = (xs ∨ ys)) ≔
begin
    assume xs ys; 
    rewrite ∨_com ⊥ ys;
    rewrite or_identity_r;
    reflexivity
end;

// (define-rule* bool-or-flatten ((xs Bool :list) (b Bool) (ys Bool :list) (zs Bool :list)) (or xs (or b ys) zs) (or xs b ys zs))
opaque symbol bool-or-flatten xs b ys zs : π ((xs ∨ (b ∨ ys) ∨ zs) = (xs ∨ b ∨ ys ∨ zs)) ≔
begin
    assume xs b ys zs;
    rewrite left ∨_assoc;
    reflexivity
end;


// Reviewed bool-or-flatten without `xs`
// (define-rule* bool-or-flatten ((b Bool) (ys Bool :list) (zs Bool :list)) (or (or b ys) zs) (or b ys zs))
opaque symbol bool-or-flatten' b ys zs : π (((b ∨ ys) ∨ zs) = (b ∨ ys ∨ zs)) ≔
begin
    assume b ys zs;
    symmetry;
    apply ∨_assoc;
end;

// (define-rule* bool-and-flatten ((xs Bool :list) (b Bool) (ys Bool :list) (zs Bool :list)) (and xs (and b ys) zs) (and xs b ys zs))
opaque symbol bool-and-flatten b [xs ys zs] : π ((xs ∧ (b ∧ ys) ∧ zs) = (xs ∧ b ∧ ys ∧ zs)) ≔
begin
    assume b xs ys zs;
    rewrite left ∧_assoc;
    reflexivity
end;

// Reviewed bool-and-flatten without `xs`
// (define-rule* bool-and-flatten ((b Bool) (ys Bool :list) (zs Bool :list)) (and (and b ys) zs) (and b ys zs))
opaque symbol bool-and-flatten' b ys zs : π (((b ∧ ys) ∧ zs) = (b ∧ ys ∧ zs)) ≔
begin
    assume b ys zs;
    symmetry;
    apply ∧_assoc;
end;

// (define-rule bool-eq-true ((t Bool)) (= t true) t)
opaque symbol bool-eq-true (t: τ o) : π ((t = ⊤) = t) ≔
begin
    assume t;
    apply prop_ext;
    apply ∧ᵢ
    {
        
        assume H;
        rewrite H;
        apply ⊤ᵢ
    }
    {
        
        assume Ht;
        apply prop_ext;
        apply ∧ᵢ
        {  assume Ht'; apply ⊤ᵢ }
        {  assume Ht';  apply Ht }
    }
end;

// (define-rule bool-eq-false ((t Bool)) (= t false) (not t))
opaque symbol bool-eq-false (t: τ o) : π ((t = ⊥) = ¬ t) ≔
begin
    assume t;
    apply prop_ext;
    apply ∧ᵢ
    {
        
        assume H;
        rewrite H;
        assume Hbot;
        apply Hbot
    }
    {
        
        assume Hnt;
        apply prop_ext;
        apply ∧ᵢ
        {   assume Ht; apply (¬ₑ Hnt Ht) }
        {  assume Ht';  apply (⊥ₑ Ht') }
    }
end;

// (define-rule* bool-and-de-morgan ((x Bool) (y Bool) (zs Bool :list)) 
//   (not (and x y zs))
//   (not (and y zs))
//   (or (not x) _))
opaque symbol bool-and-de-morgan (x y zs: τ o): π ((¬ (x ∧ y ∧ zs)) = ((¬ x) ∨ (¬ y) ∨ (¬ zs))) ≔
begin
    assume x y zs;
    apply prop_ext;
    apply ∧ᵢ
    { rewrite morgan1; rewrite morgan1;  assume H; refine H }
    { rewrite morgan1; rewrite morgan1;  assume H; refine H }
end;

// (define-rule* bool-or-de-morgan ((x Bool) (y Bool) (zs Bool :list)) 
//   (not (or x y zs))
//   (not (or y zs))
//   (and (not x) _))
opaque symbol bool-or-de-morgan (x y zs: τ o): π ((¬ (x ∨ y ∨ zs)) = ((¬ x) ∧ (¬ y) ∧ (¬ zs))) ≔
begin
    assume x y zs;
    apply prop_ext;
    apply ∧ᵢ
    { rewrite morgan2; rewrite morgan2;  assume H; refine H }
    { rewrite morgan2; rewrite morgan2;  assume H; refine H }
end;


// Integer
require open Stdlib.Z;
require open Stdlib.Bool;
require open Stdlib.Comp;
require open Stdlib.Pos;

notation ≥ infix 10; //FIXME: fix notation in Stdlib

// (define-rule arith-elim-lt ((t ?) (s ?)) (< t s) (not (>= t s)))
opaque symbol arith-elim-lt t s : π ((t < s) = ¬ (t ≥ s)) ≔
begin
    assume t s;
    simplify;
    apply prop_ext;
    apply ∧ᵢ
    {
        assume H;
        assume H2;
        apply fold_⇒ H2;
        apply H  
    }
    {
        assume H;
        have H2: π (¬ ¬ istrue (isLt (t ≐ s))) { refine H };
        rewrite left nnpp_eq;
        refine H2
    }
end;

symbol ind_ℤ (p: (ℤ → Prop)) :
    Π x,  π (p 0) → 
    (Π (y: ℙ), π (p (Zpos y))) → 
    (Π (y: ℙ), π (p (Zneg y))) → 
    π (p x);


symbol ind_ℤ₂ (p: (ℤ → Prop)) :
     π (p 0) → 
    (Π (y: ℙ), π (p (Zpos y))) → 
    (Π (y: ℙ), π (p (Zneg y))) → 
    Π x, π (p x);

symbol ind_ℙ (p: ℙ → Prop):
    Π (x: ℙ), (Π y: ℙ, π (p y) → π (p (I y))) →
    (Π y: ℙ, π (p y) →
    π (p (O y))) →
    π (p H) → π (p x);

// (define-rule arith-geq-tighten ((t Int) (s Int)) (not (>= t s)) (>= s (+ t 1)))
opaque symbol arith-geq-tighten t s : π ((¬ (t ≥ s)) = (s ≥ (t + 1))) ≔
begin
admitted;

// (define-rule arith-geq-norm2 ((t ?) (s ?)) (>= t s) (<= (- t) (- s)))
opaque symbol arith-geq-norm2 t s : π ((t ≥ s) =  (— t ≤ — s)) ≔
begin 
    assume t s;
    apply prop_ext;
    apply ∧ᵢ
    {
        refine (∧ₑ₁ (opp_le_mono t s));
    }
    {
        refine (∧ₑ₂ (opp_le_mono t s));
    }
end;

// (define-rule arith-geq-norm1 ((t ?) (s ?)) (>= t s) (>= (- t s) 0))
opaque symbol arith-geq-norm1 t s : π ((t ≥ s) = ((t - s) ≥ 0)) ≔
begin 
    assume t s;
    apply prop_ext;
    apply ∧ᵢ
    {
        refine ge_implies_diff_nonneg t s;
    }
    {
        refine diff_nonneg_implies_ge t s;
    }
end;

// (define-rule arith-leq-norm ((t Int) (s Int)) (<= t s) (not (>= t (+ s 1))))
opaque symbol arith-leq-norm (t s: τ int) : π ((t ≤ s) = ¬ (t ≥ s + 1)) ≔
begin
    assume t s;
    apply prop_ext;
    apply ∧ᵢ
    {
        refine ≤-norm t s
    }
    {
        admit //TODO: prove me
    }
end;

// (define-rule arith-elim-gt ((t ?) (s ?)) (> t s) (not (<= t s)))
opaque symbol arith-elim-gt (t s: τ int) : π ((t > s) = (¬ (t ≤ s))) ≔
begin 
assume t s;
apply prop_ext;
apply ∧ᵢ
{
    refine >_neg_≤ t s
}
{
    refine (λ x, x);
}
end;

// (define-rule arith-elim-leq ((t ?) (s ?)) (<= t s) (>= s t))
opaque symbol arith-elim-leq (t s: τ int) : π ((t ≤ s) = (s ≥ t)) ≔
begin 
    assume t s;
    apply prop_ext;
    apply ∧ᵢ
    {
        assume H;
        refine (∧ₑ₂ (≤_≥ s t)) H
    }
    {
        assume H;
        refine (∧ₑ₁ (≤_≥ s t)) H
    }
end;

// (define-rule arith-refl-leq ((t ?)) (<= t t) true)
opaque symbol arith-refl-leq (t: τ int) : π ((t ≤ t) = ⊤) ≔
begin
assume t;
apply prop_ext;
apply ∧ᵢ
{  assume H; apply ⊤ᵢ }
{
     assume Htop;
    refine (≤_refl t)
}
end;

// (define-rule arith-refl-lt ((t ?)) (< t t) false)
opaque symbol arith-refl-lt (t: τ int) : π ((t < t) = ⊥) ≔
begin
    assume t;
    apply prop_ext;
    apply ∧ᵢ
    {
        refine <_no_refl t
    }
    {
        
        assume Hbot;
        apply ⊥ₑ Hbot 
    }
end;

// (define-rule arith-refl-geq ((t ?)) (>= t t) true)
opaque symbol arith-refl-geq (t: τ int) : π ((t ≥ t) = ⊤) ≔
begin
assume t;
apply prop_ext;
apply ∧ᵢ
{  assume H; apply ⊤ᵢ }
{
     assume Htop;
    refine (≥_refl t)
}
end;

// (define-rule arith-refl-gt ((t ?)) (> t t) false)
opaque symbol arith-refl-gt (t: τ int) : π ((t > t) = ⊥) ≔
begin 
assume t;
apply prop_ext;
apply ∧ᵢ
{
    generalize t;
    assume t;
    refine >_no_refl t;
}
{
    
    assume Hbot;
    apply ⊥ₑ Hbot 
};
end;

// (define-rule arith-int-eq-elim ((t Int) (s Int)) (= t s) (and (>= t s) (<= t s)))
opaque symbol arith-int-eq-elim (t s: τ int) : π ((t = s) = ((t ≥ s) ∧ (t ≤ s))) ≔
begin
assume t s;
apply prop_ext;
apply ∧ᵢ
{
     assume Heq;
    rewrite Heq;
    apply ∧ᵢ 
    {
        refine (≥_refl s)
    }
    {
        refine (≤_refl s)
    }
}
{
    assume H1;
    refine  ≤_antisym t s _ _
    {
        refine (∧ₑ₁ (≤_≥ s t)) _;
        refine (∧ₑ₂ (≤_≥ s t)) (∧ₑ₂ H1);
    }
    {  refine  (∧ₑ₁ (≤_≥ t s)) (∧ₑ₁ H1); }
}
end;