require open lambdapi.Alethe;
require open lambdapi.Tactic;
require open Stdlib.List;

// Rule 71: equiv_simplify

symbol equiv_simplify1 p q : π (((¬ p) = ¬ q) = (p = q)) ≔
begin
    assume p q;
    apply prop_ext;
    apply ∧ᵢ
    {
        assume Heq;
        apply prop_ext; 
        apply ∧ᵢ
        {
            rewrite left imp_eq_or;
            rewrite Heq;
            rewrite ∨_com;
            apply em
        }
        {
            rewrite left imp_eq_or;
            rewrite left Heq;
            rewrite ∨_com;
            apply em
        }
    }
    {
        assume Heq;
        rewrite Heq;
        reflexivity
    }
end;

symbol equiv_simplify2  (p : τ o) : π ((p = p) = ⊤) ≔
begin
    assume p;
    apply prop_ext;
    apply ∧ᵢ
    { assume H; remove H; apply ⊤ᵢ  }
    { assume H⊤; remove H⊤; reflexivity }
end;

// (𝜑 ≈ ¬ 𝜑) ⇒ ⊥
symbol equiv_simplify3 p : π ((p = (¬ p)) = ⊥) ≔
begin
    assume p;
    apply prop_ext;
    rewrite left iff_equiv_eq;
    simplify;
    rewrite left imp_eq_or;
    rewrite left imp_eq_or;
    rewrite left imp_eq_or;
    rewrite left imp_eq_or;
    apply ∧ᵢ
    {
        rewrite or_identity_r;
        rewrite or_identity_r;
        rewrite morgan1;
        rewrite .[¬ ((¬ (¬ p)) ∨ p)] morgan2;
        rewrite distributive_or;
        rewrite or_idempotent;
        apply ∧ᵢ
        {
            apply em
        }
        {
            rewrite ∨_com;
            apply em
        };
    }
    {   
        assume contra;
        refine ⊥ₑ contra
    }
end;

// (¬ 𝜑 ≈ 𝜑) ⇒ ⊥
symbol equiv_simplify4 p : π (((¬ p) = p) = ⊥) ≔
begin
    assume p;
    rewrite =_sym (¬ p) p;
    apply equiv_simplify3
end;

//(⊤ ≈ 𝜑) ⇒ 𝜑
symbol equiv_simplify5 p : π ((⊤ = p) = p) ≔
begin
    assume p;
    apply prop_ext;
    rewrite left iff_equiv_eq;
    apply ∧ᵢ
    {
        assume H;
        have H2: π (⊤ ⇒ p) { apply ∧ₑ₁ H };
        apply H2;
        apply ⊤ᵢ
    }
    {
        assume Hp;
        apply ∧ᵢ
        { assume Htop; apply Hp }
        { assume Hp'; apply ⊤ᵢ }
    }
end;


// (𝜑 ≈ ⊤) ⇒ 𝜑
symbol equiv_simplify6 p : π ((p = ⊤) = p) ≔
begin
    assume p;
    rewrite =_sym p ⊤;
    apply equiv_simplify5
end;

// (⊥ ≈ 𝜑) ⇒ ¬ 𝜑
symbol equiv_simplify7 p : π ((⊥ = p) = ¬ p) ≔
begin
    assume p;
    apply prop_ext;
    rewrite left iff_equiv_eq;
    simplify;
    apply ∧ᵢ
    { assume h; refine ∧ₑ₂ h }
    { assume h; apply ∧ᵢ { assume contra; refine ⊥ₑ contra } { refine h } }
end;

// (𝜑 ≈ ⊥) ⇒ ¬ 𝜑
symbol equiv_simplify8 p : π ((p = ⊥) = ¬ p) ≔
begin
    assume p;
    rewrite =_sym  p ⊥;
    apply equiv_simplify7
end;

symbol all_equiv_simplify ≔ 
    (#rewrite equiv_simplify1) ⸬ (#rewrite equiv_simplify2) ⸬ (#rewrite equiv_simplify3)
    ⸬ (#rewrite equiv_simplify4) ⸬(#rewrite equiv_simplify5) ⸬ (#rewrite equiv_simplify6) ⸬ (#rewrite equiv_simplify7) ⸬  (#rewrite equiv_simplify8) ⸬  □;

symbol equiv_simplify ≔ #repeat (applyAny all_equiv_simplify) and #try (#reflexivity #orelse (#apply ⊤ᵢ));


// Rule 69: not_simplify

opaque symbol not_simplify1 t : π ((¬ ¬ t) = t) ≔
begin
    assume t;
    apply prop_ext;
    apply ∧ᵢ
    {
        rewrite nnpp_eq;
        assume Ht;
        apply Ht
    }
    {
        rewrite nnpp_eq;
        assume Ht;
        apply Ht
    }
end;

opaque symbol not_simplify2 : π (¬ ⊥ = ⊤) ≔
begin
    simplify;
    apply prop_ext;
    apply ∧ᵢ
    { assume H; apply ⊤ᵢ }
    { assume Htop Hbot; refine Hbot }
end;

opaque symbol not_simplify3 : π (¬ ⊤ = ⊥) ≔
begin
    simplify;
    apply prop_ext;
    apply ∧ᵢ
    { assume H; apply fold_⇒ H; apply ⊤ᵢ }
    { assume Hbot; apply ⊥ₑ; refine Hbot }
end;

symbol all_not_simplify ≔ (#rewrite not_simplify1) ⸬ (#rewrite not_simplify2) ⸬ (#rewrite not_simplify3) ⸬ □;

symbol not_simplify ≔ #repeat (applyAny all_not_simplify) and #try (#reflexivity #orelse (#apply ⊤ᵢ));

private symbol not_simplify_test : π ((¬ ¬ ¬ ¬ ¬ ¬ ⊤) = (¬ ⊥)) ≔ begin
eval not_simplify;
end;

// Rule 70: implies_simplify

opaque symbol implies_simplify1 p q : π ((¬ p ⇒ ¬ q) = (q ⇒ p)) ≔
begin
    assume p q;
    apply prop_ext;
    apply ∧ᵢ
    { 
        assume H; rewrite left imp_eq_or;
        have H1: π ((¬ ¬ p) ∨ ¬ q) { rewrite imp_eq_or; refine H };
        apply ∨ₑ H1
        { assume Hnnp;  apply ∨ᵢ₂; apply ¬¬ₑ; refine Hnnp }
        { assume Hnq;  apply ∨ᵢ₁; refine Hnq }
    }
    {
        assume H; rewrite left imp_eq_or;
        have H1: π ((¬ q) ∨ p) { rewrite imp_eq_or; refine H };
        apply ∨ₑ H1
        { assume Hnq;  apply ∨ᵢ₂; refine Hnq }
        { assume Hp;  apply ∨ᵢ₁; rewrite not_simplify1; refine Hp }
    }
end;

opaque symbol implies_simplify2 p : π ((⊥ ⇒ p) = ⊤) ≔
begin
    assume p;
    apply prop_ext;
    apply ∧ᵢ
    { assume H; apply ⊤ᵢ }
    { assume H; rewrite left imp_eq_or; apply ∨ᵢ₁; refine neg_⊥ }
end;

opaque symbol implies_simplify3 p : π ((p ⇒ ⊤) = ⊤) ≔
begin
    assume p;
    apply prop_ext;
    apply ∧ᵢ
    { assume H; apply ⊤ᵢ }
    { assume H H2; apply ⊤ᵢ  }
end;

opaque symbol implies_simplify4 p : π ((⊤ ⇒ p) = p) ≔
begin
    assume p;
    apply prop_ext;
    apply ∧ᵢ
    { 
        assume H;
        have H1: π ⊤ → π p {
            refine H
        };
        apply H1;
        apply ⊤ᵢ
    }
    { assume H H2; apply H }
end;

opaque symbol implies_simplify5 p : π ((p ⇒ ⊥) = ¬ p) ≔
begin
    assume p;
    apply prop_ext;
    apply ∧ᵢ
    { 
        assume H;
        have H1: π p → π ⊥ {
            refine H
        };
        refine H1
    }
    { assume H H2; apply (fold_⇒ H) H2  }
end;

opaque symbol implies_simplify6 p : π ((p ⇒ p) = ⊤) ≔
begin
    assume p;
    apply prop_ext;
    apply ∧ᵢ
    { 
        assume H;
        apply ⊤ᵢ
    }
    { assume H H2; apply H2  }
end;

opaque symbol implies_simplify7 p : π ((¬ p ⇒ p) = p) ≔
begin
    assume p;
    apply prop_ext;
    rewrite left imp_eq_or;
    apply ∧ᵢ
    { 
        assume H;
        apply ∨ₑ H
        { assume Hnnp; apply ¬¬ₑ; refine Hnnp }
        { assume Hp; refine Hp }
    }
    { assume Hp; apply ∨ᵢ₂; apply Hp }
end;

opaque symbol implies_simplify8 p : π ((p ⇒ ¬ p) = ¬ p) ≔
begin
    assume p;
    apply prop_ext;
    rewrite left imp_eq_or;
    apply ∧ᵢ
    { 
        assume H;
        apply ∨ₑ H
        { assume Hnp; refine Hnp }
        { assume Hnp; refine Hnp }
    }
    { assume Hnp; apply ∨ᵢ₂; refine Hnp }
end;

symbol all_implies_simplify ≔ 
    (#rewrite implies_simplify1) ⸬ (#rewrite implies_simplify2) ⸬ (#rewrite implies_simplify3)
    ⸬ (#rewrite implies_simplify4) ⸬(#rewrite implies_simplify5) ⸬ (#rewrite implies_simplify6) ⸬ (#rewrite implies_simplify7) ⸬  (#rewrite implies_simplify8) ⸬  □;

symbol implies_simplify ≔ #repeat (applyAny all_implies_simplify) and #try (#reflexivity #orelse (#apply ⊤ᵢ));



// Rule 74. ite_simplify
opaque symbol ite_simplify1 a (t1 t2: τ a) : π (ite ⊤ t1 t2 = t1) ≔
begin
    assume a t1 t2;
    refine ite_ind ⊤ t1 t2 (λ u, u = t1) _ _
    {assume h; reflexivity}
    {assume contra; refine ⊥ₑ (contra ⊤ᵢ)}
end;

opaque symbol ite_simplify2 a (t1 t2: τ a) : π (ite ⊥ t1 t2 = t2) ≔
begin
    assume a t1 t2;
    refine ite_ind ⊥ t1 t2 (λ u, u = t2) _ _
    {assume h; refine ⊥ₑ h }
    {assume h; reflexivity }
end;

opaque symbol ite_simplify3 c : π ((@ite o c ⊤ ⊤) = ⊤) ≔
begin
    assume c;
    refine ite_ind c ⊤ ⊤ (λ u, u = ⊤) _ _
    {reflexivity}
    {reflexivity}
end;

opaque symbol ite_simplify4 a c (t1 t2: τ a) : π ((ite (¬ c) t1 t2) = (ite c t2 t1)) ≔
begin
    assume a c t1 t2;
    refine ite_ind (¬ c) t1 t2 (λ u, u = (ite c t2 t1)) _ _
    {
        assume hnc;
        refine ite_ind (c) t2 t1 (λ u, t1 = u) _ _
        { assume hc; refine ⊥ₑ (hnc hc) }
        { assume h; reflexivity }
    }
    {
        assume hnnc;
        refine ite_ind (c) t2 t1 (λ u, t2 = u) _ _
        { assume hc; reflexivity }
        { assume h; refine ⊥ₑ (hnnc h) }
    }
end;

opaque symbol ite_then [a] c (t1 t2: τ a) : π c → π (t1 = ite c t1 t2) ≔
begin
    assume a c t1 t2;
    assume hc;
    refine ite_ind c t1 t2 (λ u, t1 = u) _ _
    {  reflexivity }
    { assume hnc;  refine ⊥ₑ (hnc hc) }
end;

opaque symbol ite_else [a] c (t1 t2: τ a) : π (¬ c) → π (t2 = ite c t1 t2) ≔
begin
    assume a c t1 t2;
    assume hnc;
    refine ite_ind c t1 t2 (λ u, t2 = u) _ _
    { assume hc;  refine ⊥ₑ (hnc hc) }
    {  reflexivity }
end;

opaque symbol ite_simplify5 a c (t1 t2 t3: τ a) : π (ite c (ite c t1 t2) t3 = ite c t1 t3) ≔
begin
    assume a c t1 t2 t3;
    refine ite_ind (c) (ite c t1 t2) t3 (λ u, u = ite c t1 t3) _ _
    {
        assume hc;
        rewrite left ite_then c t1 t2 hc;
        rewrite left ite_then c t1 t3 hc;
        reflexivity
    }
    {
        assume hnc;
        rewrite left ite_else c t1 t3 hnc;
        reflexivity
    }
end;

opaque symbol ite_simplify6 a c (t1 t2 t3: τ a) : π (ite c t1 (ite c t2 t3) = ite c t1 t3) ≔
begin
    assume a c t1 t2 t3;
    refine ite_ind c t1 (ite c t2 t3) (λ u, u = ite c t1 t3) _ _
    {
        assume hc;
        rewrite left ite_then c t1 t3 hc;
        reflexivity
    }
    {
        assume hnc;
        rewrite left ite_else c t1 t3 hnc;
        rewrite left ite_else c t2 t3 hnc;
        reflexivity
    }
end;

opaque symbol ite_simplify7 c : π (ite c ⊤ ⊥ = c) ≔
begin
    assume c;
    refine ite_ind c ⊤ ⊥ (λ u, u = c) _ _
    {
        assume hc;
        apply prop_ext;
        apply ∧ᵢ
        { simplify; assume h; refine hc }
        { assume hcc; apply ⊤ᵢ }
    }
    {
        assume hnc;
        apply prop_ext;
        apply ∧ᵢ
        { simplify; assume h; refine ⊥ₑ h }
        { assume hc; refine hnc hc }
    }
end;

opaque symbol ite_simplify8 c : π (ite c ⊥ ⊤ = ¬ c) ≔
begin
    assume c;
    refine ite_ind c ⊥ ⊤ (λ u, u = ¬ c) _ _
    {
        assume hc;
        apply prop_ext;
        apply ∧ᵢ
        { simplify; assume h; refine ⊥ₑ h }
        { simplify; assume hnc; refine hnc hc }
    }
    {
        assume hc;
        apply prop_ext;
        apply ∧ᵢ
        { simplify; assume h; refine hc }
        { assume hcc; apply ⊤ᵢ }
    }
end;

opaque symbol ite_simplify9 c t : π (ite c ⊤ t = (c ∨ t)) ≔
begin
    assume c t;
    refine ite_ind c ⊤ t (λ u, u = (c ∨ t)) _ _
    {
        assume hc;
        apply prop_ext;
        apply ∧ᵢ
        {assume h; apply ∨ᵢ₁; refine hc }
        {assume h; apply ⊤ᵢ}
    }
    {
        assume hnc;
        apply prop_ext;
        apply ∧ᵢ
        {assume h; apply ∨ᵢ₂; refine h }
        {assume h; apply ∨ₑ h { assume hc; refine ⊥ₑ (hnc hc) } { refine λ x, x }}
    }
end;

opaque symbol ite_simplify10 c t : π ((ite c t ⊥) = (c ∧ t)) ≔
begin
    assume c t;
    refine ite_ind c t ⊥ (λ u, u = (c ∧ t)) _ _
    {
        assume hc;
        apply prop_ext;
        apply ∧ᵢ
        { assume ht; apply ∧ᵢ { refine hc } { refine ht }  }
        { assume h; apply ∧ₑ₂ h }
    }
    {
        assume hc;
        apply prop_ext;
        apply ∧ᵢ
        { assume contra; refine ⊥ₑ contra }
        { assume h; refine hc _; refine ∧ₑ₁ h }
    }
end;

opaque symbol ite_simplify11 c t : π (ite c ⊥ t = ((¬ c) ∧ t)) ≔
begin
    assume c t;
    refine ite_ind c ⊥ t (λ u, u = ((¬ c) ∧ t)) _ _
    {
        assume hc;
        apply prop_ext;
        apply ∧ᵢ
        { assume hcontra; refine ⊥ₑ hcontra }
        { assume h; refine ∧ₑ₁ h _; refine hc }
    }
    {
        assume hnc;
        apply prop_ext;
        apply ∧ᵢ
        { assume ht; apply ∧ᵢ { refine hnc } { refine ht } }
        { assume h; refine ∧ₑ₂ h }
    }
end;

opaque symbol ite_simplify12 c t : π (ite c t ⊤ = ((¬ c) ∨ t)) ≔
begin
    assume c t;
    refine ite_ind c t ⊤ (λ u, u = ((¬ c) ∨ t)) _ _
    {
        assume hc;
        apply prop_ext;
        apply ∧ᵢ
        { assume ht; apply ∨ᵢ₂; refine ht }
        { assume h; apply ∨ₑ h { assume hnc; refine ⊥ₑ (hnc hc) } { refine λ x, x } }
    }
    {
        assume hnc;
        apply prop_ext;
        apply ∧ᵢ
        { assume h; apply ∨ᵢ₁; refine hnc }
        {
            assume h;
            apply ∨ₑ h
            { assume h2; apply ⊤ᵢ }
            { assume h2; apply ⊤ᵢ }
        }
    }
end;

symbol all_ite_simplify a ≔ 
    (#rewrite (ite_simplify1 a))
    ⸬ (#rewrite (ite_simplify2 a))
    ⸬ (#rewrite ite_simplify3)
    ⸬ (#rewrite (ite_simplify4 a)) 
    ⸬ (#rewrite (ite_simplify5 a)) 
    ⸬ (#rewrite (ite_simplify6 a)) 
    ⸬ (#rewrite ite_simplify7) 
    ⸬ (#rewrite ite_simplify8) 
    ⸬ (#rewrite ite_simplify9) 
    ⸬ (#rewrite ite_simplify10)
    ⸬ (#rewrite ite_simplify11)
    ⸬  (#rewrite ite_simplify12)
    ⸬ □;

symbol ite_simplify [a] ≔ #repeat (applyAny (all_ite_simplify a)) and #try (#reflexivity #orelse (#apply ⊤ᵢ));

// Rule 73: ac_simp
symbol ac_simp_and ≔ #repeat (#rewrite_gen "left" "" ∧_assoc) and #repeat (#rewrite ∧_idem) and #reflexivity;
symbol ac_simp_or ≔ #repeat (#rewrite_gen "left" "" ∨_assoc) and #repeat (#rewrite ∨_idem) and #reflexivity;

opaque symbol eq_symm [a] [x y: τ a] : π̇ ((x = y) = ((y = x)) ⟇ ▩) ≔
begin
  assume a x y;
  apply ∨ᵢ₁;
  apply prop_ext;
  apply ∧ᵢ
  { assume H; symmetry; apply H }
  { assume H; symmetry; apply H }
end;