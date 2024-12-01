require open Stdlib.Prop;
require open Stdlib.FOL;
require open Stdlib.Set;
require open Stdlib.Eq;
require open lambdapi.Classic;
require open lambdapi.Alethe;

// symbol o: Set;
// rule τ o ↪ Prop;


constant symbol eq_reflᶜ [a] (x:τ a) : πᶜ (x = x);
constant symbol ind_eqᶜ [a] [x y:τ a] : πᶜ (x = y) → Π p, πᶜ (p y) → πᶜ (p x);

// builtin "P"     ≔ πᶜ; // : Prop → TYPE
// builtin "refl"  ≔ eq_reflᶜ; // : Π [a] (x:T a), P(x = x)
// builtin "eqind" ≔ ind_eqᶜ; // : Π [a] x y, P(x = y) → Π p:T a → Prop, P(p y) → P(p x)


notation ¬ prefix 35;

// Use it to unfold the definition of `¬`.
// The tactic simplify is to agressive.
opaque symbol negdef p : πᶜ ((p ⇒ ⊥) = ¬ p) ≔
begin
    simplify;
    reflexivity
end;

// Rule 71: equiv_simplify

symbol equiv_simplify₁ p q : πᶜ (((¬ p) = ¬ q) = (p = q)) ≔
begin
    assume p q;
    apply prop_ext;
    apply ∧ᶜᵢ
    {
        apply ⇒ᶜᵢ;
        assume Heq;
        apply prop_ext; 
        apply ∧ᶜᵢ
        {
            rewrite left imp_eq_or;
            rewrite Heq;
            rewrite or_com;
            apply classic
        }
        {
            rewrite left imp_eq_or;
            rewrite left Heq;
            rewrite or_com;
            apply classic
        }
    }
    {
        apply ⇒ᶜᵢ;
        assume Heq;
        rewrite Heq;
        reflexivity
    }
end;

symbol equiv_simplify₂ [a] (p: τ a) : πᶜ ((p = p) = ⊤) ≔
begin
    assume a p;
    apply prop_ext;
    apply ∧ᶜᵢ
    { apply ⇒ᶜᵢ; assume H; remove H; apply trivial }
    { apply ⇒ᶜᵢ; assume H⊤; remove H⊤; reflexivity }
end;

symbol equiv_simplify₃ p : πᶜ ((p = (¬ p)) = ⊥) ≔
begin
    assume p;
    apply prop_ext;
    rewrite left iff_equiv_eq;
    simplify;
    rewrite left imp_eq_or;
    rewrite left imp_eq_or;
    rewrite left imp_eq_or;
    rewrite left imp_eq_or;
    apply ∧ᶜᵢ
    {
        rewrite or_identity_r;
        rewrite morgan₁;
        rewrite .[¬ ((¬ (p ⇒ ⊥)) ∨ᶜ p)] morgan₂;
        rewrite distributive_or;
        rewrite negdef;
        rewrite or_idempotent;
        apply ∧ᶜᵢ
        {
            apply classic
        }
        {
            rewrite or_com;
            apply classic
        };
    }
    {
        rewrite negdef;
        apply ∨ᶜᵢ₁;
        refine neg_⊥
    }
end;

symbol equiv_simplify₄ p : πᶜ ((p = ⊤) = p) ≔
begin
    assume p;
    apply prop_ext;
    rewrite left iff_equiv_eq;
    apply ∧ᶜᵢ
    {
        apply ⇒ᶜᵢ;
        assume H;
        have H2: πᶜ (⊤ ⇒ᶜ p) { apply ∧ᶜₑ₂ H };
        apply ⇒ᶜₑ H2;
        apply trivial
    }
    {
        apply ⇒ᶜᵢ;
        assume Hp;
        apply ∧ᶜᵢ
        { apply ⇒ᶜᵢ; assume Hp'; apply trivial }
        { apply ⇒ᶜᵢ; assume Htop; apply Hp }
    }
end;

symbol equiv_simplify₅ p : πᶜ ((p = ⊥) = ¬ p) ≔
begin
    assume p;
    simplify;
    apply prop_ext;
    rewrite left iff_equiv_eq;
    apply ∧ᶜᵢ
    {
        apply ⇒ᶜᵢ;
        assume H;
        apply meta-arr;
        assume Hp;
        apply ⇒ᶜₑ (∧ᶜₑ₁ H) Hp
    }
    {
        apply ⇒ᶜᵢ;
        assume H;
        apply ∧ᶜᵢ
        {
            apply ⇒ᶜᵢ;
            assume Hp;
            apply fold_⇒ᶜ H Hp;
        }
        {
            apply ⇒ᶜᵢ;
            assume Hbot;
            apply ⊥ᶜₑ;
            apply Hbot
        }
    };
end;

symbol equiv_simplify₆ p : πᶜ ((⊥ = p) = ¬ p) ≔
begin
    assume p;
    admit //FIXME: need sym
end;

// Rule 69: not_simplify

opaque symbol not_simplify₁ t : πᶜ ((¬ (¬ t)) = t) ≔
begin
    assume t;
    apply prop_ext;
    apply ∧ᶜᵢ
    {
        rewrite nnpp_eq;
        apply ⇒ᶜᵢ;
        assume Ht;
        apply Ht
    }
    {
        rewrite nnpp_eq;
        apply ⇒ᶜᵢ;
        assume Ht;
        apply Ht
    }
end;

opaque symbol not_simplify₂ : πᶜ ((¬ ⊥) = ⊤) ≔
begin
    simplify;
    apply prop_ext;
    apply ∧ᶜᵢ
    { apply ⇒ᶜᵢ; assume H; apply trivial }
    { apply ⇒ᶜᵢ; assume Htop; apply meta-arr; assume Hbot; refine Hbot }
end;

opaque symbol not_simplify₃ : πᶜ ((¬ ⊤) = ⊥) ≔
begin
    simplify;
    apply prop_ext;
    apply ∧ᶜᵢ
    { apply ⇒ᶜᵢ; assume H; apply fold_⇒ᶜ H; apply trivial }
    { apply ⇒ᶜᵢ; assume Hbot; apply ⊥ᶜₑ; refine Hbot }
end;

// Rule 70: implies_simplify

opaque symbol implies_simplify₁ p q : πᶜ (( (¬ p) ⇒ᶜ (¬ q)) = (q ⇒ᶜ p)) ≔
begin
    assume p q;
    apply prop_ext;
    apply ∧ᶜᵢ
    { 
        apply  ⇒ᶜᵢ; assume H; rewrite left imp_eq_or;
        have H1: πᶜ ((¬ ¬ p) ∨ᶜ ¬ q) { rewrite imp_eq_or; refine H };
        apply ∨ᶜₑ H1
        { assume Hnnp;  apply ∨ᶜᵢ₂; apply nnpp; refine Hnnp }
        { assume Hnq;  apply ∨ᶜᵢ₁; refine Hnq }
    }
    {
        apply  ⇒ᶜᵢ; assume H; rewrite left imp_eq_or;
        have H1: πᶜ ((¬ q) ∨ᶜ p) { rewrite imp_eq_or; refine H };
        apply ∨ᶜₑ H1
        { assume Hnq;  apply ∨ᶜᵢ₂; refine Hnq }
        { assume Hp;  apply ∨ᶜᵢ₁; rewrite not_simplify₁; refine Hp }
    }
end;

opaque symbol implies_simplify₂ p : πᶜ ((⊥ ⇒ᶜ p) = ⊤) ≔
begin
    assume p;
    apply prop_ext;
    apply ∧ᶜᵢ
    { apply ⇒ᶜᵢ; assume H; apply trivial }
    { apply ⇒ᶜᵢ; assume H; rewrite left imp_eq_or; apply ∨ᶜᵢ₁; refine neg_⊥ }
end;

opaque symbol implies_simplify₃ p : πᶜ ((p ⇒ᶜ ⊤) = ⊤) ≔
begin
    assume p;
    apply prop_ext;
    apply ∧ᶜᵢ
    { apply ⇒ᶜᵢ; assume H; apply trivial }
    { apply ⇒ᶜᵢ; assume H; apply ⇒ᶜᵢ; assume H2; apply trivial  }
end;

opaque symbol implies_simplify₄ p : πᶜ ((⊤ ⇒ᶜ p) = p) ≔
begin
    assume p;
    apply prop_ext;
    apply ∧ᶜᵢ
    { 
        apply ⇒ᶜᵢ; assume H;
        have H1: πᶜ ⊤ → πᶜ p {
            refine ⇒ᶜₑ H
        };
        apply H1;
        apply trivial
    }
    { apply ⇒ᶜᵢ; assume H; apply ⇒ᶜᵢ; assume H2; apply H }
end;

opaque symbol implies_simplify₅ p : πᶜ ((p ⇒ᶜ ⊥) = ¬ p) ≔
begin
    assume p;
    apply prop_ext;
    apply ∧ᶜᵢ
    { 
        apply ⇒ᶜᵢ; assume H;
        have H1: πᶜ p → πᶜ ⊥ {
            refine ⇒ᶜₑ H
        };
        apply meta-arr;
        refine H1
    }
    { apply ⇒ᶜᵢ; assume H; apply ⇒ᶜᵢ; assume H2; apply (fold_⇒ᶜ H) H2  }
end;

opaque symbol implies_simplify₆ p : πᶜ ((p ⇒ᶜ p) = ⊤) ≔
begin
    assume p;
    apply prop_ext;
    apply ∧ᶜᵢ
    { 
        apply ⇒ᶜᵢ; assume H;
        apply trivial
    }
    { apply ⇒ᶜᵢ; assume H; apply ⇒ᶜᵢ; assume H2; apply H2  }
end;

opaque symbol implies_simplify₇ p : πᶜ (((¬ p) ⇒ᶜ p) = p) ≔
begin
    assume p;
    apply prop_ext;
    rewrite left imp_eq_or;
    apply ∧ᶜᵢ
    { 
        apply ⇒ᶜᵢ; assume H;
        apply ∨ᶜₑ H
        { assume Hnnp; apply nnpp; refine Hnnp }
        { assume Hp; refine Hp }
    }
    { apply ⇒ᶜᵢ; assume Hp; apply ∨ᶜᵢ₂; apply Hp }
end;

opaque symbol implies_simplify₈ p : πᶜ ((p ⇒ᶜ ¬ p) = ¬ p) ≔
begin
    assume p;
    apply prop_ext;
    rewrite left imp_eq_or;
    apply ∧ᶜᵢ
    { 
        apply ⇒ᶜᵢ; assume H;
        apply ∨ᶜₑ H
        { assume Hnp; refine Hnp }
        { assume Hnp; refine Hnp }
    }
    { apply ⇒ᶜᵢ; assume Hnp; apply ∨ᶜᵢ₂; refine Hnp }
end;


// Rule 74. ite_simplify
// opaque symbol ite_simplify₁ t1 t2 : πᶜ (ite ⊤ t1 t2 = t1) ≔
// begin
//     assume t1 t2;
//     simplify;
//     apply prop_ext;
//     apply ∧ᶜᵢ
//     {
//         apply ⇒ᶜᵢ;
//         assume H;
//         apply ⇒ᶜₑ (∧ᶜₑ₁ H);
//         apply trivial
//     }
//     {
//         apply ⇒ᶜᵢ;
//         assume H;
//         apply ∧ᶜᵢ
//         {
//             apply ⇒ᶜᵢ;
//             assume Ht1;
//             apply H;
//         }
//         {
//             apply ⇒ᶜᵢ;
//             assume Ht1;
//             apply ⊥ᶜₑ;
//             apply fold_⇒ᶜ Ht1;
//             apply trivial
//         }
//     }    
// end;

// opaque symbol ite_simplify₂ t1 t2 : πᶜ (ite ⊥ t1 t2 = t2) ≔
// begin
//     assume t1 t2;
//     simplify;
//     apply prop_ext;
//     apply ∧ᶜᵢ
//     {
//         apply ⇒ᶜᵢ;
//         assume H;
//         apply ⇒ᶜₑ (∧ᶜₑ₂ H);
//         apply meta-arr;
//         assume Hbot;
//         apply Hbot
//     }
//     {
//         apply ⇒ᶜᵢ;
//         assume Ht2;
//         apply ∧ᶜᵢ
//         {
//             apply ⇒ᶜᵢ;
//             assume Ht1;
//             apply ⊥ᶜₑ Ht1;
//         }
//         {
//             apply ⇒ᶜᵢ;
//             assume Hbot;
//             apply Ht2;
//         }
//     }    
// end;

// opaque symbol ite_simplify₃ c : πᶜ (ite c ⊤ ⊤ = ⊤) ≔
// begin
//     assume c;
//     simplify;
//     apply prop_ext;
//     apply ∧ᶜᵢ
//     {
//         apply ⇒ᶜᵢ;
//         assume H;
//         apply trivial
//     }
//     {
//         apply ⇒ᶜᵢ;
//         assume Ht2;
//         apply ∧ᶜᵢ
//         {
//             apply ⇒ᶜᵢ;
//             assume Ht1;
//             apply trivial
//         }
//         {
//             apply ⇒ᶜᵢ;
//             assume Hbot;
//             apply trivial;
//         }
//     }    
// end;

// opaque symbol ite_simplify₄ c t1 t2 : πᶜ (ite (¬ c) t1 t2 = ite c t2 t1) ≔
// begin
//     assume c t1 t2;
//     admit
// end;

// opaque symbol ite_simplify₅ c t1 t2 t3 : πᶜ (ite c (ite c t1 t2) t3 = ite c t1 t3) ≔
// begin
//     assume c t1 t2;
//     admit
// end;

// opaque symbol ite_simplify₆ c t1 t2 t3 : πᶜ (ite c t1 (ite c t2 t3) = ite c t1 t3) ≔
// begin
//     assume c t1 t2;
//     admit
// end;

// opaque symbol ite_simplify₇ c : πᶜ (ite c ⊤ ⊥ = c) ≔
// begin
//     assume c;
//     admit
// end;

// opaque symbol ite_simplify₈ c : πᶜ (ite c ⊥ ⊤ = ¬ c) ≔
// begin
//     assume c;
//     admit
// end;

// opaque symbol ite_simplify₉ c t : πᶜ (ite c ⊤ t = c ∨ᶜ t) ≔
// begin
//     assume c t;
//     admit
// end;

// opaque symbol ite_simplify₁₀ c t : πᶜ (ite c t ⊥ = c ∧ᶜ t) ≔
// begin
//     assume c t;
//     admit
// end;

// opaque symbol ite_simplify₁₁ c t : πᶜ (ite c ⊥ t = (¬ c) ∧ᶜ t) ≔
// begin
//     assume c t;
//     admit
// end;

// opaque symbol ite_simplify₁₂ c t : πᶜ (ite c t ⊤ = (¬ c) ∨ᶜ t) ≔
// begin
//     assume c t;
//     admit
// end;

// opaque ite;

// Rule 73: ac_simp
opaque symbol ac_simp_or p : πᶜ (p ∨ᶜ p = p) ≔ or_idempotent p;
opaque symbol ac_simp_and p : πᶜ (p ∧ᶜ p = p) ≔ and_idempotent p;

opaque symbol eq_symm [a] [x y: τ a] : π̇ ((x = y) = ((y = x)) ⟇ ▩) ≔
begin
  assume a x y;
  apply ∨ᶜᵢ₁;
  apply prop_ext;
  apply ∧ᶜᵢ
  { apply ⇒ᶜᵢ; assume H; symmetry; apply H }
  { apply ⇒ᶜᵢ; assume H; symmetry; apply H }
end;
