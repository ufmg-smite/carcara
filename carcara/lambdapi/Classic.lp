require open Stdlib.Prop;
require open Stdlib.FOL;
require open Stdlib.Set;

notation ¬ prefix 35;

injective symbol πᶜ p ≔ π (¬ ¬ p);

constant symbol ⊥ᶜₑ [p] : πᶜ ⊥ → πᶜ p;

symbol ∧ᶜ p q ≔ ¬ ¬ p ∧ ¬ ¬ q; notation ∧ᶜ infix right 30;

opaque symbol ∧ᶜᵢ [p q] : πᶜ p → πᶜ q → πᶜ (p ∧ᶜ q) ≔
begin
  assume p q Hp Hq;
  assume Hnnp_and_Hnnq;
  apply Hnnp_and_Hnnq;
  apply ∧ᵢ
  { assume Hnp; apply Hp;  refine Hnp }
  { assume Hnq; apply Hq;  refine Hnq }
end;

opaque  symbol ∧ᶜₑ₁ [p q] : πᶜ (p ∧ᶜ q) → πᶜ p ≔
begin
  assume p q Hp_and_q;
  assume Hnp;
  apply Hp_and_q;
  assume Hnnp_and_nnq;
  refine (∧ₑ₁ Hnnp_and_nnq) Hnp;
end;

opaque  symbol ∧ᶜₑ₂ [p q] : πᶜ (p ∧ᶜ q) → πᶜ q ≔
begin
  assume p q Hp_and_q;
  assume Hnq;
  apply Hp_and_q;
  assume Hnnp_and_nnq;
  refine (∧ₑ₂ Hnnp_and_nnq) Hnq;
end;

symbol ⇒ᶜ p q ≔ ¬ ¬ p ⇒ ¬ ¬ q; notation ⇒ᶜ infix right 10;

opaque symbol ⇒ᶜᵢ' [p q]: (πᶜ p → πᶜ q) → πᶜ (p ⇒ q) ≔
begin
  simplify;
  assume p q Hpimpq;  
  assume H;
  apply  Hpimpq
  { assume Hnp; apply H; assume Hp; apply ⊥ₑ; apply Hnp Hp  }
  { assume Hq; apply H; assume Hp; apply Hq };
end;

opaque symbol ⇒ᶜᵢ [p q]: (πᶜ p → πᶜ q) → πᶜ (p ⇒ᶜ q) ≔
begin
  assume p q Hpimpq;  
  assume H;
  apply H;
  assume Hnnp Hnq;
  apply (Hpimpq Hnnp Hnq)
end;

opaque symbol ⇒ᶜₑ [p q]: πᶜ (p ⇒ᶜ q) → πᶜ p → πᶜ q ≔
begin
  assume p q Hpimpq Hnnp Hq;  
  apply Hpimpq;
  assume H;
  refine (H Hnnp Hq) 
end;

symbol ∀ᶜ [a] p ≔ `∀ x : τ a, ¬ ¬ (p x); notation ∀ᶜ quantifier;

opaque symbol ∀ᶜᵢ [a] p : (Π (x: τ a), πᶜ (p x)) → πᶜ (∀ᶜ p) ≔
begin
  assume a p Hnnpx Hnnnpx;
  apply Hnnnpx;
  assume x Hnnp;
  apply Hnnpx x;
  assume Hnp;
  apply Hnnp;
  apply Hnp
end;

opaque symbol ∀ᶜₑ [a p] (x: τ a) : πᶜ (∀ᶜ p) → πᶜ (p x) ≔
begin
  assume a p x Hnnforallnnp Hnnpx;
  apply Hnnforallnnp;
  assume Hforallnnp;
  refine Hforallnnp x Hnnpx
end;


symbol ∃ᶜ [a] p ≔ `∃ x : τ a, ¬ ¬ (p x); notation ∃ᶜ quantifier;

opaque symbol ∃ᶜᵢ [a] p (x: τ a) : πᶜ (p x) → πᶜ (∃ᶜ p) ≔
begin
  assume a p x Hpx;
  assume Hnnnex;
  apply Hnnnex;
  apply ∃ᵢ
  { refine x; }
  { refine Hpx };
end;

opaque symbol ∃ᶜₑ [a] p : πᶜ (∃ᶜ p) → Π q, (Π x:τ a, πᶜ (p x) → πᶜ q) → πᶜ q ≔
begin
  assume a p Hexp q H;
  assume Hnq;
  apply Hexp;
  admit
  // apply ∃ₑ _ H2;
  // assume x Hnnp;
  // apply (H x Hnnp Hnq);
end;

symbol ∨ᶜ p q ≔ ¬ ¬ p ∨ ¬ ¬ q; notation ∨ᶜ infix right 20;

opaque symbol ∨ᶜᵢ₁ [p q] : πᶜ p → πᶜ (p ∨ᶜ q) ≔
begin
  assume p q Hnnp;
  assume Hnnp_or_nnq;
  apply Hnnp_or_nnq;
  apply ∨ᵢ₁;
  refine Hnnp;
end;

opaque symbol ∨ᶜᵢ₂ [p q] : πᶜ q → πᶜ (p ∨ᶜ q) ≔
begin
  assume p q Hnnp;
  assume Hnnp_or_nnq;
  apply Hnnp_or_nnq;
  apply ∨ᵢ₂;
  refine Hnnp;
end;

opaque symbol ∨ᶜₑ [p q r] : πᶜ (p ∨ᶜ q) → (πᶜ p → πᶜ r) → (πᶜ q → πᶜ r) → πᶜ r ≔
begin
  assume p q r Hnnp_or_nnq Hnnp→nr Hnnq→nr Hr→⊥;
  apply Hnnp_or_nnq;
  assume H;
  apply ∨ₑ H 
  { assume Hnnp; apply Hnnp→nr Hnnp Hr→⊥ }
  { assume Hnnq; apply Hnnq→nr Hnnq Hr→⊥ }
end;

opaque symbol ¬ᶜᵢ [p] : (πᶜ p → πᶜ ⊥) → πᶜ (¬ p) ≔
begin
  assume p Hnp;
  assume Hnnp;
  apply Hnnp;
  assume Hp;
  apply Hnp Hnnp;
  assume Hbot;
  refine Hbot;
end;

opaque symbol ¬ᶜₑ [p q] : πᶜ (¬ p) → πᶜ p → πᶜ q ≔
begin
  assume p q Hnnnp Hnnp Hnq;
  refine Hnnnp Hnnp 
end;

opaque symbol classic [p] : πᶜ (p ∨ᶜ ¬ p) ≔
begin
  assume p H;
  apply H;
  apply ∨ᵢ₁;
  assume Hnp;
  apply H;
  apply ∨ᵢ₂;
  assume Hnnp;
  apply Hnnp;
  refine Hnp
end;

opaque symbol nnpp [p] : πᶜ (¬ ¬ p) → πᶜ p ≔
begin
  assume p H_nn_p H_p⟹⊥;
  apply H_nn_p;
  assume H_nnn_p;
  apply H_nnn_p;
  assume H_np;
  apply H_p⟹⊥ H_np
end;

opaque symbol pierce [p] : πᶜ ((p ⇒ᶜ ⊥) ⇒ᶜ p) → πᶜ p ≔
begin
  assume p H_cl_p⇒ᶜ⊥⇒ᶜp Hnp;
  apply H_cl_p⇒ᶜ⊥⇒ᶜp;
  assume H_Int_p⇒ᶜ⊥⇒ᶜp;
  apply H_Int_p⇒ᶜ⊥⇒ᶜp
  {
    assume Hnnp⇒ᶜ⊥;
    apply Hnnp⇒ᶜ⊥;
    assume Hp⇒ᶜ⊥;
    assume Hnn⊥;
    apply Hnn⊥;
    apply Hp⇒ᶜ⊥;
    assume HP;
    apply Hnp HP 
  }
  { refine Hnp };
end;

opaque symbol imply_to_or [p q] : πᶜ (p ⇒ᶜ q) → πᶜ ((¬ p) ∨ᶜ q) ≔
begin
  assume p q Hp⇒ᶜq⇒ᶜ⊥ Hnnnp_or_nnq;
  apply Hp⇒ᶜq⇒ᶜ⊥;
  assume Hp⇒ᶜq;
  apply Hp⇒ᶜq
  {
    assume Hnnp;
    apply Hnnnp_or_nnq;
    apply ∨ᵢ₁;
    assume Hnnnp;
    apply Hnnnp Hnnp
  }
  {
    assume Hq;
    apply Hnnnp_or_nnq;
    apply ∨ᵢ₂;
    assume Hqimpbot;
    apply Hqimpbot Hq
  };
end;

opaque symbol imply_to_and [p q] : πᶜ (¬ (p ⇒ᶜ q)) → πᶜ (p ∧ᶜ (¬ q)) ≔
begin
  assume p q Hnpimq Hnnp_and_nnnq;
  apply Hnpimq;
  assume Hnnp_imp_nnnq;
  apply Hnnp_imp_nnnq;
  assume Hnnp Hnq;
  apply Hnnp_and_nnnq;
  apply ∧ᵢ
  { refine Hnnp; }
  { assume Hnq_imp_bot; apply Hnq_imp_bot Hnq }
end;

opaque symbol or_to_imply [p q] : πᶜ ((¬ p) ∨ᶜ q) → πᶜ (p ⇒ᶜ q) ≔
begin
  assume p q Hn_porq Hnnpnnq⊥;
  apply Hnnpnnq⊥;
  assume Hnnp Hnq;
  apply Hn_porq;
  assume Hnnpornq;
  apply ∨ₑ Hnnpornq
  { assume Hnnnp; apply Hnnnp; refine Hnnp }
  { assume Hnnnq; apply Hnnnq; refine Hnq };
end;

opaque symbol not_and_or [p q] : πᶜ (¬ (p ∧ᶜ q)) → πᶜ (¬ p ∨ᶜ ¬ q) ≔
begin
  assume p q H H1;
  apply H;
  assume H2;
  apply H2;
  apply ∧ᵢ
  {
      assume Hnnp;
      apply H1;
      apply ∨ᵢ₁;
      assume Hnnp_imp_bot;
      apply Hnnp_imp_bot Hnnp;
  }
  {
      assume Hnnq;
      apply H1;
      apply ∨ᵢ₂;
      assume Hnnq_imp_bot;
      apply Hnnq_imp_bot Hnnq;
  }
end;

opaque symbol or_not_and [p q] : πᶜ (¬ p ∨ᶜ ¬ q) → πᶜ (¬ (p ∧ᶜ q)) ≔
begin
  assume p q;
  assume Hnp_or_nq_imp_bot;
  assume  Hn_pandq;
  apply Hn_pandq;
  assume Hnnp_and_nnq;
  apply Hnp_or_nq_imp_bot;
  assume Hnnnp_or_nnnq;
  apply ∨ₑ Hnnnp_or_nnnq
  { assume Hnnp_imp_bot; apply Hnnp_imp_bot (∧ₑ₁ Hnnp_and_nnq) }
  { assume Hnnp_imp_bot; apply Hnnp_imp_bot (∧ₑ₂ Hnnp_and_nnq) }
end;

opaque symbol not_or_and [p q] : πᶜ (¬ (p ∨ᶜ q)) → πᶜ (¬ p ∧ᶜ ¬ q) ≔
begin
  assume p q Hn_p_or_q Hn_npandnq;
  apply Hn_npandnq;
  apply ∧ᵢ
  {
      assume Hnnp;
      apply Hn_p_or_q;
      assume Hn_p_or_q_intui;
      apply Hn_p_or_q_intui;
      apply ∨ᵢ₁;
      refine Hnnp;
  }
  {
      assume Hnnp;
      apply Hn_p_or_q;
      assume Hn_p_or_q_intui;
      apply Hn_p_or_q_intui;
      apply ∨ᵢ₂;
      refine Hnnp;
  }
end;

opaque symbol and_not_or [p q] : πᶜ (¬ p ∧ᶜ ¬ q) → πᶜ (¬ (p ∨ᶜ q)) ≔
begin
  assume p q H1 H2;
  apply H2;
  assume H3;
  apply ∨ₑ H3
  {
    assume Hnnp;
    apply H1;
    assume H4;
    apply (∧ₑ₁ H4) Hnnp 
  }
  {
    assume Hnnq;
    apply H1;
    assume H4;
    apply (∧ₑ₂ H4) Hnnq 
  }
end;

symbol ¬ᶜ p : πᶜ (p ⇒ᶜ ⊥); notation ¬ᶜ prefix 20;

// symbol neg_bot : πᶜ (¬ ⊥) ≔
// begin
//   simplify;

// end;

opaque πᶜ;
opaque ∧ᶜ;
opaque ∨ᶜ;
opaque ∀ᶜ;
opaque ∃ᶜ;
opaque ⇒ᶜ;

symbol ⇔ᶜ p q ≔ (p ⇒ᶜ q) ∧ᶜ (q ⇒ᶜ p); notation ⇔ᶜ infix right 5;

opaque symbol ∨ᶜ_com [x y] : πᶜ (x ∨ᶜ y) → πᶜ (y ∨ᶜ x) ≔
begin
assume x y hxy;
apply ∨ᶜₑ hxy
{ assume hx; apply ∨ᶜᵢ₂; apply hx }
{ assume hy; apply ∨ᶜᵢ₁; apply hy }
end;

opaque symbol ∨ᶜ_assoc [x y z] : πᶜ (x ∨ᶜ y ∨ᶜ z ⇔ᶜ (x ∨ᶜ y) ∨ᶜ z) ≔
begin
  assume x y z;
  apply ∧ᶜᵢ
  {
    apply ⇒ᶜᵢ;
    assume Hxyz;
    apply ∨ᶜₑ Hxyz
    { assume Hx; apply ∨ᶜᵢ₁; apply ∨ᶜᵢ₁; apply Hx }
    {
      assume Hyz;
      apply ∨ᶜₑ Hyz
      { assume Hy; apply ∨ᶜᵢ₁; apply ∨ᶜᵢ₂; apply Hy }
      { assume Hz; apply ∨ᶜᵢ₂; apply Hz }
    }
  }
  {
    apply ⇒ᶜᵢ;
    assume Hxyz;
    apply ∨ᶜₑ Hxyz
    {
      assume Hxy;
      apply ∨ᶜₑ Hxy
      { assume Hx; apply ∨ᶜᵢ₁; refine Hx }
      { assume Hy; apply ∨ᶜᵢ₂; apply ∨ᶜᵢ₁; refine Hy }
    }
    { assume Hz; apply ∨ᶜᵢ₂; apply ∨ᶜᵢ₂; refine Hz }
  };
end;

opaque symbol ∧ᶜ_com [x y] : πᶜ (x ∧ᶜ y) → πᶜ (y ∧ᶜ x) ≔
begin
  assume x y Hx_and_y;
  apply ∧ᶜᵢ
  { apply ∧ᶜₑ₂ Hx_and_y }
  { apply ∧ᶜₑ₁ Hx_and_y };
end;

opaque symbol ∧ᶜ_assoc [x y z] : πᶜ (x ∧ᶜ y ∧ᶜ z ⇔ᶜ (x ∧ᶜ y) ∧ᶜ z) ≔
begin
  assume x y z;
  apply ∧ᶜᵢ
  {
    apply ⇒ᶜᵢ;
    assume Hxyz;
    apply ∧ᶜᵢ
    {
      apply ∧ᶜᵢ
      { refine ∧ᶜₑ₁ Hxyz }
      { refine ∧ᶜₑ₁ (∧ᶜₑ₂ Hxyz) }
    }
    { refine ∧ᶜₑ₂ (∧ᶜₑ₂ Hxyz) }
  }
  {
    apply ⇒ᶜᵢ;
    assume Hxyz;
    apply ∧ᶜᵢ
    { refine ∧ᶜₑ₁ (∧ᶜₑ₁ Hxyz) }
    {
      apply ∧ᶜᵢ
      { refine ∧ᶜₑ₂ (∧ᶜₑ₁ Hxyz) }
      { refine ∧ᶜₑ₂ Hxyz }
    }
  };
end;

opaque symbol ⇔ᶜ_refl [p] : πᶜ (p ⇔ᶜ p) ≔
begin
  assume p;
  apply ∧ᶜᵢ
  { apply ⇒ᶜᵢ; assume h; apply h }
  { apply ⇒ᶜᵢ; assume h; apply h }
end;

opaque symbol ⇔ᶜ_sym [p q] : πᶜ (p ⇔ᶜ q) → πᶜ (q ⇔ᶜ p) ≔
begin
  assume p q h; apply ∧ᶜᵢ { apply ∧ᶜₑ₂ h } { apply ∧ᶜₑ₁ h };
end;

opaque symbol ⇔ᶜ_trans p q r : πᶜ (p ⇔ᶜ q) → πᶜ (q ⇔ᶜ r) → πᶜ (p ⇔ᶜ r) ≔
begin
  assume p q r epq eqr; apply ∧ᶜᵢ
    { apply ⇒ᶜᵢ; assume hp; refine ⇒ᶜₑ (∧ᶜₑ₁ eqr) (⇒ᶜₑ (∧ᶜₑ₁ epq) hp) }
    { apply ⇒ᶜᵢ; assume hr; refine ⇒ᶜₑ (∧ᶜₑ₂ epq) (⇒ᶜₑ (∧ᶜₑ₂ eqr) hr) }
end;

opaque symbol nforall_ex [a] p : πᶜ ((¬ (`∀ᶜ (x : τ a), p x)) ⇔ᶜ (`∃ᶜ (x : τ a), ¬ p x)) ≔ begin admit end;

opaque symbol nex_forall [a] p : πᶜ ((¬ (`∃ᶜ (x : τ a), p x)) ⇔ᶜ (`∀ᶜ (x : τ a), ¬ p x)) ≔ begin admit end;