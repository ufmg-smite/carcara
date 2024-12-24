
require open Stdlib.Prop;

require open Stdlib.Set;

require open Stdlib.Eq;

require open Stdlib.Z;

require open lambdapi.Classic;

require open lambdapi.Alethe;

require open lambdapi.Simplify;

require open lambdapi.Rare;

require open lambdapi.Lia;


symbol f : τ (int ⤳ int);

symbol p_2 ≔ ((f 5) ≤ 4);

symbol p_3 ≔ (f 5);

symbol p_6 ≔ (~ 1 × (f 5));

symbol p_7 ≔ (~ 1 × 12);

symbol p_15 ≔ (~ 1 × (f 0));

symbol p_16 ≔ (f 0);

symbol p_17 ≔ (~ 1 × 10);

symbol p_19 ≔ ((f 0) ≤ 4);

notation ≥ infix 10;

print Zle_not_gt;

symbol t1 : πᶜ ((¬ ((p_3 ≤ 4)))  ∨ᶜ (¬ ((p_6 = p_7)))  ∨ᶜ ((p_3 + p_6) ≤ (4 + p_7)) ) ≔ 
begin
simplify p_3; simplify p_6; simplify p_7;
rewrite .[x in _ ∨ᶜ _ ∨ᶜ x] Zle_not_gt;
try rewrite Zinv_lt_eq;
try rewrite Zinv_le_eq;
rewrite Z_diff_geq_Z0_eq ((~ (f 5))) ((~ 4));
rewrite Z_diff_eq_Z0_eq ((~ 1 × (f 5))) ((~ 1 × 12));
rewrite Z_diff_gt_Z0_eq (((f 5) + (~ 1 × (f 5)))) ((4 + (~ 1 × 12)));
rewrite Zgt_le_succ_r_eq;
rewrite Zmult_ge_compat_eq (1) (((~ (f 5)) - (~ 4))) (0);
rewrite Zmult_eq_compat_eq (~ 1) (((~ 1 × (f 5)) - (~ 1 × 12))) (0);
rewrite Zmult_ge_compat_eq (1) ((((f 5) + (~ 1 × (f 5))) - (4 + (~ 1 × 12)))) ((0 + 1));
try rewrite Z_eq_antisym;
rewrite imp_eq_or;
apply ⇒ᶜᵢ;
assume H0;
rewrite imp_eq_or;
apply ⇒ᶜᵢ;
assume H1;
apply ¬ᶜᵢ;
assume H2;
set H0lhs ≔ (1 × ((~ (f 5)) - (~ 4)));
set H0rhs ≔ (1 × 0);
set H1lhs ≔ (~ 1 × ((~ 1 × (f 5)) - (~ 1 × 12)));
set H1rhs ≔ (~ 1 × 0);
set H2lhs ≔ (1 × (((f 5) + (~ 1 × (f 5))) - (4 + (~ 1 × 12))));
set H2rhs ≔ (1 × (0 + 1));
have Hsum : πᶜ (H0lhs + H1lhs + H2lhs ≥ H0rhs + H1rhs + H2rhs) {
    apply (Zsum_geq_s (Zsum_geq_s H0 H1) H2);
};
apply completude_lia _ _ Hsum;
end;


symbol Z_diff_gt_Z0_eq : Π a: ℤ, Π b: ℤ, πᶜ (¬ (a > b) =  ¬ ((a - b) > 0));

symbol t2 : πᶜ ((¬ ((p_3 < 5))) ∨ᶜ p_2) ≔ 
begin
simplify p_3; simplify p_2;
rewrite .[x in _ ∨ᶜ x] Zle_not_gt;
try rewrite Zinv_lt_eq;
try rewrite Zinv_le_eq;
rewrite Z_diff_gt_Z0_eq ((~ (f 5))) ((~ 5));
rewrite Z_diff_gt_Z0_eq ((f 5)) (4);
rewrite Zgt_le_succ_r_eq;
rewrite Zgt_le_succ_r_eq;
rewrite Zmult_ge_compat_eq (1) (((~ (f 5)) - (~ 5))) ((0 + 1));
rewrite Zmult_ge_compat_eq (1) (((f 5) - 4)) ((0 + 1));
try rewrite Z_eq_antisym;
rewrite imp_eq_or;
apply ⇒ᶜᵢ;
assume H0;
apply ¬ᶜᵢ;
assume H1;
set H0lhs ≔ (1 × ((~ (f 5)) - (~ 5)));
set H0rhs ≔ (1 × (0 + 1));
set H1lhs ≔ (1 × ((f 5) - 4));
set H1rhs ≔ (1 × (0 + 1));
have Hsum : πᶜ (H0lhs + H1lhs ≥ H0rhs + H1rhs) {
    apply (Zsum_geq_s H0 H1);
};
apply completude_lia _ _ Hsum;
end;

symbol t3 : πᶜ ((¬ ((p_15 = p_17))) ∨ᶜ (¬ ((p_16 ≤ 4)))  ∨ᶜ ((p_15 + p_16) ≤ (p_17 + 4))) ≔ 
begin
simplify p_15; simplify p_17; simplify p_16;
rewrite .[x in _ ∨ᶜ _ ∨ᶜ x] Zle_not_gt;
try rewrite Zinv_lt_eq;
try rewrite Zinv_le_eq;
try rewrite Z_diff_geq_Z0_eq;
try rewrite Z_diff_eq_Z0_eq;
try rewrite Z_diff_gt_Z0_eq;
rewrite Zgt_le_succ_r_eq;
rewrite Zmult_eq_compat_eq (~ 1) (((~ 1 × (f 0)) - (~ 1 × 10))) (0);
rewrite Zmult_ge_compat_eq (1) (((~ (f 0)) - (~ 4))) (0);
rewrite Zmult_ge_compat_eq (1) ((((~ 1 × (f 0)) + (f 0)) - ((~ 1 × 10) + 4))) ((0 + 1));
try rewrite Z_eq_antisym;
rewrite imp_eq_or;
apply ⇒ᶜᵢ;
assume H0;
rewrite imp_eq_or;
apply ⇒ᶜᵢ;
assume H1;
apply ¬ᶜᵢ;
assume H2;
set H0lhs ≔ (~ 1 × ((~ 1 × (f 0)) - (~ 1 × 10)));
set H0rhs ≔ (~ 1 × 0);
set H1lhs ≔ (1 × ((~ (f 0)) - (~ 4)));
set H1rhs ≔ (1 × 0);
set H2lhs ≔ (1 × (((~ 1 × (f 0)) + (f 0)) - ((~ 1 × 10) + 4)));
set H2rhs ≔ (1 × (0 + 1));
have Hsum : πᶜ (H0lhs + H1lhs + H2lhs ≥ H0rhs + H1rhs + H2rhs) {
    apply (Zsum_geq_s (Zsum_geq_s H0 H1) H2);
};
apply completude_lia _ _ Hsum;
end;

symbol t4 : πᶜ ((¬ ((p_16 < 5)))  ∨ᶜ p_19) ≔ 
begin
simplify p_19; simplify p_16;
rewrite .[x in _ ∨ᶜ x] Zle_not_gt;
try rewrite Zinv_lt_eq;
try rewrite Zinv_le_eq;
rewrite Z_diff_gt_Z0_eq ((~ (f 0))) ((~ 5));
rewrite Z_diff_gt_Z0_eq ((f 0)) (4);
rewrite Zgt_le_succ_r_eq (((~ (f 0)) - (~ 5))) (0);
rewrite Zgt_le_succ_r_eq (((f 0) - 4)) (0);
rewrite Zmult_ge_compat_eq (1) (((~ (f 0)) - (~ 5))) ((0 + 1));
rewrite Zmult_ge_compat_eq (1) (((f 0) - 4)) ((0 + 1));
try rewrite Z_eq_antisym;
rewrite imp_eq_or;
apply ⇒ᶜᵢ;
assume H0;
apply ¬ᶜᵢ;
assume H1;
set H0lhs ≔ (1 × ((~ (f 0)) - (~ 5)));
set H0rhs ≔ (1 × (0 + 1));
set H1lhs ≔ (1 × ((f 0) - 4));
set H1rhs ≔ (1 × (0 + 1));
have Hsum : πᶜ (H0lhs + H1lhs ≥ H0rhs + H1rhs) {
    apply (Zsum_geq_s H0 H1);
};
apply completude_lia _ _ Hsum;
end;

symbol t5 : π̇ ▩ ≔ 
begin
admit;
end;
