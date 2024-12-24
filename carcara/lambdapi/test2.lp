require open Stdlib.Prop;

require open Stdlib.Set;

require open Stdlib.Eq;

require open Stdlib.Z;

require open lambdapi.Classic;

require open lambdapi.Alethe;

require open lambdapi.Simplify;

require open lambdapi.Rare;

require open lambdapi.Lia;

symbol Idv : Set;

symbol TLA_Anon_OPAQUE_h6fbaa : τ (Idv);

symbol TLA_BoolSet : τ (Idv);

symbol TLA_Cast_Int : τ (int ⤳ Idv);

symbol TLA_FunApp : τ (Idv ⤳ Idv ⤳ Idv);

symbol TLA_FunDom : τ (Idv ⤳ Idv);

symbol TLA_FunExcept : τ (Idv ⤳ Idv ⤳ Idv ⤳ Idv);

symbol TLA_FunIsafcn : τ (Idv ⤳ o);

symbol TLA_FunSet : τ (Idv ⤳ Idv ⤳ Idv);

symbol TLA_IntLteq : τ (Idv ⤳ Idv ⤳ o);

symbol TLA_IntMinus : τ (Idv ⤳ Idv ⤳ Idv);

symbol TLA_IntRange : τ (Idv ⤳ Idv ⤳ Idv);

symbol TLA_IntSet : τ (Idv);

symbol TLA_Mem : τ (Idv ⤳ Idv ⤳ o);

symbol TLA_NatSet : τ (Idv);

symbol TLA_Proj_Int : τ (Idv ⤳ int);

symbol TLA_SetEnum_1 : τ (Idv ⤳ Idv);

symbol TLA_SetEnum_2 : τ (Idv ⤳ Idv ⤳ Idv);

symbol TLA_SetExtTrigger : τ (Idv ⤳ Idv ⤳ o);

symbol TLA_SetMinus : τ (Idv ⤳ Idv ⤳ Idv);

symbol TLA_StrLit_black : τ (Idv);

symbol TLA_StrLit_white : τ (Idv);

symbol TLA_StrSet : τ (Idv);

symbol TLA_TrigEq_Idv : τ (Idv ⤳ Idv ⤳ o);

symbol TLA_Tt_Idv : τ (Idv);

symbol CONSTANT_N_ : τ (Idv);

symbol VARIABLE_active_ : τ (Idv);

symbol VARIABLE_active_prime : τ (Idv);

symbol VARIABLE_color_ : τ (Idv);

symbol VARIABLE_color_prime : τ (Idv);

symbol VARIABLE_tpos_ : τ (Idv);

symbol VARIABLE_tpos_prime : τ (Idv);

symbol VARIABLE_tcolor_ : τ (Idv);

symbol VARIABLE_tcolor_prime : τ (Idv);

symbol STATE_Init_ : τ (Idv);

symbol ACTION_InitiateProbe_ : τ (Idv);

symbol ACTION_SendMsg_ : τ (Idv ⤳ Idv);

symbol ACTION_Deactivate_ : τ (Idv ⤳ Idv);

symbol ACTION_Controlled_ : τ (Idv);

symbol ACTION_Environment_ : τ (Idv);

symbol ACTION_Next_ : τ (Idv);

symbol STATE_vars_ : τ (Idv);

symbol TEMPORAL_Fairness_ : τ (Idv);

symbol TEMPORAL_Spec_ : τ (Idv);

symbol STATE_NeverBlack_ : τ (Idv);

symbol TEMPORAL_NeverChangeColor_ : τ (Idv);

symbol STATE_terminationDetected_ : τ (Idv);

symbol STATE_TerminationDetection_ : τ (Idv);

symbol TEMPORAL_Liveness_ : τ (Idv);

symbol TEMPORAL_AllNodesTerminateIfNoMessages_ : τ (Idv);

symbol STATE_Inv_ : τ (Idv);

symbol CONSTANT_i_ : τ (Idv);

symbol p_3 ≔ (TLA_Proj_Int VARIABLE_tpos_);

symbol p_7 ≔ ((TLA_Proj_Int CONSTANT_N_) + (~ 1 × (TLA_Proj_Int (TLA_Cast_Int (~ 1 + (TLA_Proj_Int VARIABLE_tpos_))))));

symbol p_8 ≔ (TLA_Proj_Int CONSTANT_N_);

symbol p_9 ≔ (~ 1 × (TLA_Proj_Int (TLA_Cast_Int (~ 1 + (TLA_Proj_Int VARIABLE_tpos_)))));

symbol p_10 ≔ (TLA_Proj_Int (TLA_Cast_Int (~ 1 + (TLA_Proj_Int VARIABLE_tpos_))));

symbol p_11 ≔ (TLA_Cast_Int (~ 1 + (TLA_Proj_Int VARIABLE_tpos_)));

symbol p_12 ≔ (~ 1 + (TLA_Proj_Int VARIABLE_tpos_));

symbol p_15 ≔ (~ 1 × ((TLA_Proj_Int VARIABLE_tpos_) + (~ 1 × (TLA_Proj_Int (TLA_Cast_Int (~ 1 + (TLA_Proj_Int VARIABLE_tpos_)))))));

symbol p_16 ≔ ((TLA_Proj_Int VARIABLE_tpos_) + (~ 1 × (TLA_Proj_Int (TLA_Cast_Int (~ 1 + (TLA_Proj_Int VARIABLE_tpos_))))));

symbol p_17 ≔ (~ 1 × 1);

symbol p_19 ≔ (((TLA_Proj_Int VARIABLE_tpos_) + (~ 1 × (TLA_Proj_Int CONSTANT_N_))) ≤ ~ 1);

symbol p_20 ≔ ((TLA_Proj_Int VARIABLE_tpos_) + (~ 1 × (TLA_Proj_Int CONSTANT_N_)));

symbol p_21 ≔ (~ 1 × (TLA_Proj_Int CONSTANT_N_));

notation ≥ infix 10;


symbol t1 : πᶜ ((¬ ((p_3 > 0))) ∨ᶜ (p_3 ≥ 1)) ≔ 
begin
simplify p_3;
rewrite .[x in _ ∨ᶜ x] Zge_not_lt;
try rewrite Zinv_lt_eq;
try rewrite Zinv_le_eq;
rewrite Z_diff_gt_Z0_eq ((TLA_Proj_Int VARIABLE_tpos_)) (0);
rewrite Z_diff_gt_Z0_eq ((~ (TLA_Proj_Int VARIABLE_tpos_))) ((~ 1));
rewrite Zgt_le_succ_r_eq (((TLA_Proj_Int VARIABLE_tpos_) - 0)) (0);
rewrite Zgt_le_succ_r_eq (((~ (TLA_Proj_Int VARIABLE_tpos_)) - (~ 1))) (0);
rewrite Zmult_ge_compat_eq (1) (((TLA_Proj_Int VARIABLE_tpos_) - 0)) ((0 + 1));
rewrite Zmult_ge_compat_eq (1) (((~ (TLA_Proj_Int VARIABLE_tpos_)) - (~ 1))) ((0 + 1));
try rewrite Z_eq_antisym;
rewrite imp_eq_or;
apply ⇒ᶜᵢ;
assume H0;
apply ¬ᶜᵢ;
assume H1;
set H0lhs ≔ (1 × ((TLA_Proj_Int VARIABLE_tpos_) - 0));
set H0rhs ≔ (1 × (0 + 1));
set H1lhs ≔ (1 × ((~ (TLA_Proj_Int VARIABLE_tpos_)) - (~ 1)));
set H1rhs ≔ (1 × (0 + 1));
have Hsum : πᶜ (H0lhs + H1lhs ≥ H0rhs + H1rhs) {
    apply (Zsum_geq_s H0 H1);
};
apply completude_lia _ _ Hsum;
end;

symbol t2 : πᶜ ((¬ ((p_7 < 1)))  ∨ᶜ (¬ ((p_15 = p_17)))  ∨ᶜ (¬ ((p_20 ≤ ~ 1)))  ∨ᶜ ((p_7 + p_15) < (1 + p_17))) ≔ 
begin
simplify p_7; simplify p_15; simplify p_20; simplify p_17;
rewrite .[x in _ ∨ᶜ _ ∨ᶜ _ ∨ᶜ x] Zlt_not_ge;
try rewrite Zinv_lt_eq;
try rewrite Zinv_le_eq;
rewrite Z_diff_gt_Z0_eq ((~ ((TLA_Proj_Int CONSTANT_N_) + (~ 1 × (TLA_Proj_Int (TLA_Cast_Int (~ 1 + (TLA_Proj_Int VARIABLE_tpos_)))))))) ((~ 1));
rewrite Z_diff_eq_Z0_eq ((~ 1 × ((TLA_Proj_Int VARIABLE_tpos_) + (~ 1 × (TLA_Proj_Int (TLA_Cast_Int (~ 1 + (TLA_Proj_Int VARIABLE_tpos_)))))))) ((~ 1 × 1));
rewrite Z_diff_geq_Z0_eq ((~ ((TLA_Proj_Int VARIABLE_tpos_) + (~ 1 × (TLA_Proj_Int CONSTANT_N_))))) ((~ ~ 1));
rewrite Z_diff_geq_Z0_eq ((((TLA_Proj_Int CONSTANT_N_) + (~ 1 × (TLA_Proj_Int (TLA_Cast_Int (~ 1 + (TLA_Proj_Int VARIABLE_tpos_)))))) + (~ 1 × ((TLA_Proj_Int VARIABLE_tpos_) + (~ 1 × (TLA_Proj_Int (TLA_Cast_Int (~ 1 + (TLA_Proj_Int VARIABLE_tpos_))))))))) ((1 + (~ 1 × 1)));
rewrite Zgt_le_succ_r_eq (((~ ((TLA_Proj_Int CONSTANT_N_) + (~ 1 × (TLA_Proj_Int (TLA_Cast_Int (~ 1 + (TLA_Proj_Int VARIABLE_tpos_))))))) - (~ 1))) (0);
rewrite Zmult_ge_compat_eq (1) (((~ ((TLA_Proj_Int CONSTANT_N_) + (~ 1 × (TLA_Proj_Int (TLA_Cast_Int (~ 1 + (TLA_Proj_Int VARIABLE_tpos_))))))) - (~ 1))) ((0 + 1));
rewrite Zmult_eq_compat_eq (~ 1) (((~ 1 × ((TLA_Proj_Int VARIABLE_tpos_) + (~ 1 × (TLA_Proj_Int (TLA_Cast_Int (~ 1 + (TLA_Proj_Int VARIABLE_tpos_))))))) - (~ 1 × 1))) (0);
rewrite Zmult_ge_compat_eq (1) (((~ ((TLA_Proj_Int VARIABLE_tpos_) + (~ 1 × (TLA_Proj_Int CONSTANT_N_)))) - (~ ~ 1))) (0);
rewrite Zmult_ge_compat_eq (1) (((((TLA_Proj_Int CONSTANT_N_) + (~ 1 × (TLA_Proj_Int (TLA_Cast_Int (~ 1 + (TLA_Proj_Int VARIABLE_tpos_)))))) + (~ 1 × ((TLA_Proj_Int VARIABLE_tpos_) + (~ 1 × (TLA_Proj_Int (TLA_Cast_Int (~ 1 + (TLA_Proj_Int VARIABLE_tpos_)))))))) - (1 + (~ 1 × 1)))) (0);
try rewrite Z_eq_antisym;
rewrite imp_eq_or;
apply ⇒ᶜᵢ;
assume H0;
rewrite imp_eq_or;
apply ⇒ᶜᵢ;
assume H1;
rewrite imp_eq_or;
apply ⇒ᶜᵢ;
assume H2;
apply ¬ᶜᵢ;
assume H3;
set H0lhs ≔ (1 × ((~ ((TLA_Proj_Int CONSTANT_N_) + (~ 1 × (TLA_Proj_Int (TLA_Cast_Int (~ 1 + (TLA_Proj_Int VARIABLE_tpos_))))))) - (~ 1)));
set H0rhs ≔ (1 × (0 + 1));
set H1lhs ≔ (~ 1 × ((~ 1 × ((TLA_Proj_Int VARIABLE_tpos_) + (~ 1 × (TLA_Proj_Int (TLA_Cast_Int (~ 1 + (TLA_Proj_Int VARIABLE_tpos_))))))) - (~ 1 × 1)));
set H1rhs ≔ (~ 1 × 0);
set H2lhs ≔ (1 × ((~ ((TLA_Proj_Int VARIABLE_tpos_) + (~ 1 × (TLA_Proj_Int CONSTANT_N_)))) - (~ ~ 1)));
set H2rhs ≔ (1 × 0);
set H3lhs ≔ (1 × ((((TLA_Proj_Int CONSTANT_N_) + (~ 1 × (TLA_Proj_Int (TLA_Cast_Int (~ 1 + (TLA_Proj_Int VARIABLE_tpos_)))))) + (~ 1 × ((TLA_Proj_Int VARIABLE_tpos_) + (~ 1 × (TLA_Proj_Int (TLA_Cast_Int (~ 1 + (TLA_Proj_Int VARIABLE_tpos_)))))))) - (1 + (~ 1 × 1))));
set H3rhs ≔ (1 × 0);
compute reify ( H0lhs + H1lhs + H2lhs + H3lhs);
have Hsum : πᶜ (H0lhs + H1lhs + H2lhs + H3lhs ≥ H0rhs + H1rhs + H2rhs + H3rhs) {
    apply (Zsum_geq_s (Zsum_geq_s (Zsum_geq_s H0 H1) H2) H3);
};


admit
//apply completude_lia _ _ Hsum;
end;

symbol t3 : πᶜ ((¬ ((p_20 < 0))) ∨ᶜ p_19) ≔ 
begin
simplify p_20;
simplify p_19;
rewrite .[x in _ ∨ᶜ x] Zle_not_gt;
try rewrite Zinv_lt_eq;
try rewrite Zinv_le_eq;
rewrite Z_diff_gt_Z0_eq ((~ ((TLA_Proj_Int VARIABLE_tpos_) + (~ 1 × (TLA_Proj_Int CONSTANT_N_))))) ((~ 0));
rewrite Z_diff_gt_Z0_eq (((TLA_Proj_Int VARIABLE_tpos_) + (~ 1 × (TLA_Proj_Int CONSTANT_N_)))) (~ 1);
rewrite Zgt_le_succ_r_eq (((~ ((TLA_Proj_Int VARIABLE_tpos_) + (~ 1 × (TLA_Proj_Int CONSTANT_N_)))) - (~ 0))) (0);
rewrite Zgt_le_succ_r_eq ((((TLA_Proj_Int VARIABLE_tpos_) + (~ 1 × (TLA_Proj_Int CONSTANT_N_))) - ~ 1)) (0);
rewrite Zmult_ge_compat_eq (1) (((~ ((TLA_Proj_Int VARIABLE_tpos_) + (~ 1 × (TLA_Proj_Int CONSTANT_N_)))) - (~ 0))) ((0 + 1));
rewrite Zmult_ge_compat_eq (1) ((((TLA_Proj_Int VARIABLE_tpos_) + (~ 1 × (TLA_Proj_Int CONSTANT_N_))) - ~ 1)) ((0 + 1));
try rewrite Z_eq_antisym;
rewrite imp_eq_or;
apply ⇒ᶜᵢ;
assume H0;
apply ¬ᶜᵢ;
assume H1;
set H0lhs ≔ (1 × ((~ ((TLA_Proj_Int VARIABLE_tpos_) + (~ 1 × (TLA_Proj_Int CONSTANT_N_)))) - (~ 0)));
set H0rhs ≔ (1 × (0 + 1));
set H1lhs ≔ (1 × (((TLA_Proj_Int VARIABLE_tpos_) + (~ 1 × (TLA_Proj_Int CONSTANT_N_))) - ~ 1));
set H1rhs ≔ (1 × (0 + 1));
have Hsum : πᶜ (H0lhs + H1lhs ≥ H0rhs + H1rhs) {
    apply (Zsum_geq_s H0 H1);
};
apply completude_lia _ _ Hsum;
end;

symbol t4 : π̇ ▩ ≔ 
begin
admit;
end;
