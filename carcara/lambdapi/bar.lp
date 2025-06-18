require open lambdapi.Alethe;

require open lambdapi.Naryfun;

require open lambdapi.Simplify;

require open lambdapi.Rare;

require open lambdapi.Lia;

symbol f : Arr (int ⭆ ι) int;

symbol p_2 ≔ ((f 5) ≤ 4);

symbol p_3 ≔ (f 5);

symbol p_6 ≔ ((— 1) * (f 5));

symbol p_7 ≔ ((— 1) * 12);

symbol p_11 ≔ (¬ (((f 5) < 5)));

symbol p_12 ≔ ((f 5) < 5);

symbol p_15 ≔ ((— 1) * (f 0));

symbol p_16 ≔ (f 0);

symbol p_17 ≔ ((— 1) * 10);

symbol p_19 ≔ ((f 0) ≤ 4);

opaque symbol t1 : π̇ ((¬ ((p_3 ≤ 4)))  ⟇ (¬ ((p_6 = p_7)))  ⟇ ((p_3 + p_6) ≤ (4 + p_7)) ⟇ ▩) ≔ 
begin
have Hla : π̇ (((¬ (((f 5) ≤ 4))) ∨ (¬ ((((— 1) * (f 5)) = ((— 1) * 12)))) ∨ (((f 5) + ((— 1) * (f 5))) ≤ (4 + ((— 1) * 12))))
        ⟇ ▩) {
    apply ∨ᵢ₁;
    rewrite .[x in _ ∨ _ ∨ x] Zle_not_gt;
    try rewrite Zinv_le_eq;
    rewrite Z_diff_geq_Z0_eq ((— (f 5))) ((— 4));
    rewrite Z_diff_eq_Z0_eq (((— 1) * (f 5))) (((— 1) * 12));
    rewrite Z_diff_gt_Z0_eq (((f 5) + ((— 1) * (f 5)))) ((4 + ((— 1) * 12)));
    rewrite Zgt_le_succ_r_eq ((((f 5) + ((— 1) * (f 5))) - (4 + ((— 1) * 12)))) (0);
    rewrite Zmult_ge_compat_eq (1) (((— (f 5)) - (— 4))) (0);
    rewrite Zmult_eq_compat_eq ((— 1)) ((((— 1) * (f 5)) - ((— 1) * 12))) (0);
    rewrite Zmult_ge_compat_eq (1) ((((f 5) + ((— 1) * (f 5))) - (4 + ((— 1) * 12)))) ((0 + 1));
    try rewrite Z_eq_antisym;
    rewrite imp_eq_or;
    assume H0;
    rewrite imp_eq_or;
    assume H1;
    assume H2;
    set H0l' ≔ (1 * ((— (f 5)) - (— 4)));
    set H0r' ≔ (1 * 0);
    set H1l' ≔ ((— 1) * (((— 1) * (f 5)) - ((— 1) * 12)));
    set H1r' ≔ ((— 1) * 0);
    set H2l' ≔ (1 * (((f 5) + ((— 1) * (f 5))) - (4 + ((— 1) * 12))));
    set H2r' ≔ (1 * (0 + 1));
    set l ≔ H0l' + H1l' + H2l';
    set r ≔ H0r' + H1r' + H2r';
    have sum : π (l ≥ r) {
        refine (Zsum_geq_s H0l' H0r' (H1l' + H2l') (H1r' + H2r') H0 (Zsum_geq_s H1l' H1r' H2l' H2r' H1 H2));
    };
    refine sum _;
    rewrite left  reify_correct (l);
    rewrite left  reify_correct (r);
    set l' ≔ (reify l);
    set r' ≔ (reify r);
    rewrite eta_prod (l');
    rewrite eta_prod (r');
    rewrite left  norm_correct ((l' ₁)) ((l' ₂)) (_) 
    {
        refine ⊤ᵢ;
    }
    {
        refine ⊤ᵢ;
    };
};
simplify;
rewrite or_identity_r;
apply (π̇ₗ Hla);
end;

opaque symbol t2 : π̇ ((¬ ((p_3 < 5)))  ⟇ p_2 ⟇ ▩) ≔ 
begin
have Hla : π̇ (((¬ (((f 5) < 5))) ∨ ((f 5) ≤ 4)) ⟇ ▩) {
    apply ∨ᵢ₁;
    rewrite .[x in _ ∨ x] Zle_not_gt;
    try rewrite Zinv_lt_eq;
    rewrite Z_diff_gt_Z0_eq ((— (f 5))) ((— 5));
    rewrite Z_diff_gt_Z0_eq ((f 5)) (4);
    rewrite Zgt_le_succ_r_eq (((— (f 5)) - (— 5))) (0);
    rewrite Zgt_le_succ_r_eq (((f 5) - 4)) (0);
    rewrite Zmult_ge_compat_eq (1) (((— (f 5)) - (— 5))) ((0 + 1));
    rewrite Zmult_ge_compat_eq (1) (((f 5) - 4)) ((0 + 1));
    try rewrite Z_eq_antisym;
    rewrite imp_eq_or;
    assume H0;
    assume H1;
    set H0l' ≔ (1 * ((— (f 5)) - (— 5)));
    set H0r' ≔ (1 * (0 + 1));
    set H1l' ≔ (1 * ((f 5) - 4));
    set H1r' ≔ (1 * (0 + 1));
    set l ≔ H0l' + H1l';
    set r ≔ H0r' + H1r';
    have sum : π (l ≥ r) {
        refine (Zsum_geq_s H0l' H0r' H1l' H1r' H0 H1);
    };
    refine sum _;
    rewrite left  reify_correct (l);
    rewrite left  reify_correct (r);
    set l' ≔ (reify l);
    set r' ≔ (reify r);
    rewrite eta_prod (l');
    rewrite eta_prod (r');
    rewrite left  norm_correct ((l' ₁)) ((l' ₂)) (_) 
    {
        refine ⊤ᵢ;
    }
    {
        refine ⊤ᵢ;
    };
};
simplify;
rewrite or_identity_r;
apply (π̇ₗ Hla);
end;

opaque symbol t3 : π̇ (p_11  ⟇ p_2 ⟇ ▩) ≔ 
begin
have Hla : π̇ (((¬ (((f 5) < 5))) ∨ ((f 5) ≤ 4)) ⟇ ▩) {
    apply ∨ᵢ₁;
    rewrite .[x in _ ∨ x] Zle_not_gt;
    try rewrite Zinv_lt_eq;
    rewrite Z_diff_gt_Z0_eq ((— (f 5))) ((— 5));
    rewrite Z_diff_gt_Z0_eq ((f 5)) (4);
    rewrite Zgt_le_succ_r_eq (((— (f 5)) - (— 5))) (0);
    rewrite Zgt_le_succ_r_eq (((f 5) - 4)) (0);
    rewrite Zmult_ge_compat_eq (1) (((— (f 5)) - (— 5))) ((0 + 1));
    rewrite Zmult_ge_compat_eq (1) (((f 5) - 4)) ((0 + 1));
    try rewrite Z_eq_antisym;
    rewrite imp_eq_or;
    assume H0;
    assume H1;
    set H0l' ≔ (1 * ((— (f 5)) - (— 5)));
    set H0r' ≔ (1 * (0 + 1));
    set H1l' ≔ (1 * ((f 5) - 4));
    set H1r' ≔ (1 * (0 + 1));
    set l ≔ H0l' + H1l';
    set r ≔ H0r' + H1r';
    have sum : π (l ≥ r) {
        refine (Zsum_geq_s H0l' H0r' H1l' H1r' H0 H1);
    };
    refine sum _;
    rewrite left  reify_correct (l);
    rewrite left  reify_correct (r);
    set l' ≔ (reify l);
    set r' ≔ (reify r);
    rewrite eta_prod (l');
    rewrite eta_prod (r');
    rewrite left  norm_correct ((l' ₁)) ((l' ₂)) (_) 
    {
        refine ⊤ᵢ;
    }
    {
        refine ⊤ᵢ;
    };
};
simplify;
rewrite or_identity_r;
apply (π̇ₗ Hla);
end;

opaque symbol t4 : π̇ ((¬ ((p_15 = p_17)))  ⟇ (¬ ((p_16 ≤ 4)))  ⟇ ((p_15 + p_16) ≤ (p_17 + 4)) ⟇ ▩) ≔ 
begin
have Hla : π̇ (((¬ ((((— 1) * (f 0)) = ((— 1) * 10)))) ∨ (¬ (((f 0) ≤ 4))) ∨ ((((— 1) * (f 0)) + (f 0)) ≤ (((— 1) * 10) + 4)))
        ⟇ ▩) {
    apply ∨ᵢ₁;
    rewrite .[x in _ ∨ _ ∨ x] Zle_not_gt;
    try rewrite Zinv_le_eq;
    rewrite Z_diff_eq_Z0_eq (((— 1) * (f 0))) (((— 1) * 10));
    rewrite Z_diff_geq_Z0_eq ((— (f 0))) ((— 4));
    rewrite Z_diff_gt_Z0_eq ((((— 1) * (f 0)) + (f 0))) ((((— 1) * 10) + 4));
    rewrite Zgt_le_succ_r_eq (((((— 1) * (f 0)) + (f 0)) - (((— 1) * 10) + 4))) (0);
    rewrite Zmult_eq_compat_eq ((— 1)) ((((— 1) * (f 0)) - ((— 1) * 10))) (0);
    rewrite Zmult_ge_compat_eq (1) (((— (f 0)) - (— 4))) (0);
    rewrite Zmult_ge_compat_eq (1) (((((— 1) * (f 0)) + (f 0)) - (((— 1) * 10) + 4))) ((0 + 1));
    try rewrite Z_eq_antisym;
    rewrite imp_eq_or;
    assume H0;
    rewrite imp_eq_or;
    assume H1;
    assume H2;
    set H0l' ≔ ((— 1) * (((— 1) * (f 0)) - ((— 1) * 10)));
    set H0r' ≔ ((— 1) * 0);
    set H1l' ≔ (1 * ((— (f 0)) - (— 4)));
    set H1r' ≔ (1 * 0);
    set H2l' ≔ (1 * ((((— 1) * (f 0)) + (f 0)) - (((— 1) * 10) + 4)));
    set H2r' ≔ (1 * (0 + 1));
    set l ≔ H0l' + H1l' + H2l';
    set r ≔ H0r' + H1r' + H2r';
    have sum : π (l ≥ r) {
        refine (Zsum_geq_s H0l' H0r' (H1l' + H2l') (H1r' + H2r') H0 (Zsum_geq_s H1l' H1r' H2l' H2r' H1 H2));
    };
    refine sum _;
    rewrite left  reify_correct (l);
    rewrite left  reify_correct (r);
    set l' ≔ (reify l);
    set r' ≔ (reify r);
    rewrite eta_prod (l');
    rewrite eta_prod (r');
    rewrite left  norm_correct ((l' ₁)) ((l' ₂)) (_) 
    {
        refine ⊤ᵢ;
    }
    {
        refine ⊤ᵢ;
    };
};
simplify;
rewrite or_identity_r;
apply (π̇ₗ Hla);
end;

opaque symbol t5 : π̇ ((¬ ((p_16 < 5)))  ⟇ p_19 ⟇ ▩) ≔ 
begin
have Hla : π̇ (((¬ (((f 0) < 5))) ∨ ((f 0) ≤ 4)) ⟇ ▩) {
    apply ∨ᵢ₁;
    rewrite .[x in _ ∨ x] Zle_not_gt;
    try rewrite Zinv_lt_eq;
    rewrite Z_diff_gt_Z0_eq ((— (f 0))) ((— 5));
    rewrite Z_diff_gt_Z0_eq ((f 0)) (4);
    rewrite Zgt_le_succ_r_eq (((— (f 0)) - (— 5))) (0);
    rewrite Zgt_le_succ_r_eq (((f 0) - 4)) (0);
    rewrite Zmult_ge_compat_eq (1) (((— (f 0)) - (— 5))) ((0 + 1));
    rewrite Zmult_ge_compat_eq (1) (((f 0) - 4)) ((0 + 1));
    try rewrite Z_eq_antisym;
    rewrite imp_eq_or;
    assume H0;
    assume H1;
    set H0l' ≔ (1 * ((— (f 0)) - (— 5)));
    set H0r' ≔ (1 * (0 + 1));
    set H1l' ≔ (1 * ((f 0) - 4));
    set H1r' ≔ (1 * (0 + 1));
    set l ≔ H0l' + H1l';
    set r ≔ H0r' + H1r';
    have sum : π (l ≥ r) {
        refine (Zsum_geq_s H0l' H0r' H1l' H1r' H0 H1);
    };
    refine sum _;
    rewrite left  reify_correct (l);
    rewrite left  reify_correct (r);
    set l' ≔ (reify l);
    set r' ≔ (reify r);
    rewrite eta_prod (l');
    rewrite eta_prod (r');
    rewrite left  norm_correct ((l' ₁)) ((l' ₂)) (_) 
    {
        refine ⊤ᵢ;
    }
    {
        refine ⊤ᵢ;
    };
};
simplify;
rewrite or_identity_r;
apply (π̇ₗ Hla);
end;

opaque symbol t6 : π̇ ▩ ≔ 
begin
admit;
end;
