require open lambdapi.Alethe;

require open lambdapi.Simplify;

require open lambdapi.Rare;

require open lambdapi.Lia;

require open lambdapi.MergeSort2;

symbol f : τ (int ⤳ int);

symbol p_2 ≔ ((f 0) = 10);

symbol p_3 ≔ (f 0);

symbol p_4 ≔ ((f 5) = 12);

symbol p_5 ≔ (f 5);

symbol p_6 ≔ (`∀ (x : τ (int)), ((0 < (f x)) ∧ ((f x) < 5)));

symbol p_8 ≔ (((¬ (((f 5) = 12))) ∨ (¬ ((¬ (((f 5) ≥ 5)))))) = ((¬ (((f 5) = 12))) ∨ ((f 5) ≥ 5)));

symbol p_9 ≔ ((¬ (((f 5) = 12))) ∨ (¬ ((¬ (((f 5) ≥ 5))))));

symbol p_10 ≔ (¬ (((f 5) = 12)));

symbol p_11 ≔ (¬ ((¬ (((f 5) ≥ 5)))));

symbol p_12 ≔ (¬ (((f 5) ≥ 5)));

symbol p_13 ≔ ((f 5) ≥ 5);

symbol p_14 ≔ ((¬ (((f 5) = 12))) ∨ ((f 5) ≥ 5));

symbol p_18 ≔ (((¬ ((¬ (((f 5) ≥ 5))))) = ((f 5) ≥ 5)) = ⊤);

symbol p_19 ≔ ((¬ ((¬ (((f 5) ≥ 5))))) = ((f 5) ≥ 5));

symbol p_22 ≔ (((f 5) ≥ 5) = (¬ ((¬ (((f 5) ≥ 5))))));

symbol p_23 ≔ (((f 5) ≥ 5) = ((f 5) ≥ 5));

symbol p_27 ≔ (((((f 5) = 12) ∧ (¬ (((f 5) ≥ 5))))) ⇒ (((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))));

symbol p_28 ≔ (((f 5) = 12) ∧ (¬ (((f 5) ≥ 5))));

symbol p_29 ≔ ((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12));

symbol p_30 ≔ ((¬ ((`∀ (BOUND_VARIABLE_6883 : τ (int)), (¬ (((f BOUND_VARIABLE_6883) ≥ 5)))))) ∨ (¬ (((f 5) ≥ 5))));

symbol p_31 ≔ (¬ ((`∀ (BOUND_VARIABLE_6883 : τ (int)), (¬ (((f BOUND_VARIABLE_6883) ≥ 5))))));

symbol p_32 ≔ (`∀ (BOUND_VARIABLE_6883 : τ (int)), (¬ (((f BOUND_VARIABLE_6883) ≥ 5))));

symbol p_33 ≔ (¬ (((`∀ (x : τ (int)), ((0 < (f x)) ∧ ((f x) < 5))) = ((`∀ (BOUND_VARIABLE_6877 : τ (int)), ((f BOUND_VARIABLE_6877) ≥ 1)) ∧ (`∀ (BOUND_VARIABLE_6883 : τ (int)), (¬ (((f BOUND_VARIABLE_6883) ≥ 5))))))));

symbol p_34 ≔ ((`∀ (x : τ (int)), ((0 < (f x)) ∧ ((f x) < 5))) = ((`∀ (BOUND_VARIABLE_6877 : τ (int)), ((f BOUND_VARIABLE_6877) ≥ 1)) ∧ (`∀ (BOUND_VARIABLE_6883 : τ (int)), (¬ (((f BOUND_VARIABLE_6883) ≥ 5))))));

symbol p_35 ≔ ((`∀ (BOUND_VARIABLE_6877 : τ (int)), ((f BOUND_VARIABLE_6877) ≥ 1)) ∧ (`∀ (BOUND_VARIABLE_6883 : τ (int)), (¬ (((f BOUND_VARIABLE_6883) ≥ 5)))));

symbol p_36 ≔ (`∀ (BOUND_VARIABLE_6877 : τ (int)), ((f BOUND_VARIABLE_6877) ≥ 1));

symbol p_37 ≔ (¬ ((`∀ (x : τ (int)), ((0 < (f x)) ∧ ((f x) < 5)))));

symbol p_38 ≔ ((`∀ (x : τ (int)), ((0 < (f x)) ∧ ((f x) < 5))) = (`∀ (x : τ (int)), (((f x) ≥ 1) ∧ (¬ (((f x) ≥ 5))))));

symbol p_39 ≔ (`∀ (x : τ (int)), (((f x) ≥ 1) ∧ (¬ (((f x) ≥ 5)))));

symbol p_40 ≔ (— 0);

symbol p_41 ≔ ((`∀ (x : τ (int)), (((f x) ≥ 1) ∧ (¬ (((f x) ≥ 5))))) = ((`∀ (BOUND_VARIABLE_6877 : τ (int)), ((f BOUND_VARIABLE_6877) ≥ 1)) ∧ (`∀ (BOUND_VARIABLE_6883 : τ (int)), (¬ (((f BOUND_VARIABLE_6883) ≥ 5))))));

symbol p_42 ≔ (¬ ((((f 5) = 12) ∧ (¬ (((f 5) ≥ 5))))));

symbol p_43 ≔ (¬ (((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))));

symbol p_44 ≔ ((((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))) ⇒ (⊥));

symbol p_46 ≔ ((¬ (((f 5) ≤ 4))) = ((f 5) > 4));

symbol p_47 ≔ (¬ (((f 5) ≤ 4)));

symbol p_48 ≔ ((f 5) ≤ 4);

symbol p_49 ≔ ((f 5) > 4);

symbol p_52 ≔ (¬ (((f 5) ≥ (4 + 1))));

symbol p_53 ≔ ((f 5) ≥ (4 + 1));

symbol p_54 ≔ (4 + 1);

symbol p_65 ≔ ((((f 5) ≤ 4)) ⇒ (⊥));

symbol p_67 ≔ ((((f 5) + ((— 1) * (f 5))) ≤ (4 + ((— 1) * 12))) = ⊥);

symbol p_68 ≔ (((f 5) + ((— 1) * (f 5))) ≤ (4 + ((— 1) * 12)));

symbol p_69 ≔ ((f 5) + ((— 1) * (f 5)));

symbol p_70 ≔ ((— 1) * (f 5));

symbol p_71 ≔ (4 + ((— 1) * 12));

symbol p_72 ≔ ((— 1) * 12);

symbol p_75 ≔ (4 = 4);

symbol p_78 ≔ (4 + (— 12));

symbol p_82 ≔ (0 ≤ (— 8));

symbol p_85 ≔ (((— 1) * (f 5)) = ((— 1) * 12));

symbol p_86 ≔ (¬ (((f 5) < 5)));

symbol p_87 ≔ ((f 5) < 5);

symbol p_88 ≔ (¬ (((¬ (((f 5) ≥ 5))) = ((f 5) < 5))));

symbol p_89 ≔ ((¬ (((f 5) ≥ 5))) = ((f 5) < 5));

symbol p_90 ≔ (((f 5) < 5) = (¬ (((f 5) ≥ 5))));

symbol p_92 ≔ (((— 1) < 0) ∧ ((f 5) = 12));

symbol p_93 ≔ ((— 1) < 0);

symbol p_95 ≔ (¬ (((— 1) < 0)));

symbol p_96 ≔ ((((— 1) < 0) = ⊤) = ((— 1) < 0));

symbol p_97 ≔ (((— 1) < 0) = ⊤);

symbol p_98 ≔ (¬ ((((— 1) < 0) = ⊤)));

symbol p_99 ≔ (¬ (⊥));

symbol p_103 ≔ (((f 5) ≤ 4) = (¬ (((f 5) > 4))));

symbol p_104 ≔ (¬ (((f 5) > 4)));

symbol p_112 ≔ (((¬ (((f 0) = 10))) ∨ (¬ ((¬ (((f 0) ≥ 5)))))) = ((¬ (((f 0) = 10))) ∨ ((f 0) ≥ 5)));

symbol p_113 ≔ ((¬ (((f 0) = 10))) ∨ (¬ ((¬ (((f 0) ≥ 5))))));

symbol p_114 ≔ (¬ (((f 0) = 10)));

symbol p_115 ≔ (¬ ((¬ (((f 0) ≥ 5)))));

symbol p_116 ≔ (¬ (((f 0) ≥ 5)));

symbol p_117 ≔ ((f 0) ≥ 5);

symbol p_118 ≔ ((¬ (((f 0) = 10))) ∨ ((f 0) ≥ 5));

symbol p_122 ≔ (((¬ ((¬ (((f 0) ≥ 5))))) = ((f 0) ≥ 5)) = ⊤);

symbol p_123 ≔ ((¬ ((¬ (((f 0) ≥ 5))))) = ((f 0) ≥ 5));

symbol p_126 ≔ (((f 0) ≥ 5) = (¬ ((¬ (((f 0) ≥ 5))))));

symbol p_127 ≔ (((f 0) ≥ 5) = ((f 0) ≥ 5));

symbol p_131 ≔ (((((f 0) = 10) ∧ (¬ (((f 0) ≥ 5))))) ⇒ (⊥));

symbol p_132 ≔ (((f 0) = 10) ∧ (¬ (((f 0) ≥ 5))));

symbol p_133 ≔ ((((f 0) = 10)) ⇒ (⊥));

symbol p_135 ≔ (((((— 1) * (f 0)) + (f 0)) ≤ (((— 1) * 10) + 4)) = ⊥);

symbol p_136 ≔ ((((— 1) * (f 0)) + (f 0)) ≤ (((— 1) * 10) + 4));

symbol p_137 ≔ (((— 1) * (f 0)) + (f 0));

symbol p_138 ≔ ((— 1) * (f 0));

symbol p_139 ≔ (((— 1) * 10) + 4);

symbol p_140 ≔ ((— 1) * 10);

symbol p_145 ≔ ((— 10) + 4);

symbol p_149 ≔ (0 ≤ (— 6));

symbol p_152 ≔ (((— 1) * (f 0)) = ((— 1) * 10));

symbol p_154 ≔ ((f 0) ≤ 4);

symbol p_156 ≔ (((— 1) < 0) ∧ ((f 0) = 10));

symbol p_159 ≔ ((f 0) < 5);

symbol p_161 ≔ ((¬ (((f 0) ≥ 5))) = ((f 0) < 5));

symbol p_163 ≔ ((¬ ((`∀ (BOUND_VARIABLE_6883 : τ (int)), (¬ (((f BOUND_VARIABLE_6883) ≥ 5)))))) ∨ (¬ (((f 0) ≥ 5))));

symbol p_166 ≔ (¬ ((((f 0) = 10) ∧ (¬ (((f 0) ≥ 5))))));

symbol a0 : π̇ ((((f 0) = 10) ∨ ((f 5) = 12)) ⟇ ▩);

symbol a1 : π̇ ((`∀ (x : τ (int)), ((0 < (f x)) ∧ ((f x) < 5))) ⟇ ▩);

opaque symbol t0 : π̇ ((¬ ((p_9 = p_14)))  ⟇ (¬ (p_9))  ⟇ p_14 ⟇ ▩) ≔ 
begin
apply equiv_pos2;
end;

opaque symbol t1 : π̇ ((p_10 = p_10) ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
reflexivity;
end;

opaque symbol t2 : π̇ (((p_19 = ⊤) = p_19) ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
simplify;
eval equiv_simplify ;
end;

opaque symbol t3 : π̇ ((¬ (p_18))  ⟇ p_19 ⟇ ▩) ≔ 
begin
apply equiv1 t2;
end;

opaque symbol t4 : π̇ ((p_19 = (p_13 = p_11)) ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
apply eq-symm (¬ ((¬ (((f 5) ≥ 5))))) ((f 5) ≥ 5);
end;

opaque symbol t5 : π̇ ((p_13 = p_13) ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
reflexivity;
end;

opaque symbol t6 : π̇ (p_19 ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
apply bool-double-not-elim ((f 5) ≥ 5);
end;

opaque symbol t7 : π̇ ((p_22 = p_23) ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
apply (feq2 (=) (π̇ₗ t5) (π̇ₗ t6));
end;

opaque symbol t8 : π̇ ((p_23 = ⊤) ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
apply eq-refl ((f 5) ≥ 5);
end;

opaque symbol t9 : π̇ ((p_22 = ⊤) ⟇ ▩) ≔ 
begin
apply (trans t7 t8);
end;

opaque symbol t10 : π̇ (p_18 ⟇ ▩) ≔ 
begin
apply (trans t4 t9);
end;

opaque symbol t11 : π̇ (p_19 ⟇ ▩) ≔ 
begin
have t3_t10 : π̇ (p_19 ⟇ ▩) {
    apply resolutionᵣ _ _ _ t3 t10;
};
refine t3_t10;
end;

opaque symbol t12 : π̇ (p_8 ⟇ ▩) ≔ 
begin
apply cong_or 
{
    apply t1;
}
{
    apply t11;
};
end;

opaque symbol t13 : π̇ (((p_28) ⇒ ((p_12 ∧ p_4)))  ⟇ p_28 ⟇ ▩) ≔ 
begin
apply implies_neg1;
end;

opaque symbol t14_a0 : π̇ (p_4 ⟇ ▩) ≔ 
begin
admit;
end;

opaque symbol t14_a1 : π̇ (p_12 ⟇ ▩) ≔ 
begin
admit;
end;

opaque symbol t14_t0 : π̇ (p_29  ⟇ p_11  ⟇ p_10 ⟇ ▩) ≔ 
begin
refine and_neg (¬ (f _5 ≥ _5) ⸬ (f _5 = (_2 + (_10 * _1))) ⸬ □) _;
simplify;
rewrite .[in x in x = _] or_identity_r;
rewrite .[in x in _ = x] or_identity_r;
reflexivity
end;

opaque symbol t14_t1 : π̇ (((¬ ((`∀ (BOUND_VARIABLE_6883 : τ (int)), (¬ (((f BOUND_VARIABLE_6883) ≥ 5)))))) ∨ p_12)
    ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
apply imply_to_or;
assume H;
refine (H 5);
end;

opaque symbol t14_t2 : π̇ (p_31  ⟇ p_12 ⟇ ▩) ≔ 
begin
admit;
end;

opaque symbol t14_t3 : π̇ ((¬ ((p_6 = p_35)))  ⟇ (¬ (p_6))  ⟇ p_35 ⟇ ▩) ≔ 
begin
apply equiv_pos2;
end;

opaque symbol t14_t4 : π̇ ((p_6 = (`∀ (x : τ (int)), (((f x) ≥ 1) ∧ (¬ (((f x) ≥ 5)))))) ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
apply bind_∀;
assume x;
have t14_t4_t0 : π̇ (((0 < (f x)) = (¬ ((0 ≥ (f x))))) ⟇ ▩) {
    apply ∨ᵢ₁;
    apply arith-elim-lt 0 (f x);
};
have t14_t4_t1 : π̇ (((0 ≥ (f x)) = ((— 0) ≤ (— (f x)))) ⟇ ▩) {
    apply ∨ᵢ₁;
    apply arith-geq-norm2 0 (f x);
};
have t14_t4_t2 : π̇ (((p_40 ≤ (— (f x))) = (¬ ((p_40 ≥ ((— (f x)) + 1))))) ⟇ ▩) {
    apply ∨ᵢ₁;
    apply arith-leq-norm (— 0) (— (f x));
};
have t14_t4_t3 : π̇ ((((— 1) * (p_40 - ((— (f x)) + 1))) = ((— 1) * ((f x) - 1))) ⟇ ▩) {
    apply ∨ᵢ₁;
    simplify;
    rewrite left  .[x in _ = x] reify_correct;
    rewrite left  .[x in x = _] reify_correct;
    reflexivity;
};
have t14_t4_t4 : π̇ (((p_40 ≥ ((— (f x)) + 1)) = ((f x) ≥ 1)) ⟇ ▩) {
    admit;
};
have t14_t4_t5 : π̇ (((¬ ((p_40 ≥ ((— (f x)) + 1)))) = (¬ (((f x) ≥ 1)))) ⟇ ▩) {
    apply ∨ᵢ₁;
    apply feq (¬) (π̇ₗ t14_t4_t4);
};
have t14_t4_t6 : π̇ (((p_40 ≤ (— (f x))) = (¬ (((f x) ≥ 1)))) ⟇ ▩) {
    apply (trans t14_t4_t2 t14_t4_t5);
};
have t14_t4_t7 : π̇ (((0 ≥ (f x)) = (¬ (((f x) ≥ 1)))) ⟇ ▩) {
    apply (trans t14_t4_t1 t14_t4_t6);
};
have t14_t4_t8 : π̇ (((¬ ((0 ≥ (f x)))) = (¬ ((¬ (((f x) ≥ 1)))))) ⟇ ▩) {
    apply ∨ᵢ₁;
    apply feq (¬) (π̇ₗ t14_t4_t7);
};
have t14_t4_t9 : π̇ (((¬ ((¬ (((f x) ≥ 1))))) = ((f x) ≥ 1)) ⟇ ▩) {
    apply ∨ᵢ₁;
    apply bool-double-not-elim ((f x) ≥ 1);
};
have t14_t4_t10 : π̇ (((¬ ((0 ≥ (f x)))) = ((f x) ≥ 1)) ⟇ ▩) {
    apply (trans t14_t4_t8 t14_t4_t9);
};
have t14_t4_t11 : π̇ (((0 < (f x)) = ((f x) ≥ 1)) ⟇ ▩) {
    apply (trans t14_t4_t0 t14_t4_t10);
};
have t14_t4_t12 : π̇ ((((f x) < 5) = (¬ (((f x) ≥ 5)))) ⟇ ▩) {
    apply ∨ᵢ₁;
    apply arith-elim-lt (f x) 5;
};
have t14_t4_t13 : π̇ ((((0 < (f x)) ∧ ((f x) < 5)) = (((f x) ≥ 1) ∧ (¬ (((f x) ≥ 5))))) ⟇ ▩) {
    apply cong_and 
    {
        apply t14_t4_t11;
    }
    {
        apply t14_t4_t12;
    };
};
apply π̇ₗ t14_t4_t13;
end;

opaque symbol t14_t5 : π̇ ((p_39 = p_35) ⟇ ▩) ≔ 
begin
admit;
end;

opaque symbol t14_t6 : π̇ (p_34 ⟇ ▩) ≔ 
begin
apply (trans t14_t4 t14_t5);
end;

opaque symbol t14_t7 : π̇ (p_35 ⟇ ▩) ≔ 
begin
have t14_t3_t14_t6 : π̇ ((¬ (p_6))  ⟇ p_35 ⟇ ▩) {
    apply resolutionᵣ _ _ _ t14_t3 t14_t6;
};
have t14_t3_t14_t6_a1 : π̇ (p_35 ⟇ ▩) {
    apply resolutionᵣ _ _ _ t14_t3_t14_t6 a1;
};
refine t14_t3_t14_t6_a1;
end;

opaque symbol t14_t8 : π̇ (p_32 ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
apply (∧ₑ₂ (π̇ₗ t14_t7));
end;

opaque symbol t14_t9 : π̇ (p_12 ⟇ ▩) ≔ 
begin
have t14_t2_t14_t8 : π̇ (p_12 ⟇ ▩) {
    apply resolutionᵣ _ _ _ t14_t2 t14_t8;
};
refine t14_t2_t14_t8;
end;

opaque symbol t14_t10 : π̇ (p_29 ⟇ ▩) ≔ 
begin
have t14_t0_t14_t9 : π̇ (p_29  ⟇ p_10 ⟇ ▩) {
    have t14_t0_perm : π ((⟇_to_∨_rw (((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))
             ⟇ (¬ ((¬ (((f 5) ≥ 5)))))
             ⟇ (¬ (((f 5) = 12)))
            ⟇ ▩)) = (⟇_to_∨_rw ((¬ ((¬ (((f 5) ≥ 5)))))
             ⟇ ((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))
             ⟇ (¬ (((f 5) = 12)))
            ⟇ ▩))) {
        apply (cl_perm_correct (((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))
             ⟇ (¬ ((¬ (((f 5) ≥ 5)))))
             ⟇ (¬ (((f 5) = 12)))
            ⟇ ▩) ((¬ ((¬ (((f 5) ≥ 5)))))  ⟇ ((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))  ⟇ (¬ (((f 5) = 12))) ⟇ ▩));
        apply ⊤ᵢ;
    };
    apply resolutionᵣ _ _ _ (subst_equiv_clause (((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))
         ⟇ (¬ ((¬ (((f 5) ≥ 5)))))
         ⟇ (¬ (((f 5) = 12)))
        ⟇ ▩) ((¬ ((¬ (((f 5) ≥ 5)))))
         ⟇ ((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))
         ⟇ (¬ (((f 5) = 12)))
        ⟇ ▩) t14_t0_perm t14_t0) t14_t9;
};
have t14_t0_t14_t9_t14_a0 : π̇ (p_29 ⟇ ▩) {
    have t14_t0_t14_t9_perm : π ((⟇_to_∨_rw (((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))
             ⟇ (¬ (((f 5) = 12)))
            ⟇ ▩)) = (⟇_to_∨_rw ((¬ (((f 5) = 12)))  ⟇ ((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12)) ⟇ ▩))) {
        apply (cl_perm_correct (((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))  ⟇ (¬ (((f 5) = 12))) ⟇ ▩) ((¬ (((f 5) = 12)))
             ⟇ ((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))
            ⟇ ▩));
        apply ⊤ᵢ;
    };
    apply resolutionᵣ _ _ _ (subst_equiv_clause (((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))
         ⟇ (¬ (((f 5) = 12)))
        ⟇ ▩) ((¬ (((f 5) = 12)))  ⟇ ((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12)) ⟇ ▩) t14_t0_t14_t9_perm t14_t0_t14_t9) t14_a0;
};
refine t14_t0_t14_t9_t14_a0;
end;

opaque symbol t14 : π̇ (p_10  ⟇ p_11  ⟇ p_29 ⟇ ▩) ≔ 
begin
apply ∨ᵢ₂;
apply ∨ᵢ₂;
apply ∨ᵢ₁;
apply (π̇ₗ t14_t10);
end;

// opaque symbol t15 : π (¬ ((f _5 = (_2 + (_10 * _1))) ∧ ¬ (f _5 ≥ _5)) ∨ ((f _5 = (_2 + (_10 * _1))))) ≔ 
// begin
// refine and_pos2 Stdlib.Nat._0 ((f _5 = (_2 + (_10 * _1))) ⸬ ( ¬ (f _5 ≥ _5)) ⸬ □) ⊤ᵢ;
// end;

opaque symbol t15 : π̇ ((¬ (p_28))  ⟇ p_4 ⟇ ▩) ≔ 
begin
    refine and_pos Stdlib.Nat._0 ((f _5 = (_2 + (_10 * _1))) ⸬ ( ¬ (f _5 ≥ _5)) ⸬ □) ⊤ᵢ;
end;

opaque symbol t16 : π̇ (p_42 ⟇ p_12 ⟇ ▩) ≔ 
begin
// apply and_pos;
// reflexivity;
admit
end;

opaque symbol t17 : π̇ (p_29  ⟇ p_42  ⟇ p_42 ⟇ ▩) ≔ 
begin
have t14_t15 : π̇ (p_11  ⟇ p_29  ⟇ p_42 ⟇ ▩) {
    have t15_perm : π ((⟇_to_∨_rw ((¬ ((((f 5) = 12) ∧ (¬ (((f 5) ≥ 5))))))
             ⟇ ((f 5) = 12)
            ⟇ ▩)) = (⟇_to_∨_rw (((f 5) = 12)  ⟇ (¬ ((((f 5) = 12) ∧ (¬ (((f 5) ≥ 5)))))) ⟇ ▩))) {
        apply (cl_perm_correct ((¬ ((((f 5) = 12) ∧ (¬ (((f 5) ≥ 5))))))  ⟇ ((f 5) = 12) ⟇ ▩) (((f 5) = 12)
             ⟇ (¬ ((((f 5) = 12) ∧ (¬ (((f 5) ≥ 5))))))
            ⟇ ▩));
        apply ⊤ᵢ;
    };
    apply resolutionᵣ _ _ _ t14 (subst_equiv_clause ((¬ ((((f 5) = 12) ∧ (¬ (((f 5) ≥ 5))))))
         ⟇ ((f 5) = 12)
        ⟇ ▩) (((f 5) = 12)  ⟇ (¬ ((((f 5) = 12) ∧ (¬ (((f 5) ≥ 5)))))) ⟇ ▩) t15_perm t15);
};
have t14_t15_t16 : π̇ (p_29  ⟇ p_42  ⟇ p_42 ⟇ ▩) {
    have t16_perm : π ((⟇_to_∨_rw ((¬ ((((f 5) = 12) ∧ (¬ (((f 5) ≥ 5))))))
             ⟇ (¬ (((f 5) ≥ 5)))
            ⟇ ▩)) = (⟇_to_∨_rw ((¬ (((f 5) ≥ 5)))  ⟇ (¬ ((((f 5) = 12) ∧ (¬ (((f 5) ≥ 5)))))) ⟇ ▩))) {
        apply (cl_perm_correct ((¬ ((((f 5) = 12) ∧ (¬ (((f 5) ≥ 5))))))  ⟇ (¬ (((f 5) ≥ 5))) ⟇ ▩) ((¬ (((f 5) ≥ 5)))
             ⟇ (¬ ((((f 5) = 12) ∧ (¬ (((f 5) ≥ 5))))))
            ⟇ ▩));
        apply ⊤ᵢ;
    };
    apply resolutionᵣ _ _ _ t14_t15 (subst_equiv_clause ((¬ ((((f 5) = 12) ∧ (¬ (((f 5) ≥ 5))))))
         ⟇ (¬ (((f 5) ≥ 5)))
        ⟇ ▩) ((¬ (((f 5) ≥ 5)))  ⟇ (¬ ((((f 5) = 12) ∧ (¬ (((f 5) ≥ 5)))))) ⟇ ▩) t16_perm t16);
};
refine t14_t15_t16;
end;

opaque symbol t18 : π̇ (p_42  ⟇ p_42  ⟇ p_29 ⟇ ▩) ≔ 
begin
admit;
end;

opaque symbol t19 : π̇ (p_42  ⟇ p_29 ⟇ ▩) ≔ 
begin
admit;
end;

opaque symbol t20 : π̇ (p_27  ⟇ p_29 ⟇ ▩) ≔ 
begin
have t13_t19 : π̇ (p_27  ⟇ p_29 ⟇ ▩) {
    have t13_perm : π ((⟇_to_∨_rw ((((((f 5) = 12) ∧ (¬ (((f 5) ≥ 5))))) ⇒ (((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))))
             ⟇ (((f 5) = 12) ∧ (¬ (((f 5) ≥ 5))))
            ⟇ ▩)) = (⟇_to_∨_rw ((((f 5) = 12) ∧ (¬ (((f 5) ≥ 5))))
             ⟇ (((((f 5) = 12) ∧ (¬ (((f 5) ≥ 5))))) ⇒ (((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))))
            ⟇ ▩))) {
        apply (cl_perm_correct ((((((f 5) = 12) ∧ (¬ (((f 5) ≥ 5))))) ⇒ (((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))))
             ⟇ (((f 5) = 12) ∧ (¬ (((f 5) ≥ 5))))
            ⟇ ▩) ((((f 5) = 12) ∧ (¬ (((f 5) ≥ 5))))
             ⟇ (((((f 5) = 12) ∧ (¬ (((f 5) ≥ 5))))) ⇒ (((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))))
            ⟇ ▩));
        apply ⊤ᵢ;
    };
    apply resolutionₗ _ _ _ (subst_equiv_clause ((((((f 5) = 12) ∧ (¬ (((f 5) ≥ 5))))) ⇒ (((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))))
         ⟇ (((f 5) = 12) ∧ (¬ (((f 5) ≥ 5))))
        ⟇ ▩) ((((f 5) = 12) ∧ (¬ (((f 5) ≥ 5))))
         ⟇ (((((f 5) = 12) ∧ (¬ (((f 5) ≥ 5))))) ⇒ (((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))))
        ⟇ ▩) t13_perm t13) t19;
};
refine t13_t19;
end;

opaque symbol t21 : π̇ (p_27  ⟇ (¬ (p_29)) ⟇ ▩) ≔ 
begin
apply implies_neg2;
end;

opaque symbol t22 : π̇ (p_27  ⟇ p_27 ⟇ ▩) ≔ 
begin
have t20_t21 : π̇ (p_27  ⟇ p_27 ⟇ ▩) {
    have t20_perm : π ((⟇_to_∨_rw ((((((f 5) = 12) ∧ (¬ (((f 5) ≥ 5))))) ⇒ (((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))))
             ⟇ ((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))
            ⟇ ▩)) = (⟇_to_∨_rw (((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))
             ⟇ (((((f 5) = 12) ∧ (¬ (((f 5) ≥ 5))))) ⇒ (((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))))
            ⟇ ▩))) {
        apply (cl_perm_correct ((((((f 5) = 12) ∧ (¬ (((f 5) ≥ 5))))) ⇒ (((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))))
             ⟇ ((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))
            ⟇ ▩) (((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))
             ⟇ (((((f 5) = 12) ∧ (¬ (((f 5) ≥ 5))))) ⇒ (((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))))
            ⟇ ▩));
        apply ⊤ᵢ;
    };
    have t21_perm : π ((⟇_to_∨_rw ((((((f 5) = 12) ∧ (¬ (((f 5) ≥ 5))))) ⇒ (((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))))
             ⟇ (¬ (((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))))
            ⟇ ▩)) = (⟇_to_∨_rw ((¬ (((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))))
             ⟇ (((((f 5) = 12) ∧ (¬ (((f 5) ≥ 5))))) ⇒ (((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))))
            ⟇ ▩))) {
        apply (cl_perm_correct ((((((f 5) = 12) ∧ (¬ (((f 5) ≥ 5))))) ⇒ (((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))))
             ⟇ (¬ (((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))))
            ⟇ ▩) ((¬ (((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))))
             ⟇ (((((f 5) = 12) ∧ (¬ (((f 5) ≥ 5))))) ⇒ (((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))))
            ⟇ ▩));
        apply ⊤ᵢ;
    };
    apply resolutionₗ _ _ _ (subst_equiv_clause ((((((f 5) = 12) ∧ (¬ (((f 5) ≥ 5))))) ⇒ (((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))))
         ⟇ ((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))
        ⟇ ▩) (((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))
         ⟇ (((((f 5) = 12) ∧ (¬ (((f 5) ≥ 5))))) ⇒ (((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))))
        ⟇ ▩) t20_perm t20) (subst_equiv_clause ((((((f 5) = 12) ∧ (¬ (((f 5) ≥ 5))))) ⇒ (((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))))
         ⟇ (¬ (((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))))
        ⟇ ▩) ((¬ (((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))))
         ⟇ (((((f 5) = 12) ∧ (¬ (((f 5) ≥ 5))))) ⇒ (((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))))
        ⟇ ▩) t21_perm t21);
};
refine t20_t21;
end;

opaque symbol t23 : π̇ (p_27 ⟇ ▩) ≔ 
begin
admit;
end;

opaque symbol t24 : π̇ (p_42  ⟇ p_29 ⟇ ▩) ≔ 
begin
apply implies (π̇ₗ t23);
end;

opaque symbol t25 : π̇ (((p_29) ⇒ (⊥))  ⟇ p_29 ⟇ ▩) ≔ 
begin
apply implies_neg1;
end;

opaque symbol t26_a0 : π̇ (p_12 ⟇ ▩) ≔ 
begin
admit;
end;

opaque symbol t26_a1 : π̇ (p_4 ⟇ ▩) ≔ 
begin
admit;
end;

opaque symbol t26_t0 : π̇ ((¬ ((p_47 = p_49)))  ⟇ (¬ (p_47))  ⟇ p_49 ⟇ ▩) ≔ 
begin
apply equiv_pos2;
end;

opaque symbol t26_t1 : π̇ ((p_48 = (¬ ((p_5 ≥ (4 + 1))))) ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
apply arith-leq-norm (f 5) 4;
end;

opaque symbol t26_t2 : π̇ ((p_5 = p_5) ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
reflexivity;
end;

opaque symbol t26_t3 : π̇ ((p_54 = 5) ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
simplify;
reflexivity;
end;

opaque symbol t26_t4 : π̇ ((p_53 = p_13) ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
apply (feq2 (≥) (π̇ₗ t26_t2) (π̇ₗ t26_t3));
end;

opaque symbol t26_t5 : π̇ ((p_52 = p_12) ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
apply feq (¬) (π̇ₗ t26_t4);
end;

opaque symbol t26_t6 : π̇ ((p_48 = p_12) ⟇ ▩) ≔ 
begin
apply (trans t26_t1 t26_t5);
end;

opaque symbol t26_t7 : π̇ ((p_47 = p_11) ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
apply feq (¬) (π̇ₗ t26_t6);
end;

opaque symbol t26_t8 : π̇ ((p_47 = p_13) ⟇ ▩) ≔ 
begin
apply (trans t26_t7 t11);
end;

opaque symbol t26_t9 : π̇ ((p_49 = p_47) ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
apply arith-elim-gt (f 5) 4;
end;

opaque symbol t26_t10 : π̇ ((p_49 = p_13) ⟇ ▩) ≔ 
begin
apply (trans t26_t9 t26_t8);
end;

opaque symbol t26_t11 : π̇ ((p_13 = p_49) ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
symmetry;
apply (π̇ₗ t26_t10);
end;

opaque symbol t26_t12 : π̇ (p_46 ⟇ ▩) ≔ 
begin
apply (trans t26_t8 t26_t11);
end;

opaque symbol t26_t13 : π̇ (((p_48) ⇒ (⊥))  ⟇ p_48 ⟇ ▩) ≔ 
begin
apply implies_neg1;
end;

opaque symbol t26_t14_a0 : π̇ (p_48 ⟇ ▩) ≔ 
begin
admit;
end;

opaque symbol t26_t14_t0 : π̇ ((¬ ((p_68 = ⊥)))  ⟇ (¬ (p_68))  ⟇ ⊥ ⟇ ▩) ≔ 
begin
apply equiv_pos2;
end;

opaque symbol t26_t14_t1 : π̇ ((p_69 = 0) ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
simplify;
rewrite left  .[x in _ = x] reify_correct;
rewrite left  .[x in x = _] reify_correct;
simplify;
admit
// compute (nth ((f 5) ⸬ □) Stdlib.Nat._0);
//admit
end;

opaque symbol t26_t14_t2 : π̇ ((4 = 4) ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
reflexivity;
end;

opaque symbol t26_t14_t3 : π̇ ((p_72 = (— 12)) ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
simplify;
reflexivity;
end;

opaque symbol t26_t14_t4 : π̇ ((p_71 = (4 + (— 12))) ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
apply (feq2 (+) (π̇ₗ t26_t14_t2) (π̇ₗ t26_t14_t3));
end;

opaque symbol t26_t14_t5 : π̇ ((p_78 = (— 8)) ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
simplify;
reflexivity;
end;

opaque symbol t26_t14_t6 : π̇ ((p_71 = (— 8)) ⟇ ▩) ≔ 
begin
apply (trans t26_t14_t4 t26_t14_t5);
end;

opaque symbol t26_t14_t7 : π̇ ((p_68 = (0 ≤ (— 8))) ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
apply (feq2 (≤) (π̇ₗ t26_t14_t1) (π̇ₗ t26_t14_t6));
end;

opaque symbol t26_t14_t8 : π̇ ((p_82 = ⊥) ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
admit;
end;

opaque symbol t26_t14_t9 : π̇ (p_67 ⟇ ▩) ≔ 
begin
apply (trans t26_t14_t7 t26_t14_t8);
end;

opaque symbol t26_t14_t10 : π̇ (p_47  ⟇ (¬ ((p_70 = p_72)))  ⟇ p_68 ⟇ ▩) ≔ 
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

opaque symbol t26_t14_t11 : π̇ ((¬ ((p_5 < 5)))  ⟇ p_48 ⟇ ▩) ≔ 
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

opaque symbol t26_t14_t12 : π̇ ((¬ ((p_12 = p_87)))  ⟇ p_11  ⟇ p_87 ⟇ ▩) ≔ 
begin
apply equiv_pos2;
end;

opaque symbol t26_t14_t13 : π̇ ((p_87 = p_12) ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
apply arith-elim-lt (f 5) 5;
end;

opaque symbol t26_t14_t14 : π̇ (p_89 ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
symmetry;
apply (π̇ₗ t26_t14_t13);
end;

opaque symbol t26_t14_t15 : π̇ (p_30 ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
apply imply_to_or;
assume H;
refine (H 5);
end;

opaque symbol t26_t14_t16 : π̇ (p_31  ⟇ p_12 ⟇ ▩) ≔ 
begin
admit;
end;

opaque symbol t26_t14_t17 : π̇ (p_33  ⟇ p_37  ⟇ p_35 ⟇ ▩) ≔ 
begin
apply equiv_pos2;
end;

opaque symbol t26_t14_t18 : π̇ (p_38 ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
apply bind_∀;
assume x;
have t26_t14_t18_t0 : π̇ (((0 < (f x)) = (¬ ((0 ≥ (f x))))) ⟇ ▩) {
    apply ∨ᵢ₁;
    apply arith-elim-lt 0 (f x);
};
have t26_t14_t18_t1 : π̇ (((0 ≥ (f x)) = (p_40 ≤ (— (f x)))) ⟇ ▩) {
    apply ∨ᵢ₁;
    apply arith-geq-norm2 0 (f x);
};
have t26_t14_t18_t2 : π̇ (((p_40 ≤ (— (f x))) = (¬ ((p_40 ≥ ((— (f x)) + 1))))) ⟇ ▩) {
    apply ∨ᵢ₁;
    apply arith-leq-norm (— 0) (— (f x));
};
have t26_t14_t18_t3 : π̇ ((((— 1) * (p_40 - ((— (f x)) + 1))) = ((— 1) * ((f x) - 1))) ⟇ ▩) {
    apply ∨ᵢ₁;
    simplify;
    rewrite left  .[x in _ = x] reify_correct;
    rewrite left  .[x in x = _] reify_correct;
    reflexivity;
};
have t26_t14_t18_t4 : π̇ (((p_40 ≥ ((— (f x)) + 1)) = ((f x) ≥ 1)) ⟇ ▩) {
    admit;
};
have t26_t14_t18_t5 : π̇ (((¬ ((p_40 ≥ ((— (f x)) + 1)))) = (¬ (((f x) ≥ 1)))) ⟇ ▩) {
    apply ∨ᵢ₁;
    apply feq (¬) (π̇ₗ t26_t14_t18_t4);
};
have t26_t14_t18_t6 : π̇ (((p_40 ≤ (— (f x))) = (¬ (((f x) ≥ 1)))) ⟇ ▩) {
    apply (trans t26_t14_t18_t2 t26_t14_t18_t5);
};
have t26_t14_t18_t7 : π̇ (((0 ≥ (f x)) = (¬ (((f x) ≥ 1)))) ⟇ ▩) {
    apply (trans t26_t14_t18_t1 t26_t14_t18_t6);
};
have t26_t14_t18_t8 : π̇ (((¬ ((0 ≥ (f x)))) = (¬ ((¬ (((f x) ≥ 1)))))) ⟇ ▩) {
    apply ∨ᵢ₁;
    apply feq (¬) (π̇ₗ t26_t14_t18_t7);
};
have t26_t14_t18_t9 : π̇ (((¬ ((¬ (((f x) ≥ 1))))) = ((f x) ≥ 1)) ⟇ ▩) {
    apply ∨ᵢ₁;
    apply bool-double-not-elim ((f x) ≥ 1);
};
have t26_t14_t18_t10 : π̇ (((¬ ((0 ≥ (f x)))) = ((f x) ≥ 1)) ⟇ ▩) {
    apply (trans t26_t14_t18_t8 t26_t14_t18_t9);
};
have t26_t14_t18_t11 : π̇ (((0 < (f x)) = ((f x) ≥ 1)) ⟇ ▩) {
    apply (trans t26_t14_t18_t0 t26_t14_t18_t10);
};
have t26_t14_t18_t12 : π̇ ((((f x) < 5) = (¬ (((f x) ≥ 5)))) ⟇ ▩) {
    apply ∨ᵢ₁;
    apply arith-elim-lt (f x) 5;
};
have t26_t14_t18_t13 : π̇ ((((0 < (f x)) ∧ ((f x) < 5)) = (((f x) ≥ 1) ∧ (¬ (((f x) ≥ 5))))) ⟇ ▩) {
    apply cong_and 
    {
        apply t26_t14_t18_t11;
    }
    {
        apply t26_t14_t18_t12;
    };
};
apply π̇ₗ t26_t14_t18_t13;
end;

opaque symbol t26_t14_t19 : π̇ (p_41 ⟇ ▩) ≔ 
begin
admit;
end;

opaque symbol t26_t14_t20 : π̇ (p_34 ⟇ ▩) ≔ 
begin
apply (trans t26_t14_t18 t26_t14_t19);
end;

opaque symbol t26_t14_t21 : π̇ (p_35 ⟇ ▩) ≔ 
begin
have t26_t14_t17_t26_t14_t20 : π̇ (p_37  ⟇ p_35 ⟇ ▩) {
    apply resolutionᵣ _ _ _ t26_t14_t17 t26_t14_t20;
};
have t26_t14_t17_t26_t14_t20_a1 : π̇ (p_35 ⟇ ▩) {
    apply resolutionᵣ _ _ _ t26_t14_t17_t26_t14_t20 a1;
};
refine t26_t14_t17_t26_t14_t20_a1;
end;

opaque symbol t26_t14_t22 : π̇ (p_32 ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
apply (∧ₑ₂ (π̇ₗ t26_t14_t21));
end;

opaque symbol t26_t14_t23 : π̇ (p_12 ⟇ ▩) ≔ 
begin
have t26_t14_t16_t26_t14_t22 : π̇ (p_12 ⟇ ▩) {
    apply resolutionᵣ _ _ _ t26_t14_t16 t26_t14_t22;
};
refine t26_t14_t16_t26_t14_t22;
end;

opaque symbol t26_t14_t24 : π̇ (p_87 ⟇ ▩) ≔ 
begin
have t26_t14_t12_t26_t14_t14 : π̇ (p_11  ⟇ p_87 ⟇ ▩) {
    apply resolutionᵣ _ _ _ t26_t14_t12 t26_t14_t14;
};
have t26_t14_t12_t26_t14_t14_t26_t14_t23 : π̇ (p_87 ⟇ ▩) {
    apply resolutionᵣ _ _ _ t26_t14_t12_t26_t14_t14 t26_t14_t23;
};
refine t26_t14_t12_t26_t14_t14_t26_t14_t23;
end;

opaque symbol t26_t14_t25 : π̇ (p_48 ⟇ ▩) ≔ 
begin
have t26_t14_t11_t26_t14_t24 : π̇ (p_48 ⟇ ▩) {
    apply resolutionᵣ _ _ _ t26_t14_t11 t26_t14_t24;
};
refine t26_t14_t11_t26_t14_t24;
end;

opaque symbol t26_t14_t26 : π̇ ((((((— 1) < 0) ∧ p_4)) ⇒ (p_85)) ⟇ ▩) ≔ 
begin
admit;
end;

opaque symbol t26_t14_t27 : π̇ ((¬ (p_92))  ⟇ p_85 ⟇ ▩) ≔ 
begin
apply implies (π̇ₗ t26_t14_t26);
end;

opaque symbol t26_t14_t28 : π̇ (p_92  ⟇ (¬ (p_93))  ⟇ p_10 ⟇ ▩) ≔ 
begin
refine and_neg (⊤ ⸬ (f 5 = 12) ⸬ □) (eq_refl _);
end;

opaque symbol t26_t14_t29 : π̇ (((p_93 = ⊤) = p_93) ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
simplify;
eval equiv_simplify ;
end;

opaque symbol t26_t14_t30 : π̇ ((¬ (p_97))  ⟇ p_93 ⟇ ▩) ≔ 
begin
apply equiv1 t26_t14_t29;
end;

opaque symbol t26_t14_t31 : π̇ (p_97 ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
admit;
end;

opaque symbol t26_t14_t32 : π̇ (p_93 ⟇ ▩) ≔ 
begin
have t26_t14_t30_t26_t14_t31 : π̇ (p_93 ⟇ ▩) {
    apply resolutionᵣ _ _ _ t26_t14_t30 t26_t14_t31;
};
refine t26_t14_t30_t26_t14_t31;
end;

opaque symbol t26_t14_t33 : π̇ (p_92 ⟇ ▩) ≔ 
begin
have t26_t14_t28_t26_t14_t32 : π̇ (p_92  ⟇ p_10 ⟇ ▩) {
    have t26_t14_t28_perm : π ((⟇_to_∨_rw ((((— 1) < 0) ∧ ((f 5) = 12))
             ⟇ (¬ (((— 1) < 0)))
             ⟇ (¬ (((f 5) = 12)))
            ⟇ ▩)) = (⟇_to_∨_rw ((¬ (((— 1) < 0)))  ⟇ (((— 1) < 0) ∧ ((f 5) = 12))  ⟇ (¬ (((f 5) = 12))) ⟇ ▩))) {
        apply (cl_perm_correct ((((— 1) < 0) ∧ ((f 5) = 12))
             ⟇ (¬ (((— 1) < 0)))
             ⟇ (¬ (((f 5) = 12)))
            ⟇ ▩) ((¬ (((— 1) < 0)))  ⟇ (((— 1) < 0) ∧ ((f 5) = 12))  ⟇ (¬ (((f 5) = 12))) ⟇ ▩));
        apply ⊤ᵢ;
    };
    apply resolutionᵣ _ _ _ (subst_equiv_clause ((((— 1) < 0) ∧ ((f 5) = 12))
         ⟇ (¬ (((— 1) < 0)))
         ⟇ (¬ (((f 5) = 12)))
        ⟇ ▩) ((¬ (((— 1) < 0)))
         ⟇ (((— 1) < 0) ∧ ((f 5) = 12))
         ⟇ (¬ (((f 5) = 12)))
        ⟇ ▩) t26_t14_t28_perm t26_t14_t28) t26_t14_t32;
};
have t26_t14_t28_t26_t14_t32_t26_a1 : π̇ (p_92 ⟇ ▩) {
    have t26_t14_t28_t26_t14_t32_perm : π ((⟇_to_∨_rw ((((— 1) < 0) ∧ ((f 5) = 12))
             ⟇ (¬ (((f 5) = 12)))
            ⟇ ▩)) = (⟇_to_∨_rw ((¬ (((f 5) = 12)))  ⟇ (((— 1) < 0) ∧ ((f 5) = 12)) ⟇ ▩))) {
        apply (cl_perm_correct ((((— 1) < 0) ∧ ((f 5) = 12))  ⟇ (¬ (((f 5) = 12))) ⟇ ▩) ((¬ (((f 5) = 12)))
             ⟇ (((— 1) < 0) ∧ ((f 5) = 12))
            ⟇ ▩));
        apply ⊤ᵢ;
    };
    apply resolutionᵣ _ _ _ (subst_equiv_clause ((((— 1) < 0) ∧ ((f 5) = 12))
         ⟇ (¬ (((f 5) = 12)))
        ⟇ ▩) ((¬ (((f 5) = 12)))
         ⟇ (((— 1) < 0) ∧ ((f 5) = 12))
        ⟇ ▩) t26_t14_t28_t26_t14_t32_perm t26_t14_t28_t26_t14_t32) t26_a1;
};
refine t26_t14_t28_t26_t14_t32_t26_a1;
end;

opaque symbol t26_t14_t34 : π̇ (p_85 ⟇ ▩) ≔ 
begin
have t26_t14_t27_t26_t14_t33 : π̇ (p_85 ⟇ ▩) {
    apply resolutionᵣ _ _ _ t26_t14_t27 t26_t14_t33;
};
refine t26_t14_t27_t26_t14_t33;
end;

opaque symbol t26_t14_t35 : π̇ (p_68 ⟇ ▩) ≔ 
begin
have t26_t14_t10_t26_t14_t25 : π̇ ((¬ (p_85))  ⟇ p_68 ⟇ ▩) {
    apply resolutionᵣ _ _ _ t26_t14_t10 t26_t14_t25;
};
have t26_t14_t10_t26_t14_t25_t26_t14_t34 : π̇ (p_68 ⟇ ▩) {
    apply resolutionᵣ _ _ _ t26_t14_t10_t26_t14_t25 t26_t14_t34;
};
refine t26_t14_t10_t26_t14_t25_t26_t14_t34;
end;

opaque symbol t26_t14_t36 : π̇ (⊥ ⟇ ▩) ≔ 
begin
have t26_t14_t0_t26_t14_t9 : π̇ ((¬ (p_68))  ⟇ ⊥ ⟇ ▩) {
    apply resolutionᵣ _ _ _ t26_t14_t0 t26_t14_t9;
};
have t26_t14_t0_t26_t14_t9_t26_t14_t35 : π̇ (⊥ ⟇ ▩) {
    apply resolutionᵣ _ _ _ t26_t14_t0_t26_t14_t9 t26_t14_t35;
};
refine t26_t14_t0_t26_t14_t9_t26_t14_t35;
end;

opaque symbol t26_t14 : π̇ (p_47  ⟇ ⊥ ⟇ ▩) ≔ 
begin
apply ∨ᵢ₂;
apply t26_t14_t36;
end;

opaque symbol t26_t15 : π̇ (p_65  ⟇ ⊥ ⟇ ▩) ≔ 
begin
have t26_t13_t26_t14 : π̇ (p_65  ⟇ ⊥ ⟇ ▩) {
    have t26_t13_perm : π ((⟇_to_∨_rw (((((f 5) ≤ 4)) ⇒ (⊥))  ⟇ ((f 5) ≤ 4) ⟇ ▩)) = (⟇_to_∨_rw (((f 5) ≤ 4)
             ⟇ ((((f 5) ≤ 4)) ⇒ (⊥))
            ⟇ ▩))) {
        apply (cl_perm_correct (((((f 5) ≤ 4)) ⇒ (⊥))  ⟇ ((f 5) ≤ 4) ⟇ ▩) (((f 5) ≤ 4)  ⟇ ((((f 5) ≤ 4)) ⇒ (⊥)) ⟇ ▩));
        apply ⊤ᵢ;
    };
    apply resolutionₗ _ _ _ (subst_equiv_clause (((((f 5) ≤ 4)) ⇒ (⊥))  ⟇ ((f 5) ≤ 4) ⟇ ▩) (((f 5) ≤ 4)
         ⟇ ((((f 5) ≤ 4)) ⇒ (⊥))
        ⟇ ▩) t26_t13_perm t26_t13) t26_t14;
};
refine t26_t13_t26_t14;
end;

opaque symbol t26_t16 : π̇ (p_65  ⟇ (¬ (⊥)) ⟇ ▩) ≔ 
begin
apply implies_neg2;
end;

opaque symbol t26_t17 : π̇ (p_65  ⟇ p_65 ⟇ ▩) ≔ 
begin
have t26_t15_t26_t16 : π̇ (p_65  ⟇ p_65 ⟇ ▩) {
    have t26_t15_perm : π ((⟇_to_∨_rw (((((f 5) ≤ 4)) ⇒ (⊥))  ⟇ ⊥ ⟇ ▩)) = (⟇_to_∨_rw (⊥
             ⟇ ((((f 5) ≤ 4)) ⇒ (⊥))
            ⟇ ▩))) {
        apply (cl_perm_correct (((((f 5) ≤ 4)) ⇒ (⊥))  ⟇ ⊥ ⟇ ▩) (⊥  ⟇ ((((f 5) ≤ 4)) ⇒ (⊥)) ⟇ ▩));
        apply ⊤ᵢ;
    };
    have t26_t16_perm : π ((⟇_to_∨_rw (((((f 5) ≤ 4)) ⇒ (⊥))  ⟇ (¬ (⊥)) ⟇ ▩)) = (⟇_to_∨_rw ((¬ (⊥))
             ⟇ ((((f 5) ≤ 4)) ⇒ (⊥))
            ⟇ ▩))) {
        apply (cl_perm_correct (((((f 5) ≤ 4)) ⇒ (⊥))  ⟇ (¬ (⊥)) ⟇ ▩) ((¬ (⊥))  ⟇ ((((f 5) ≤ 4)) ⇒ (⊥)) ⟇ ▩));
        apply ⊤ᵢ;
    };
    apply resolutionₗ _ _ _ (subst_equiv_clause (((((f 5) ≤ 4)) ⇒ (⊥))  ⟇ ⊥ ⟇ ▩) (⊥
         ⟇ ((((f 5) ≤ 4)) ⇒ (⊥))
        ⟇ ▩) t26_t15_perm t26_t15) (subst_equiv_clause (((((f 5) ≤ 4)) ⇒ (⊥))  ⟇ (¬ (⊥)) ⟇ ▩) ((¬ (⊥))
         ⟇ ((((f 5) ≤ 4)) ⇒ (⊥))
        ⟇ ▩) t26_t16_perm t26_t16);
};
refine t26_t15_t26_t16;
end;

opaque symbol t26_t18 : π̇ (p_65 ⟇ ▩) ≔ 
begin
admit;
end;

opaque symbol t26_t19 : π̇ ((p_65 = p_47) ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
simplify;
eval implies_simplify ;
end;

opaque symbol t26_t20 : π̇ ((¬ (p_65))  ⟇ p_47 ⟇ ▩) ≔ 
begin
apply equiv1 t26_t19;
end;

opaque symbol t26_t21 : π̇ (p_47 ⟇ ▩) ≔ 
begin
have t26_t18_t26_t20 : π̇ (p_47 ⟇ ▩) {
    apply resolutionₗ _ _ _ t26_t18 t26_t20;
};
refine t26_t18_t26_t20;
end;

opaque symbol t26_t22 : π̇ (p_49 ⟇ ▩) ≔ 
begin
have t26_t0_t26_t12 : π̇ ((¬ (p_47))  ⟇ p_49 ⟇ ▩) {
    apply resolutionᵣ _ _ _ t26_t0 t26_t12;
};
have t26_t0_t26_t12_t26_t21 : π̇ (p_49 ⟇ ▩) {
    apply resolutionᵣ _ _ _ t26_t0_t26_t12 t26_t21;
};
refine t26_t0_t26_t12_t26_t21;
end;

opaque symbol t26_t23 : π̇ ((¬ ((p_48 = p_104)))  ⟇ p_47  ⟇ p_104 ⟇ ▩) ≔ 
begin
apply equiv_pos2;
end;

opaque symbol t26_t24 : π̇ ((p_104 = p_12) ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
apply feq (¬) (π̇ₗ t26_t10);
end;

opaque symbol t26_t25 : π̇ ((p_12 = p_104) ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
symmetry;
apply (π̇ₗ t26_t24);
end;

opaque symbol t26_t26 : π̇ (p_103 ⟇ ▩) ≔ 
begin
apply (trans t26_t6 t26_t25);
end;

opaque symbol t26_t27 : π̇ (p_86  ⟇ p_48 ⟇ ▩) ≔ 
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

opaque symbol t26_t28 : π̇ (p_88  ⟇ p_11  ⟇ p_87 ⟇ ▩) ≔ 
begin
apply equiv_pos2;
end;

opaque symbol t26_t29 : π̇ (p_90 ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
apply arith-elim-lt (f 5) 5;
end;

opaque symbol t26_t30 : π̇ (p_89 ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
symmetry;
apply (π̇ₗ t26_t29);
end;

opaque symbol t26_t31 : π̇ (p_30 ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
apply imply_to_or;
assume H;
refine (H 5);
end;

opaque symbol t26_t32 : π̇ (p_31  ⟇ p_12 ⟇ ▩) ≔ 
begin
admit;
end;

opaque symbol t26_t33 : π̇ (p_33  ⟇ p_37  ⟇ p_35 ⟇ ▩) ≔ 
begin
apply equiv_pos2;
end;

opaque symbol t26_t34 : π̇ (p_38 ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
apply bind_∀;
assume x;
have t26_t34_t0 : π̇ (((0 < (f x)) = (¬ ((0 ≥ (f x))))) ⟇ ▩) {
    apply ∨ᵢ₁;
    apply arith-elim-lt 0 (f x);
};
have t26_t34_t1 : π̇ (((0 ≥ (f x)) = (p_40 ≤ (— (f x)))) ⟇ ▩) {
    apply ∨ᵢ₁;
    apply arith-geq-norm2 0 (f x);
};
have t26_t34_t2 : π̇ (((p_40 ≤ (— (f x))) = (¬ ((p_40 ≥ ((— (f x)) + 1))))) ⟇ ▩) {
    apply ∨ᵢ₁;
    apply arith-leq-norm (— 0) (— (f x));
};
have t26_t34_t3 : π̇ ((((— 1) * (p_40 - ((— (f x)) + 1))) = ((— 1) * ((f x) - 1))) ⟇ ▩) {
    apply ∨ᵢ₁;
    simplify;
    rewrite left  .[x in _ = x] reify_correct;
    rewrite left  .[x in x = _] reify_correct;
    reflexivity;
};
have t26_t34_t4 : π̇ (((p_40 ≥ ((— (f x)) + 1)) = ((f x) ≥ 1)) ⟇ ▩) {
    admit;
};
have t26_t34_t5 : π̇ (((¬ ((p_40 ≥ ((— (f x)) + 1)))) = (¬ (((f x) ≥ 1)))) ⟇ ▩) {
    apply ∨ᵢ₁;
    apply feq (¬) (π̇ₗ t26_t34_t4);
};
have t26_t34_t6 : π̇ (((p_40 ≤ (— (f x))) = (¬ (((f x) ≥ 1)))) ⟇ ▩) {
    apply (trans t26_t34_t2 t26_t34_t5);
};
have t26_t34_t7 : π̇ (((0 ≥ (f x)) = (¬ (((f x) ≥ 1)))) ⟇ ▩) {
    apply (trans t26_t34_t1 t26_t34_t6);
};
have t26_t34_t8 : π̇ (((¬ ((0 ≥ (f x)))) = (¬ ((¬ (((f x) ≥ 1)))))) ⟇ ▩) {
    apply ∨ᵢ₁;
    apply feq (¬) (π̇ₗ t26_t34_t7);
};
have t26_t34_t9 : π̇ (((¬ ((¬ (((f x) ≥ 1))))) = ((f x) ≥ 1)) ⟇ ▩) {
    apply ∨ᵢ₁;
    apply bool-double-not-elim ((f x) ≥ 1);
};
have t26_t34_t10 : π̇ (((¬ ((0 ≥ (f x)))) = ((f x) ≥ 1)) ⟇ ▩) {
    apply (trans t26_t34_t8 t26_t34_t9);
};
have t26_t34_t11 : π̇ (((0 < (f x)) = ((f x) ≥ 1)) ⟇ ▩) {
    apply (trans t26_t34_t0 t26_t34_t10);
};
have t26_t34_t12 : π̇ ((((f x) < 5) = (¬ (((f x) ≥ 5)))) ⟇ ▩) {
    apply ∨ᵢ₁;
    apply arith-elim-lt (f x) 5;
};
have t26_t34_t13 : π̇ ((((0 < (f x)) ∧ ((f x) < 5)) = (((f x) ≥ 1) ∧ (¬ (((f x) ≥ 5))))) ⟇ ▩) {
    apply cong_and 
    {
        apply t26_t34_t11;
    }
    {
        apply t26_t34_t12;
    };
};
apply π̇ₗ t26_t34_t13;
end;

opaque symbol t26_t35 : π̇ (p_41 ⟇ ▩) ≔ 
begin
admit;
end;

opaque symbol t26_t36 : π̇ (p_34 ⟇ ▩) ≔ 
begin
apply (trans t26_t34 t26_t35);
end;

opaque symbol t26_t37 : π̇ (p_35 ⟇ ▩) ≔ 
begin
have t26_t33_t26_t36 : π̇ (p_37  ⟇ p_35 ⟇ ▩) {
    apply resolutionᵣ _ _ _ t26_t33 t26_t36;
};
have t26_t33_t26_t36_a1 : π̇ (p_35 ⟇ ▩) {
    apply resolutionᵣ _ _ _ t26_t33_t26_t36 a1;
};
refine t26_t33_t26_t36_a1;
end;

opaque symbol t26_t38 : π̇ (p_32 ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
apply (∧ₑ₂ (π̇ₗ t26_t37));
end;

opaque symbol t26_t39 : π̇ (p_12 ⟇ ▩) ≔ 
begin
have t26_t32_t26_t38 : π̇ (p_12 ⟇ ▩) {
    apply resolutionᵣ _ _ _ t26_t32 t26_t38;
};
refine t26_t32_t26_t38;
end;

opaque symbol t26_t40 : π̇ (p_87 ⟇ ▩) ≔ 
begin
have t26_t28_t26_t30 : π̇ (p_11  ⟇ p_87 ⟇ ▩) {
    apply resolutionᵣ _ _ _ t26_t28 t26_t30;
};
have t26_t28_t26_t30_t26_t39 : π̇ (p_87 ⟇ ▩) {
    apply resolutionᵣ _ _ _ t26_t28_t26_t30 t26_t39;
};
refine t26_t28_t26_t30_t26_t39;
end;

opaque symbol t26_t41 : π̇ (p_48 ⟇ ▩) ≔ 
begin
have t26_t27_t26_t40 : π̇ (p_48 ⟇ ▩) {
    apply resolutionᵣ _ _ _ t26_t27 t26_t40;
};
refine t26_t27_t26_t40;
end;

opaque symbol t26_t42 : π̇ (p_104 ⟇ ▩) ≔ 
begin
have t26_t23_t26_t26 : π̇ (p_47  ⟇ p_104 ⟇ ▩) {
    apply resolutionᵣ _ _ _ t26_t23 t26_t26;
};
have t26_t23_t26_t26_t26_t41 : π̇ (p_104 ⟇ ▩) {
    apply resolutionᵣ _ _ _ t26_t23_t26_t26 t26_t41;
};
refine t26_t23_t26_t26_t26_t41;
end;

opaque symbol t26_t43 : π̇ ▩ ≔ 
begin
have t26_t22_t26_t42 : π̇ ▩ {
    apply resolutionₗ _ _ _ t26_t22 t26_t42;
};
refine t26_t22_t26_t42;
end;

opaque symbol t26 : π̇ (p_11  ⟇ p_10  ⟇ ⊥ ⟇ ▩) ≔ 
begin
// apply ∨ᵢ₂;
// apply ∨ᵢ₂;
// apply ∨ᵢ₁;
// apply (π̇ₗ t26_t43);
admit
end;

opaque symbol t27 : π̇ (p_43  ⟇ p_12 ⟇ ▩) ≔ 
begin
admit
end;

opaque symbol t28 : π̇ (p_43  ⟇ p_4 ⟇ ▩) ≔ 
begin
refine and_pos Stdlib.Nat._1 (¬ (f _5 ≥ _5) ⸬ (f _5 = (_2 + (_10 * _1))) ⸬ □) ⊤ᵢ; 
//reflexivity;
end;

opaque symbol t29 : π̇ (⊥  ⟇ p_43  ⟇ p_43 ⟇ ▩) ≔ 
begin
have t26_t27 : π̇ (p_10  ⟇ ⊥  ⟇ p_43 ⟇ ▩) {
    have t27_perm : π ((⟇_to_∨_rw ((¬ (((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))))
             ⟇ (¬ (((f 5) ≥ 5)))
            ⟇ ▩)) = (⟇_to_∨_rw ((¬ (((f 5) ≥ 5)))  ⟇ (¬ (((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12)))) ⟇ ▩))) {
        apply (cl_perm_correct ((¬ (((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))))  ⟇ (¬ (((f 5) ≥ 5))) ⟇ ▩) ((¬ (((f 5) ≥ 5)))
             ⟇ (¬ (((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))))
            ⟇ ▩));
        apply ⊤ᵢ;
    };
    apply resolutionᵣ _ _ _ t26 (subst_equiv_clause ((¬ (((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))))
         ⟇ (¬ (((f 5) ≥ 5)))
        ⟇ ▩) ((¬ (((f 5) ≥ 5)))  ⟇ (¬ (((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12)))) ⟇ ▩) t27_perm t27);
};
have t26_t27_t28 : π̇ (⊥  ⟇ p_43  ⟇ p_43 ⟇ ▩) {
    have t28_perm : π ((⟇_to_∨_rw ((¬ (((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))))
             ⟇ ((f 5) = 12)
            ⟇ ▩)) = (⟇_to_∨_rw (((f 5) = 12)  ⟇ (¬ (((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12)))) ⟇ ▩))) {
        apply (cl_perm_correct ((¬ (((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))))  ⟇ ((f 5) = 12) ⟇ ▩) (((f 5) = 12)
             ⟇ (¬ (((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))))
            ⟇ ▩));
        apply ⊤ᵢ;
    };
    apply resolutionᵣ _ _ _ t26_t27 (subst_equiv_clause ((¬ (((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))))
         ⟇ ((f 5) = 12)
        ⟇ ▩) (((f 5) = 12)  ⟇ (¬ (((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12)))) ⟇ ▩) t28_perm t28);
};
refine t26_t27_t28;
end;

opaque symbol t30 : π̇ (p_43  ⟇ p_43  ⟇ ⊥ ⟇ ▩) ≔ 
begin
admit;
end;

opaque symbol t31 : π̇ (p_43  ⟇ ⊥ ⟇ ▩) ≔ 
begin
admit;
end;

opaque symbol t32 : π̇ (p_44  ⟇ ⊥ ⟇ ▩) ≔ 
begin
have t25_t31 : π̇ (p_44  ⟇ ⊥ ⟇ ▩) {
    have t25_perm : π ((⟇_to_∨_rw (((((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))) ⇒ (⊥))
             ⟇ ((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))
            ⟇ ▩)) = (⟇_to_∨_rw (((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))
             ⟇ ((((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))) ⇒ (⊥))
            ⟇ ▩))) {
        apply (cl_perm_correct (((((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))) ⇒ (⊥))
             ⟇ ((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))
            ⟇ ▩) (((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))  ⟇ ((((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))) ⇒ (⊥)) ⟇ ▩));
        apply ⊤ᵢ;
    };
    apply resolutionₗ _ _ _ (subst_equiv_clause (((((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))) ⇒ (⊥))
         ⟇ ((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))
        ⟇ ▩) (((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))  ⟇ ((((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))) ⇒ (⊥)) ⟇ ▩) t25_perm t25) t31;
};
refine t25_t31;
end;

opaque symbol t33 : π̇ (p_44  ⟇ p_99 ⟇ ▩) ≔ 
begin
apply implies_neg2;
end;

opaque symbol t34 : π̇ (p_44  ⟇ p_44 ⟇ ▩) ≔ 
begin
have t32_t33 : π̇ (p_44  ⟇ p_44 ⟇ ▩) {
    have t32_perm : π ((⟇_to_∨_rw (((((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))) ⇒ (⊥))  ⟇ ⊥ ⟇ ▩)) = (⟇_to_∨_rw (⊥
             ⟇ ((((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))) ⇒ (⊥))
            ⟇ ▩))) {
        apply (cl_perm_correct (((((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))) ⇒ (⊥))  ⟇ ⊥ ⟇ ▩) (⊥
             ⟇ ((((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))) ⇒ (⊥))
            ⟇ ▩));
        apply ⊤ᵢ;
    };
    have t33_perm : π ((⟇_to_∨_rw (((((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))) ⇒ (⊥))  ⟇ (¬ (⊥)) ⟇ ▩)) = (⟇_to_∨_rw ((¬ (⊥))
             ⟇ ((((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))) ⇒ (⊥))
            ⟇ ▩))) {
        apply (cl_perm_correct (((((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))) ⇒ (⊥))  ⟇ (¬ (⊥)) ⟇ ▩) ((¬ (⊥))
             ⟇ ((((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))) ⇒ (⊥))
            ⟇ ▩));
        apply ⊤ᵢ;
    };
    apply resolutionₗ _ _ _ (subst_equiv_clause (((((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))) ⇒ (⊥))  ⟇ ⊥ ⟇ ▩) (⊥
         ⟇ ((((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))) ⇒ (⊥))
        ⟇ ▩) t32_perm t32) (subst_equiv_clause (((((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))) ⇒ (⊥))  ⟇ (¬ (⊥)) ⟇ ▩) ((¬ (⊥))
         ⟇ ((((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))) ⇒ (⊥))
        ⟇ ▩) t33_perm t33);
};
refine t32_t33;
end;

opaque symbol t35 : π̇ (p_44 ⟇ ▩) ≔ 
begin
admit;
end;

opaque symbol t36 : π̇ ((p_44 = p_43) ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
simplify;
eval implies_simplify ;
end;

opaque symbol t37 : π̇ ((¬ (p_44))  ⟇ p_43 ⟇ ▩) ≔ 
begin
apply equiv1 t36;
end;

opaque symbol t38 : π̇ (p_43 ⟇ ▩) ≔ 
begin
have t35_t37 : π̇ (p_43 ⟇ ▩) {
    apply resolutionₗ _ _ _ t35 t37;
};
refine t35_t37;
end;

opaque symbol t39 : π̇ (p_42 ⟇ ▩) ≔ 
begin
have t24_t38 : π̇ (p_42 ⟇ ▩) {
    have t24_perm : π ((⟇_to_∨_rw ((¬ ((((f 5) = 12) ∧ (¬ (((f 5) ≥ 5))))))
             ⟇ ((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))
            ⟇ ▩)) = (⟇_to_∨_rw (((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))  ⟇ (¬ ((((f 5) = 12) ∧ (¬ (((f 5) ≥ 5)))))) ⟇ ▩))) {
        apply (cl_perm_correct ((¬ ((((f 5) = 12) ∧ (¬ (((f 5) ≥ 5))))))
             ⟇ ((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))
            ⟇ ▩) (((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))  ⟇ (¬ ((((f 5) = 12) ∧ (¬ (((f 5) ≥ 5)))))) ⟇ ▩));
        apply ⊤ᵢ;
    };
    apply resolutionₗ _ _ _ (subst_equiv_clause ((¬ ((((f 5) = 12) ∧ (¬ (((f 5) ≥ 5))))))
         ⟇ ((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))
        ⟇ ▩) (((¬ (((f 5) ≥ 5))) ∧ ((f 5) = 12))  ⟇ (¬ ((((f 5) = 12) ∧ (¬ (((f 5) ≥ 5)))))) ⟇ ▩) t24_perm t24) t38;
};
refine t24_t38;
end;

opaque symbol t40 : π̇ (p_10  ⟇ p_11 ⟇ ▩) ≔ 
begin
refine not_and ((f _5 = (_2 + (_10 * _1))) ⸬ (¬ (f _5 ≥ _5)) ⸬ □) (π̇ₗ t39);
end;

opaque symbol t41 : π̇ (p_9  ⟇ (¬ (p_10)) ⟇ ▩) ≔ 
begin
simplify p_9;
simplify p_10;
set X ≔ (f _5 = (_2 + (_10 * _1)));
set Y ≔ (¬ (f _5 ≥ _5));
apply sym_clause;
refine or_neg Stdlib.Nat._0 (¬ X ⸬ ¬ Y ⸬ □) _ ⊤ᵢ;
simplify;
rewrite or_identity_r;
rewrite or_identity_r;
reflexivity
end;

opaque symbol t42 : π̇ (p_9  ⟇ (¬ (p_11)) ⟇ ▩) ≔ 
begin
apply or_neg;
reflexivity;
end;

opaque symbol t43 : π̇ (p_9  ⟇ p_9 ⟇ ▩) ≔ 
begin
have t40_t41 : π̇ (p_11  ⟇ p_9 ⟇ ▩) {
    have t41_perm : π ((⟇_to_∨_rw (((¬ (((f 5) = 12))) ∨ (¬ ((¬ (((f 5) ≥ 5))))))
             ⟇ (¬ ((¬ (((f 5) = 12)))))
            ⟇ ▩)) = (⟇_to_∨_rw ((¬ ((¬ (((f 5) = 12)))))  ⟇ ((¬ (((f 5) = 12))) ∨ (¬ ((¬ (((f 5) ≥ 5)))))) ⟇ ▩))) {
        apply (cl_perm_correct (((¬ (((f 5) = 12))) ∨ (¬ ((¬ (((f 5) ≥ 5))))))
             ⟇ (¬ ((¬ (((f 5) = 12)))))
            ⟇ ▩) ((¬ ((¬ (((f 5) = 12)))))  ⟇ ((¬ (((f 5) = 12))) ∨ (¬ ((¬ (((f 5) ≥ 5)))))) ⟇ ▩));
        apply ⊤ᵢ;
    };
    apply resolutionₗ _ _ _ t40 (subst_equiv_clause (((¬ (((f 5) = 12))) ∨ (¬ ((¬ (((f 5) ≥ 5))))))
         ⟇ (¬ ((¬ (((f 5) = 12)))))
        ⟇ ▩) ((¬ ((¬ (((f 5) = 12)))))  ⟇ ((¬ (((f 5) = 12))) ∨ (¬ ((¬ (((f 5) ≥ 5)))))) ⟇ ▩) t41_perm t41);
};
have t40_t41_t42 : π̇ (p_9  ⟇ p_9 ⟇ ▩) {
    have t42_perm : π ((⟇_to_∨_rw (((¬ (((f 5) = 12))) ∨ (¬ ((¬ (((f 5) ≥ 5))))))
             ⟇ (¬ ((¬ ((¬ (((f 5) ≥ 5)))))))
            ⟇ ▩)) = (⟇_to_∨_rw ((¬ ((¬ ((¬ (((f 5) ≥ 5)))))))  ⟇ ((¬ (((f 5) = 12))) ∨ (¬ ((¬ (((f 5) ≥ 5)))))) ⟇ ▩))) {
        apply (cl_perm_correct (((¬ (((f 5) = 12))) ∨ (¬ ((¬ (((f 5) ≥ 5))))))
             ⟇ (¬ ((¬ ((¬ (((f 5) ≥ 5)))))))
            ⟇ ▩) ((¬ ((¬ ((¬ (((f 5) ≥ 5)))))))  ⟇ ((¬ (((f 5) = 12))) ∨ (¬ ((¬ (((f 5) ≥ 5)))))) ⟇ ▩));
        apply ⊤ᵢ;
    };
    apply resolutionₗ _ _ _ t40_t41 (subst_equiv_clause (((¬ (((f 5) = 12))) ∨ (¬ ((¬ (((f 5) ≥ 5))))))
         ⟇ (¬ ((¬ ((¬ (((f 5) ≥ 5)))))))
        ⟇ ▩) ((¬ ((¬ ((¬ (((f 5) ≥ 5)))))))  ⟇ ((¬ (((f 5) = 12))) ∨ (¬ ((¬ (((f 5) ≥ 5)))))) ⟇ ▩) t42_perm t42);
};
refine t40_t41_t42;
end;

opaque symbol t44 : π̇ (p_9 ⟇ ▩) ≔ 
begin
admit;
end;

opaque symbol t45 : π̇ (p_14 ⟇ ▩) ≔ 
begin
have t0_t12 : π̇ ((¬ (p_9))  ⟇ p_14 ⟇ ▩) {
    apply resolutionᵣ _ _ _ t0 t12;
};
have t0_t12_t44 : π̇ (p_14 ⟇ ▩) {
    apply resolutionᵣ _ _ _ t0_t12 t44;
};
refine t0_t12_t44;
end;

opaque symbol t46 : π̇ (p_10  ⟇ p_13 ⟇ ▩) ≔ 
begin
admit;
end;

opaque symbol t47 : π̇ (p_30 ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
apply imply_to_or;
assume H;
refine (H 5);
end;

opaque symbol t48 : π̇ (p_31  ⟇ p_12 ⟇ ▩) ≔ 
begin
admit;
end;

opaque symbol t49 : π̇ (p_33  ⟇ p_37  ⟇ p_35 ⟇ ▩) ≔ 
begin
apply equiv_pos2;
end;

opaque symbol t50 : π̇ (p_38 ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
apply bind_∀;
assume x;
have t50_t0 : π̇ (((0 < (f x)) = (¬ ((0 ≥ (f x))))) ⟇ ▩) {
    apply ∨ᵢ₁;
    apply arith-elim-lt 0 (f x);
};
have t50_t1 : π̇ (((0 ≥ (f x)) = (p_40 ≤ (— (f x)))) ⟇ ▩) {
    apply ∨ᵢ₁;
    apply arith-geq-norm2 0 (f x);
};
have t50_t2 : π̇ (((p_40 ≤ (— (f x))) = (¬ ((p_40 ≥ ((— (f x)) + 1))))) ⟇ ▩) {
    apply ∨ᵢ₁;
    apply arith-leq-norm (— 0) (— (f x));
};
have t50_t3 : π̇ ((((— 1) * (p_40 - ((— (f x)) + 1))) = ((— 1) * ((f x) - 1))) ⟇ ▩) {
    apply ∨ᵢ₁;
    simplify;
    rewrite left  .[x in _ = x] reify_correct;
    rewrite left  .[x in x = _] reify_correct;
    reflexivity;
};
have t50_t4 : π̇ (((p_40 ≥ ((— (f x)) + 1)) = ((f x) ≥ 1)) ⟇ ▩) {
    admit;
};
have t50_t5 : π̇ (((¬ ((p_40 ≥ ((— (f x)) + 1)))) = (¬ (((f x) ≥ 1)))) ⟇ ▩) {
    apply ∨ᵢ₁;
    apply feq (¬) (π̇ₗ t50_t4);
};
have t50_t6 : π̇ (((p_40 ≤ (— (f x))) = (¬ (((f x) ≥ 1)))) ⟇ ▩) {
    apply (trans t50_t2 t50_t5);
};
have t50_t7 : π̇ (((0 ≥ (f x)) = (¬ (((f x) ≥ 1)))) ⟇ ▩) {
    apply (trans t50_t1 t50_t6);
};
have t50_t8 : π̇ (((¬ ((0 ≥ (f x)))) = (¬ ((¬ (((f x) ≥ 1)))))) ⟇ ▩) {
    apply ∨ᵢ₁;
    apply feq (¬) (π̇ₗ t50_t7);
};
have t50_t9 : π̇ (((¬ ((¬ (((f x) ≥ 1))))) = ((f x) ≥ 1)) ⟇ ▩) {
    apply ∨ᵢ₁;
    apply bool-double-not-elim ((f x) ≥ 1);
};
have t50_t10 : π̇ (((¬ ((0 ≥ (f x)))) = ((f x) ≥ 1)) ⟇ ▩) {
    apply (trans t50_t8 t50_t9);
};
have t50_t11 : π̇ (((0 < (f x)) = ((f x) ≥ 1)) ⟇ ▩) {
    apply (trans t50_t0 t50_t10);
};
have t50_t12 : π̇ ((((f x) < 5) = (¬ (((f x) ≥ 5)))) ⟇ ▩) {
    apply ∨ᵢ₁;
    apply arith-elim-lt (f x) 5;
};
have t50_t13 : π̇ ((((0 < (f x)) ∧ ((f x) < 5)) = (((f x) ≥ 1) ∧ (¬ (((f x) ≥ 5))))) ⟇ ▩) {
    apply cong_and 
    {
        apply t50_t11;
    }
    {
        apply t50_t12;
    };
};
apply π̇ₗ t50_t13;
end;

opaque symbol t51 : π̇ (p_41 ⟇ ▩) ≔ 
begin
admit;
end;

opaque symbol t52 : π̇ (p_34 ⟇ ▩) ≔ 
begin
apply (trans t50 t51);
end;

opaque symbol t53 : π̇ (p_35 ⟇ ▩) ≔ 
begin
have t49_t52 : π̇ (p_37  ⟇ p_35 ⟇ ▩) {
    apply resolutionᵣ _ _ _ t49 t52;
};
have t49_t52_a1 : π̇ (p_35 ⟇ ▩) {
    apply resolutionᵣ _ _ _ t49_t52 a1;
};
refine t49_t52_a1;
end;

opaque symbol t54 : π̇ (p_32 ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
apply (∧ₑ₂ (π̇ₗ t53));
end;

opaque symbol t55 : π̇ (p_12 ⟇ ▩) ≔ 
begin
have t48_t54 : π̇ (p_12 ⟇ ▩) {
    apply resolutionᵣ _ _ _ t48 t54;
};
refine t48_t54;
end;

opaque symbol t56 : π̇ (p_2  ⟇ p_4 ⟇ ▩) ≔ 
begin
admit;
end;

opaque symbol t57 : π̇ ((¬ ((p_113 = p_118)))  ⟇ (¬ (p_113))  ⟇ p_118 ⟇ ▩) ≔ 
begin
apply equiv_pos2;
end;

opaque symbol t58 : π̇ ((p_114 = p_114) ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
reflexivity;
end;

opaque symbol t59 : π̇ (((p_123 = ⊤) = p_123) ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
simplify;
eval equiv_simplify ;
end;

opaque symbol t60 : π̇ ((¬ (p_122))  ⟇ p_123 ⟇ ▩) ≔ 
begin
apply equiv1 t59;
end;

opaque symbol t61 : π̇ ((p_123 = (p_117 = p_115)) ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
apply eq-symm (¬ ((¬ (((f 0) ≥ 5))))) ((f 0) ≥ 5);
end;

opaque symbol t62 : π̇ ((p_117 = p_117) ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
reflexivity;
end;

opaque symbol t63 : π̇ (p_123 ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
apply bool-double-not-elim ((f 0) ≥ 5);
end;

opaque symbol t64 : π̇ ((p_126 = p_127) ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
apply (feq2 (=) (π̇ₗ t62) (π̇ₗ t63));
end;

opaque symbol t65 : π̇ ((p_127 = ⊤) ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
apply eq-refl ((f 0) ≥ 5);
end;

opaque symbol t66 : π̇ ((p_126 = ⊤) ⟇ ▩) ≔ 
begin
apply (trans t64 t65);
end;

opaque symbol t67 : π̇ (p_122 ⟇ ▩) ≔ 
begin
apply (trans t61 t66);
end;

opaque symbol t68 : π̇ (p_123 ⟇ ▩) ≔ 
begin
have t60_t67 : π̇ (p_123 ⟇ ▩) {
    apply resolutionᵣ _ _ _ t60 t67;
};
refine t60_t67;
end;

opaque symbol t69 : π̇ (p_112 ⟇ ▩) ≔ 
begin
apply cong_or 
{
    apply t58;
}
{
    apply t68;
};
end;

opaque symbol t70 : π̇ (((p_132) ⇒ (⊥))  ⟇ p_132 ⟇ ▩) ≔ 
begin
apply implies_neg1;
end;

opaque symbol t71_a0 : π̇ (p_2 ⟇ ▩) ≔ 
begin
admit;
end;

opaque symbol t71_a1 : π̇ (p_116 ⟇ ▩) ≔ 
begin
admit;
end;

opaque symbol t71_t0 : π̇ (((p_2) ⇒ (⊥))  ⟇ p_2 ⟇ ▩) ≔ 
begin
apply implies_neg1;
end;

opaque symbol t71_t1_a0 : π̇ (p_2 ⟇ ▩) ≔ 
begin
admit;
end;

opaque symbol t71_t1_t0 : π̇ ((¬ ((p_136 = ⊥)))  ⟇ (¬ (p_136))  ⟇ ⊥ ⟇ ▩) ≔ 
begin
apply equiv_pos2;
end;

opaque symbol t71_t1_t1 : π̇ ((p_137 = 0) ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
simplify;
rewrite left  .[x in _ = x] reify_correct;
rewrite left  .[x in x = _] reify_correct;
//reflexivity;
admit
end;

opaque symbol t71_t1_t2 : π̇ ((p_140 = (— 10)) ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
simplify;
reflexivity;
end;

opaque symbol t71_t1_t3 : π̇ (p_75 ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
reflexivity;
end;

opaque symbol t71_t1_t4 : π̇ ((p_139 = ((— 10) + 4)) ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
apply (feq2 (+) (π̇ₗ t71_t1_t2) (π̇ₗ t71_t1_t3));
end;

opaque symbol t71_t1_t5 : π̇ ((p_145 = (— 6)) ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
simplify;
reflexivity;
end;

opaque symbol t71_t1_t6 : π̇ ((p_139 = (— 6)) ⟇ ▩) ≔ 
begin
apply (trans t71_t1_t4 t71_t1_t5);
end;

opaque symbol t71_t1_t7 : π̇ ((p_136 = (0 ≤ (— 6))) ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
apply (feq2 (≤) (π̇ₗ t71_t1_t1) (π̇ₗ t71_t1_t6));
end;

opaque symbol t71_t1_t8 : π̇ ((p_149 = ⊥) ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
admit;
end;

opaque symbol t71_t1_t9 : π̇ (p_135 ⟇ ▩) ≔ 
begin
apply (trans t71_t1_t7 t71_t1_t8);
end;

opaque symbol t71_t1_t10 : π̇ ((¬ ((p_138 = p_140)))  ⟇ (¬ ((p_3 ≤ 4)))  ⟇ p_136 ⟇ ▩) ≔ 
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

opaque symbol t71_t1_t11 : π̇ ((((p_93 ∧ p_2)) ⇒ (p_152)) ⟇ ▩) ≔ 
begin
admit;
end;

opaque symbol t71_t1_t12 : π̇ ((¬ (p_156))  ⟇ p_152 ⟇ ▩) ≔ 
begin
apply implies (π̇ₗ t71_t1_t11);
end;

opaque symbol t71_t1_t13 : π̇ (p_156  ⟇ p_95  ⟇ p_114 ⟇ ▩) ≔ 
begin
apply and_neg;
reflexivity;
end;

opaque symbol t71_t1_t14 : π̇ (p_96 ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
simplify;
eval equiv_simplify ;
end;

opaque symbol t71_t1_t15 : π̇ (p_98  ⟇ p_93 ⟇ ▩) ≔ 
begin
apply equiv1 t71_t1_t14;
end;

opaque symbol t71_t1_t16 : π̇ (p_97 ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
admit;
end;

opaque symbol t71_t1_t17 : π̇ (p_93 ⟇ ▩) ≔ 
begin
have t71_t1_t15_t71_t1_t16 : π̇ (p_93 ⟇ ▩) {
    apply resolutionᵣ _ _ _ t71_t1_t15 t71_t1_t16;
};
refine t71_t1_t15_t71_t1_t16;
end;

opaque symbol t71_t1_t18 : π̇ (p_156 ⟇ ▩) ≔ 
begin
have t71_t1_t13_t71_t1_t17 : π̇ (p_156  ⟇ p_114 ⟇ ▩) {
    have t71_t1_t13_perm : π ((⟇_to_∨_rw ((((— 1) < 0) ∧ ((f 0) = 10))
             ⟇ (¬ (((— 1) < 0)))
             ⟇ (¬ (((f 0) = 10)))
            ⟇ ▩)) = (⟇_to_∨_rw ((¬ (((— 1) < 0)))  ⟇ (((— 1) < 0) ∧ ((f 0) = 10))  ⟇ (¬ (((f 0) = 10))) ⟇ ▩))) {
        apply (cl_perm_correct ((((— 1) < 0) ∧ ((f 0) = 10))
             ⟇ (¬ (((— 1) < 0)))
             ⟇ (¬ (((f 0) = 10)))
            ⟇ ▩) ((¬ (((— 1) < 0)))  ⟇ (((— 1) < 0) ∧ ((f 0) = 10))  ⟇ (¬ (((f 0) = 10))) ⟇ ▩));
        apply ⊤ᵢ;
    };
    apply resolutionᵣ _ _ _ (subst_equiv_clause ((((— 1) < 0) ∧ ((f 0) = 10))
         ⟇ (¬ (((— 1) < 0)))
         ⟇ (¬ (((f 0) = 10)))
        ⟇ ▩) ((¬ (((— 1) < 0)))
         ⟇ (((— 1) < 0) ∧ ((f 0) = 10))
         ⟇ (¬ (((f 0) = 10)))
        ⟇ ▩) t71_t1_t13_perm t71_t1_t13) t71_t1_t17;
};
have t71_t1_t13_t71_t1_t17_t71_t1_a0 : π̇ (p_156 ⟇ ▩) {
    have t71_t1_t13_t71_t1_t17_perm : π ((⟇_to_∨_rw ((((— 1) < 0) ∧ ((f 0) = 10))
             ⟇ (¬ (((f 0) = 10)))
            ⟇ ▩)) = (⟇_to_∨_rw ((¬ (((f 0) = 10)))  ⟇ (((— 1) < 0) ∧ ((f 0) = 10)) ⟇ ▩))) {
        apply (cl_perm_correct ((((— 1) < 0) ∧ ((f 0) = 10))  ⟇ (¬ (((f 0) = 10))) ⟇ ▩) ((¬ (((f 0) = 10)))
             ⟇ (((— 1) < 0) ∧ ((f 0) = 10))
            ⟇ ▩));
        apply ⊤ᵢ;
    };
    apply resolutionᵣ _ _ _ (subst_equiv_clause ((((— 1) < 0) ∧ ((f 0) = 10))
         ⟇ (¬ (((f 0) = 10)))
        ⟇ ▩) ((¬ (((f 0) = 10)))
         ⟇ (((— 1) < 0) ∧ ((f 0) = 10))
        ⟇ ▩) t71_t1_t13_t71_t1_t17_perm t71_t1_t13_t71_t1_t17) t71_t1_a0;
};
refine t71_t1_t13_t71_t1_t17_t71_t1_a0;
end;

opaque symbol t71_t1_t19 : π̇ (p_152 ⟇ ▩) ≔ 
begin
have t71_t1_t12_t71_t1_t18 : π̇ (p_152 ⟇ ▩) {
    apply resolutionᵣ _ _ _ t71_t1_t12 t71_t1_t18;
};
refine t71_t1_t12_t71_t1_t18;
end;

opaque symbol t71_t1_t20 : π̇ ((¬ ((p_3 < 5)))  ⟇ p_154 ⟇ ▩) ≔ 
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

opaque symbol t71_t1_t21 : π̇ ((¬ ((p_116 = p_159)))  ⟇ p_115  ⟇ p_159 ⟇ ▩) ≔ 
begin
apply equiv_pos2;
end;

opaque symbol t71_t1_t22 : π̇ ((p_159 = p_116) ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
apply arith-elim-lt (f 0) 5;
end;

opaque symbol t71_t1_t23 : π̇ (p_161 ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
symmetry;
apply (π̇ₗ t71_t1_t22);
end;

opaque symbol t71_t1_t24 : π̇ ((p_31 ∨ p_116) ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
apply imply_to_or;
assume H;
refine (H 0);
end;

opaque symbol t71_t1_t25 : π̇ (p_31  ⟇ p_116 ⟇ ▩) ≔ 
begin
admit;
end;

opaque symbol t71_t1_t26 : π̇ (p_116 ⟇ ▩) ≔ 
begin
have t71_t1_t25_t54 : π̇ (p_116 ⟇ ▩) {
    apply resolutionᵣ _ _ _ t71_t1_t25 t54;
};
refine t71_t1_t25_t54;
end;

opaque symbol t71_t1_t27 : π̇ (p_159 ⟇ ▩) ≔ 
begin
have t71_t1_t21_t71_t1_t23 : π̇ (p_115  ⟇ p_159 ⟇ ▩) {
    apply resolutionᵣ _ _ _ t71_t1_t21 t71_t1_t23;
};
have t71_t1_t21_t71_t1_t23_t71_t1_t26 : π̇ (p_159 ⟇ ▩) {
    apply resolutionᵣ _ _ _ t71_t1_t21_t71_t1_t23 t71_t1_t26;
};
refine t71_t1_t21_t71_t1_t23_t71_t1_t26;
end;

opaque symbol t71_t1_t28 : π̇ (p_154 ⟇ ▩) ≔ 
begin
have t71_t1_t20_t71_t1_t27 : π̇ (p_154 ⟇ ▩) {
    apply resolutionᵣ _ _ _ t71_t1_t20 t71_t1_t27;
};
refine t71_t1_t20_t71_t1_t27;
end;

opaque symbol t71_t1_t29 : π̇ (p_136 ⟇ ▩) ≔ 
begin
have t71_t1_t10_t71_t1_t19 : π̇ ((¬ (p_154))  ⟇ p_136 ⟇ ▩) {
    apply resolutionᵣ _ _ _ t71_t1_t10 t71_t1_t19;
};
have t71_t1_t10_t71_t1_t19_t71_t1_t28 : π̇ (p_136 ⟇ ▩) {
    apply resolutionᵣ _ _ _ t71_t1_t10_t71_t1_t19 t71_t1_t28;
};
refine t71_t1_t10_t71_t1_t19_t71_t1_t28;
end;

opaque symbol t71_t1_t30 : π̇ (⊥ ⟇ ▩) ≔ 
begin
have t71_t1_t0_t71_t1_t9 : π̇ ((¬ (p_136))  ⟇ ⊥ ⟇ ▩) {
    apply resolutionᵣ _ _ _ t71_t1_t0 t71_t1_t9;
};
have t71_t1_t0_t71_t1_t9_t71_t1_t29 : π̇ (⊥ ⟇ ▩) {
    apply resolutionᵣ _ _ _ t71_t1_t0_t71_t1_t9 t71_t1_t29;
};
refine t71_t1_t0_t71_t1_t9_t71_t1_t29;
end;

opaque symbol t71_t1 : π̇ (p_114  ⟇ ⊥ ⟇ ▩) ≔ 
begin
apply ∨ᵢ₂;
apply t71_t1_t30;
end;

opaque symbol t71_t2 : π̇ (p_133  ⟇ ⊥ ⟇ ▩) ≔ 
begin
have t71_t0_t71_t1 : π̇ (p_133  ⟇ ⊥ ⟇ ▩) {
    have t71_t0_perm : π ((⟇_to_∨_rw (((((f 0) = 10)) ⇒ (⊥))  ⟇ ((f 0) = 10) ⟇ ▩)) = (⟇_to_∨_rw (((f 0) = 10)
             ⟇ ((((f 0) = 10)) ⇒ (⊥))
            ⟇ ▩))) {
        apply (cl_perm_correct (((((f 0) = 10)) ⇒ (⊥))  ⟇ ((f 0) = 10) ⟇ ▩) (((f 0) = 10)
             ⟇ ((((f 0) = 10)) ⇒ (⊥))
            ⟇ ▩));
        apply ⊤ᵢ;
    };
    apply resolutionₗ _ _ _ (subst_equiv_clause (((((f 0) = 10)) ⇒ (⊥))  ⟇ ((f 0) = 10) ⟇ ▩) (((f 0) = 10)
         ⟇ ((((f 0) = 10)) ⇒ (⊥))
        ⟇ ▩) t71_t0_perm t71_t0) t71_t1;
};
refine t71_t0_t71_t1;
end;

opaque symbol t71_t3 : π̇ (p_133  ⟇ p_99 ⟇ ▩) ≔ 
begin
apply implies_neg2;
end;

opaque symbol t71_t4 : π̇ (p_133  ⟇ p_133 ⟇ ▩) ≔ 
begin
have t71_t2_t71_t3 : π̇ (p_133  ⟇ p_133 ⟇ ▩) {
    have t71_t2_perm : π ((⟇_to_∨_rw (((((f 0) = 10)) ⇒ (⊥))  ⟇ ⊥ ⟇ ▩)) = (⟇_to_∨_rw (⊥
             ⟇ ((((f 0) = 10)) ⇒ (⊥))
            ⟇ ▩))) {
        apply (cl_perm_correct (((((f 0) = 10)) ⇒ (⊥))  ⟇ ⊥ ⟇ ▩) (⊥  ⟇ ((((f 0) = 10)) ⇒ (⊥)) ⟇ ▩));
        apply ⊤ᵢ;
    };
    have t71_t3_perm : π ((⟇_to_∨_rw (((((f 0) = 10)) ⇒ (⊥))  ⟇ (¬ (⊥)) ⟇ ▩)) = (⟇_to_∨_rw ((¬ (⊥))
             ⟇ ((((f 0) = 10)) ⇒ (⊥))
            ⟇ ▩))) {
        apply (cl_perm_correct (((((f 0) = 10)) ⇒ (⊥))  ⟇ (¬ (⊥)) ⟇ ▩) ((¬ (⊥))  ⟇ ((((f 0) = 10)) ⇒ (⊥)) ⟇ ▩));
        apply ⊤ᵢ;
    };
    apply resolutionₗ _ _ _ (subst_equiv_clause (((((f 0) = 10)) ⇒ (⊥))  ⟇ ⊥ ⟇ ▩) (⊥
         ⟇ ((((f 0) = 10)) ⇒ (⊥))
        ⟇ ▩) t71_t2_perm t71_t2) (subst_equiv_clause (((((f 0) = 10)) ⇒ (⊥))  ⟇ (¬ (⊥)) ⟇ ▩) ((¬ (⊥))
         ⟇ ((((f 0) = 10)) ⇒ (⊥))
        ⟇ ▩) t71_t3_perm t71_t3);
};
refine t71_t2_t71_t3;
end;

opaque symbol t71_t5 : π̇ (p_133 ⟇ ▩) ≔ 
begin
admit;
end;

opaque symbol t71_t6 : π̇ ((p_133 = p_114) ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
simplify;
eval implies_simplify ;
end;

opaque symbol t71_t7 : π̇ ((¬ (p_133))  ⟇ p_114 ⟇ ▩) ≔ 
begin
apply equiv1 t71_t6;
end;

opaque symbol t71_t8 : π̇ (p_114 ⟇ ▩) ≔ 
begin
have t71_t5_t71_t7 : π̇ (p_114 ⟇ ▩) {
    apply resolutionₗ _ _ _ t71_t5 t71_t7;
};
refine t71_t5_t71_t7;
end;

opaque symbol t71_t9 : π̇ ▩ ≔ 
begin
have t71_a0_t71_t8 : π̇ ▩ {
    apply resolutionₗ _ _ _ t71_a0 t71_t8;
};
refine t71_a0_t71_t8;
end;

opaque symbol t71 : π̇ (p_114  ⟇ p_115  ⟇ ⊥ ⟇ ▩) ≔ 
begin
// apply ∨ᵢ₂;
// apply ∨ᵢ₂;
// apply ∨ᵢ₁;
// apply (π̇ₗ t71_t9);
admit
end;

opaque symbol t72 : π̇ ((¬ (p_132))  ⟇ p_2 ⟇ ▩) ≔ 
begin
apply and_pos;
reflexivity;
end;

opaque symbol t73 : π̇ (p_166  ⟇ p_116 ⟇ ▩) ≔ 
begin
apply and_pos;
reflexivity;
end;

opaque symbol t74 : π̇ (⊥  ⟇ p_166  ⟇ p_166 ⟇ ▩) ≔ 
begin
have t71_t72 : π̇ (p_115  ⟇ ⊥  ⟇ p_166 ⟇ ▩) {
    have t72_perm : π ((⟇_to_∨_rw ((¬ ((((f 0) = 10) ∧ (¬ (((f 0) ≥ 5))))))
             ⟇ ((f 0) = 10)
            ⟇ ▩)) = (⟇_to_∨_rw (((f 0) = 10)  ⟇ (¬ ((((f 0) = 10) ∧ (¬ (((f 0) ≥ 5)))))) ⟇ ▩))) {
        apply (cl_perm_correct ((¬ ((((f 0) = 10) ∧ (¬ (((f 0) ≥ 5))))))  ⟇ ((f 0) = 10) ⟇ ▩) (((f 0) = 10)
             ⟇ (¬ ((((f 0) = 10) ∧ (¬ (((f 0) ≥ 5))))))
            ⟇ ▩));
        apply ⊤ᵢ;
    };
    apply resolutionᵣ _ _ _ t71 (subst_equiv_clause ((¬ ((((f 0) = 10) ∧ (¬ (((f 0) ≥ 5))))))
         ⟇ ((f 0) = 10)
        ⟇ ▩) (((f 0) = 10)  ⟇ (¬ ((((f 0) = 10) ∧ (¬ (((f 0) ≥ 5)))))) ⟇ ▩) t72_perm t72);
};
have t71_t72_t73 : π̇ (⊥  ⟇ p_166  ⟇ p_166 ⟇ ▩) {
    have t73_perm : π ((⟇_to_∨_rw ((¬ ((((f 0) = 10) ∧ (¬ (((f 0) ≥ 5))))))
             ⟇ (¬ (((f 0) ≥ 5)))
            ⟇ ▩)) = (⟇_to_∨_rw ((¬ (((f 0) ≥ 5)))  ⟇ (¬ ((((f 0) = 10) ∧ (¬ (((f 0) ≥ 5)))))) ⟇ ▩))) {
        apply (cl_perm_correct ((¬ ((((f 0) = 10) ∧ (¬ (((f 0) ≥ 5))))))  ⟇ (¬ (((f 0) ≥ 5))) ⟇ ▩) ((¬ (((f 0) ≥ 5)))
             ⟇ (¬ ((((f 0) = 10) ∧ (¬ (((f 0) ≥ 5))))))
            ⟇ ▩));
        apply ⊤ᵢ;
    };
    apply resolutionᵣ _ _ _ t71_t72 (subst_equiv_clause ((¬ ((((f 0) = 10) ∧ (¬ (((f 0) ≥ 5))))))
         ⟇ (¬ (((f 0) ≥ 5)))
        ⟇ ▩) ((¬ (((f 0) ≥ 5)))  ⟇ (¬ ((((f 0) = 10) ∧ (¬ (((f 0) ≥ 5)))))) ⟇ ▩) t73_perm t73);
};
refine t71_t72_t73;
end;

opaque symbol t75 : π̇ (p_166  ⟇ p_166  ⟇ ⊥ ⟇ ▩) ≔ 
begin
admit;
end;

opaque symbol t76 : π̇ (p_166  ⟇ ⊥ ⟇ ▩) ≔ 
begin
admit;
end;

opaque symbol t77 : π̇ (p_131  ⟇ ⊥ ⟇ ▩) ≔ 
begin
have t70_t76 : π̇ (p_131  ⟇ ⊥ ⟇ ▩) {
    have t70_perm : π ((⟇_to_∨_rw ((((((f 0) = 10) ∧ (¬ (((f 0) ≥ 5))))) ⇒ (⊥))
             ⟇ (((f 0) = 10) ∧ (¬ (((f 0) ≥ 5))))
            ⟇ ▩)) = (⟇_to_∨_rw ((((f 0) = 10) ∧ (¬ (((f 0) ≥ 5))))
             ⟇ (((((f 0) = 10) ∧ (¬ (((f 0) ≥ 5))))) ⇒ (⊥))
            ⟇ ▩))) {
        apply (cl_perm_correct ((((((f 0) = 10) ∧ (¬ (((f 0) ≥ 5))))) ⇒ (⊥))
             ⟇ (((f 0) = 10) ∧ (¬ (((f 0) ≥ 5))))
            ⟇ ▩) ((((f 0) = 10) ∧ (¬ (((f 0) ≥ 5))))  ⟇ (((((f 0) = 10) ∧ (¬ (((f 0) ≥ 5))))) ⇒ (⊥)) ⟇ ▩));
        apply ⊤ᵢ;
    };
    apply resolutionₗ _ _ _ (subst_equiv_clause ((((((f 0) = 10) ∧ (¬ (((f 0) ≥ 5))))) ⇒ (⊥))
         ⟇ (((f 0) = 10) ∧ (¬ (((f 0) ≥ 5))))
        ⟇ ▩) ((((f 0) = 10) ∧ (¬ (((f 0) ≥ 5))))  ⟇ (((((f 0) = 10) ∧ (¬ (((f 0) ≥ 5))))) ⇒ (⊥)) ⟇ ▩) t70_perm t70) t76;
};
refine t70_t76;
end;

opaque symbol t78 : π̇ (p_131  ⟇ p_99 ⟇ ▩) ≔ 
begin
apply implies_neg2;
end;

opaque symbol t79 : π̇ (p_131  ⟇ p_131 ⟇ ▩) ≔ 
begin
have t77_t78 : π̇ (p_131  ⟇ p_131 ⟇ ▩) {
    have t77_perm : π ((⟇_to_∨_rw ((((((f 0) = 10) ∧ (¬ (((f 0) ≥ 5))))) ⇒ (⊥))  ⟇ ⊥ ⟇ ▩)) = (⟇_to_∨_rw (⊥
             ⟇ (((((f 0) = 10) ∧ (¬ (((f 0) ≥ 5))))) ⇒ (⊥))
            ⟇ ▩))) {
        apply (cl_perm_correct ((((((f 0) = 10) ∧ (¬ (((f 0) ≥ 5))))) ⇒ (⊥))  ⟇ ⊥ ⟇ ▩) (⊥
             ⟇ (((((f 0) = 10) ∧ (¬ (((f 0) ≥ 5))))) ⇒ (⊥))
            ⟇ ▩));
        apply ⊤ᵢ;
    };
    have t78_perm : π ((⟇_to_∨_rw ((((((f 0) = 10) ∧ (¬ (((f 0) ≥ 5))))) ⇒ (⊥))  ⟇ (¬ (⊥)) ⟇ ▩)) = (⟇_to_∨_rw ((¬ (⊥))
             ⟇ (((((f 0) = 10) ∧ (¬ (((f 0) ≥ 5))))) ⇒ (⊥))
            ⟇ ▩))) {
        apply (cl_perm_correct ((((((f 0) = 10) ∧ (¬ (((f 0) ≥ 5))))) ⇒ (⊥))  ⟇ (¬ (⊥)) ⟇ ▩) ((¬ (⊥))
             ⟇ (((((f 0) = 10) ∧ (¬ (((f 0) ≥ 5))))) ⇒ (⊥))
            ⟇ ▩));
        apply ⊤ᵢ;
    };
    apply resolutionₗ _ _ _ (subst_equiv_clause ((((((f 0) = 10) ∧ (¬ (((f 0) ≥ 5))))) ⇒ (⊥))  ⟇ ⊥ ⟇ ▩) (⊥
         ⟇ (((((f 0) = 10) ∧ (¬ (((f 0) ≥ 5))))) ⇒ (⊥))
        ⟇ ▩) t77_perm t77) (subst_equiv_clause ((((((f 0) = 10) ∧ (¬ (((f 0) ≥ 5))))) ⇒ (⊥))  ⟇ (¬ (⊥)) ⟇ ▩) ((¬ (⊥))
         ⟇ (((((f 0) = 10) ∧ (¬ (((f 0) ≥ 5))))) ⇒ (⊥))
        ⟇ ▩) t78_perm t78);
};
refine t77_t78;
end;

opaque symbol t80 : π̇ (p_131 ⟇ ▩) ≔ 
begin
admit;
end;

opaque symbol t81 : π̇ ((p_131 = p_166) ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
simplify;
eval implies_simplify ;
end;

opaque symbol t82 : π̇ ((¬ (p_131))  ⟇ p_166 ⟇ ▩) ≔ 
begin
apply equiv1 t81;
end;

opaque symbol t83 : π̇ (p_166 ⟇ ▩) ≔ 
begin
have t80_t82 : π̇ (p_166 ⟇ ▩) {
    apply resolutionₗ _ _ _ t80 t82;
};
refine t80_t82;
end;

opaque symbol t84 : π̇ (p_114  ⟇ p_115 ⟇ ▩) ≔ 
begin
apply not_and (π̇ₗ t83);
reflexivity;
end;

opaque symbol t85 : π̇ (p_113  ⟇ (¬ (p_114)) ⟇ ▩) ≔ 
begin
apply or_neg;
reflexivity;
end;

opaque symbol t86 : π̇ (p_113  ⟇ (¬ (p_115)) ⟇ ▩) ≔ 
begin
apply or_neg;
reflexivity;
end;

opaque symbol t87 : π̇ (p_113  ⟇ p_113 ⟇ ▩) ≔ 
begin
have t84_t85 : π̇ (p_115  ⟇ p_113 ⟇ ▩) {
    have t85_perm : π ((⟇_to_∨_rw (((¬ (((f 0) = 10))) ∨ (¬ ((¬ (((f 0) ≥ 5))))))
             ⟇ (¬ ((¬ (((f 0) = 10)))))
            ⟇ ▩)) = (⟇_to_∨_rw ((¬ ((¬ (((f 0) = 10)))))  ⟇ ((¬ (((f 0) = 10))) ∨ (¬ ((¬ (((f 0) ≥ 5)))))) ⟇ ▩))) {
        apply (cl_perm_correct (((¬ (((f 0) = 10))) ∨ (¬ ((¬ (((f 0) ≥ 5))))))
             ⟇ (¬ ((¬ (((f 0) = 10)))))
            ⟇ ▩) ((¬ ((¬ (((f 0) = 10)))))  ⟇ ((¬ (((f 0) = 10))) ∨ (¬ ((¬ (((f 0) ≥ 5)))))) ⟇ ▩));
        apply ⊤ᵢ;
    };
    apply resolutionₗ _ _ _ t84 (subst_equiv_clause (((¬ (((f 0) = 10))) ∨ (¬ ((¬ (((f 0) ≥ 5))))))
         ⟇ (¬ ((¬ (((f 0) = 10)))))
        ⟇ ▩) ((¬ ((¬ (((f 0) = 10)))))  ⟇ ((¬ (((f 0) = 10))) ∨ (¬ ((¬ (((f 0) ≥ 5)))))) ⟇ ▩) t85_perm t85);
};
have t84_t85_t86 : π̇ (p_113  ⟇ p_113 ⟇ ▩) {
    have t86_perm : π ((⟇_to_∨_rw (((¬ (((f 0) = 10))) ∨ (¬ ((¬ (((f 0) ≥ 5))))))
             ⟇ (¬ ((¬ ((¬ (((f 0) ≥ 5)))))))
            ⟇ ▩)) = (⟇_to_∨_rw ((¬ ((¬ ((¬ (((f 0) ≥ 5)))))))  ⟇ ((¬ (((f 0) = 10))) ∨ (¬ ((¬ (((f 0) ≥ 5)))))) ⟇ ▩))) {
        apply (cl_perm_correct (((¬ (((f 0) = 10))) ∨ (¬ ((¬ (((f 0) ≥ 5))))))
             ⟇ (¬ ((¬ ((¬ (((f 0) ≥ 5)))))))
            ⟇ ▩) ((¬ ((¬ ((¬ (((f 0) ≥ 5)))))))  ⟇ ((¬ (((f 0) = 10))) ∨ (¬ ((¬ (((f 0) ≥ 5)))))) ⟇ ▩));
        apply ⊤ᵢ;
    };
    apply resolutionₗ _ _ _ t84_t85 (subst_equiv_clause (((¬ (((f 0) = 10))) ∨ (¬ ((¬ (((f 0) ≥ 5))))))
         ⟇ (¬ ((¬ ((¬ (((f 0) ≥ 5)))))))
        ⟇ ▩) ((¬ ((¬ ((¬ (((f 0) ≥ 5)))))))  ⟇ ((¬ (((f 0) = 10))) ∨ (¬ ((¬ (((f 0) ≥ 5)))))) ⟇ ▩) t86_perm t86);
};
refine t84_t85_t86;
end;

opaque symbol t88 : π̇ (p_113 ⟇ ▩) ≔ 
begin
admit;
end;

opaque symbol t89 : π̇ (p_118 ⟇ ▩) ≔ 
begin
have t57_t69 : π̇ ((¬ (p_113))  ⟇ p_118 ⟇ ▩) {
    apply resolutionᵣ _ _ _ t57 t69;
};
have t57_t69_t88 : π̇ (p_118 ⟇ ▩) {
    apply resolutionᵣ _ _ _ t57_t69 t88;
};
refine t57_t69_t88;
end;

opaque symbol t90 : π̇ (p_114  ⟇ p_117 ⟇ ▩) ≔ 
begin
admit;
end;

opaque symbol t91 : π̇ (p_163 ⟇ ▩) ≔ 
begin
apply ∨ᵢ₁;
apply imply_to_or;
assume H;
refine (H 0);
end;

opaque symbol t92 : π̇ (p_31  ⟇ p_116 ⟇ ▩) ≔ 
begin
admit;
end;

opaque symbol t93 : π̇ (p_116 ⟇ ▩) ≔ 
begin
have t92_t54 : π̇ (p_116 ⟇ ▩) {
    apply resolutionᵣ _ _ _ t92 t54;
};
refine t92_t54;
end;

opaque symbol t94 : π̇ (p_114 ⟇ ▩) ≔ 
begin
have t90_t93 : π̇ (p_114 ⟇ ▩) {
    have t90_perm : π ((⟇_to_∨_rw ((¬ (((f 0) = 10)))  ⟇ ((f 0) ≥ 5) ⟇ ▩)) = (⟇_to_∨_rw (((f 0) ≥ 5)
             ⟇ (¬ (((f 0) = 10)))
            ⟇ ▩))) {
        apply (cl_perm_correct ((¬ (((f 0) = 10)))  ⟇ ((f 0) ≥ 5) ⟇ ▩) (((f 0) ≥ 5)  ⟇ (¬ (((f 0) = 10))) ⟇ ▩));
        apply ⊤ᵢ;
    };
    apply resolutionₗ _ _ _ (subst_equiv_clause ((¬ (((f 0) = 10)))  ⟇ ((f 0) ≥ 5) ⟇ ▩) (((f 0) ≥ 5)
         ⟇ (¬ (((f 0) = 10)))
        ⟇ ▩) t90_perm t90) t93;
};
refine t90_t93;
end;

opaque symbol t95 : π̇ (p_4 ⟇ ▩) ≔ 
begin
have t56_t94 : π̇ (p_4 ⟇ ▩) {
    apply resolutionₗ _ _ _ t56 t94;
};
refine t56_t94;
end;

opaque symbol t96 : π̇ ▩ ≔ 
begin
have t46_t55 : π̇ (p_10 ⟇ ▩) {
    have t46_perm : π ((⟇_to_∨_rw ((¬ (((f 5) = 12)))  ⟇ ((f 5) ≥ 5) ⟇ ▩)) = (⟇_to_∨_rw (((f 5) ≥ 5)
             ⟇ (¬ (((f 5) = 12)))
            ⟇ ▩))) {
        apply (cl_perm_correct ((¬ (((f 5) = 12)))  ⟇ ((f 5) ≥ 5) ⟇ ▩) (((f 5) ≥ 5)  ⟇ (¬ (((f 5) = 12))) ⟇ ▩));
        apply ⊤ᵢ;
    };
    apply resolutionₗ _ _ _ (subst_equiv_clause ((¬ (((f 5) = 12)))  ⟇ ((f 5) ≥ 5) ⟇ ▩) (((f 5) ≥ 5)
         ⟇ (¬ (((f 5) = 12)))
        ⟇ ▩) t46_perm t46) t55;
};
have t46_t55_t95 : π̇ ▩ {
    apply resolutionᵣ _ _ _ t46_t55 t95;
};
refine t46_t55_t95;
end;
