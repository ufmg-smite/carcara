require open lambdapi.Zgcd;

symbol ℚ : TYPE;
symbol rat: Set;
rule τ rat ↪ ℚ;

// The symbol `rat` denotes any fraction while `/` denotes irreducible fractions.
injective symbol frac : ℤ → ℤ → ℚ; // raw fraction constructor

symbol ind_Rat : Π p0: (ℚ → Prop), (Π x: ℤ, Π y: ℤ, π (p0 (frac x y))) → Π x: ℚ, π (p0 x);
rule ind_Rat $p0 $frac (frac $x $y) ↪ $frac $x $y;


injective symbol / : ℤ → ℤ → ℚ; notation / infix right 30;

rule frac $x $y ↪ (sign $y * Z_red_Stein $x $y) / (sign $y * Z_red_Stein $y $x);


symbol ᵣ+  : ℚ → ℚ → ℚ; notation ᵣ+ infix right 20;
symbol ᵣ- : ℚ → ℚ → ℚ; notation ᵣ- infix left 20;
symbol *ᵣ  : ℚ → ℚ → ℚ; notation *ᵣ infix right 22;
symbol —ᵣ : ℚ → ℚ; notation —ᵣ prefix 24;

rule ($x / $y) ᵣ+ ($u / $v) ↪ frac (($x * $v) + ($u * $y)) ($y * $v);
rule ($x / $y) *ᵣ ($u / $v) ↪ frac ( $x * $u ) ( $y * $v );

rule —ᵣ (Zpos $x / Zpos $y) ↪ (Zneg $x / Zpos $y)
with —ᵣ (Zneg $x / Zpos $y) ↪ (Zpos $x / Zpos $y)
with —ᵣ (0 / $d) ↪ (0 / $d);

symbol inj_z : ℤ → ℚ;
rule inj_z $x ↪ $x / 1;

coerce_rule coerce ℤ ℚ $x ↪ inj_z $x;

compute frac 152 12;

rule _ / 0 ↪ 0 / 1;
rule 0 / Zpos (I _) ↪ 0 / 1
with 0 / Zpos (O _) ↪ 0 / 1
with 0 / Zneg (I _) ↪ 0 / 1
with 0 / Zneg (O _) ↪ 0 / 1
with 0 / Zneg H ↪ 0 / 1;

rule (Zneg $x) / (Zneg $y) ↪ Zpos $x / Zpos $y;
rule (Zpos $x) / (Zneg $y) ↪ Zneg $x / Zpos $y;

symbol 0⫽1 : ℚ ≔  Z0 / 1;
symbol 1⫽1 : ℚ ≔  1 / 1;


opaque symbol sign_case x : π (sign x = 1 ∨ sign x = — 1) ≔
begin
    induction
    {apply ∨ᵢ₁;  reflexivity}
    {assume p; apply ∨ᵢ₁;  reflexivity}
    {assume p; apply ∨ᵢ₂;  reflexivity}
end;

opaque symbol sign_inj x : π (sign (sign x) = sign x) ≔
begin
    induction
    {reflexivity}
    {assume p; reflexivity}
    {assume p; reflexivity}
end;

opaque symbol frac_neg n d : π (frac (— n) (— d) = frac n d) ≔
begin
    simplify;
    induction
    {
        induction
        {reflexivity}
        {assume p; reflexivity}
        {assume p; reflexivity}
    }
    {
        assume p;
        induction
        {reflexivity}
        {assume q; reflexivity}
        {assume q; reflexivity}
    }
    {
        assume p;
        induction
        {reflexivity}
        {assume q; reflexivity}
        {assume q; reflexivity}
    }
end;

opaque symbol neg_neg_cancel_div n d : π (((— n) / (— d)) = (n / d)) ≔
begin
    induction
    {
        induction
        {reflexivity}
        {
            simplify;
            induction
            {assume p ih; simplify; reflexivity }
            {assume p ih; simplify; reflexivity }
            {reflexivity}
        }
        {
            simplify;
            induction
            {assume p ih; simplify; reflexivity }
            {assume p ih; simplify; reflexivity }
            {reflexivity}
        }
    }
    {
        assume p;
        simplify —;
        induction
        {
            reflexivity
        }
        {
            assume q;
            simplify —;
            reflexivity
        }
        {
            assume q;
            simplify;
            reflexivity
        }
    }
    {
         assume p;
        simplify —;
        induction
        {
            reflexivity
        }
        {
            assume q;
            simplify —;
            reflexivity
        }
        {
            assume q;
            simplify;
            reflexivity
        }
    }
end;

opaque symbol frac_0_num d: π (frac 0 d = 0 / 1) ≔
begin
    induction
    {reflexivity}
    {reflexivity}
    {reflexivity}
end;

opaque symbol div_0_num d: π (0 / d = 0 / 1) ≔
begin
   simplify;
    //assume d;
    induction
    {reflexivity}
    {induction {reflexivity} {reflexivity} {reflexivity}}
    {induction {reflexivity} {reflexivity} {reflexivity}}
end;

opaque symbol frac_0_den n: π (frac n 0 = 0 / 1) ≔
begin
    induction
    {reflexivity}
    {reflexivity;}
    {reflexivity}
end;

symbol 0⫽n_is_0⫽1  n : π (0 / n = 0 / 1) ≔
begin
    induction
    {reflexivity}
    {induction {reflexivity} {reflexivity} {reflexivity}}
    {induction {reflexivity} {reflexivity} { reflexivity }} 
end;

symbol *ᵣ_com_div n1 d1 n2 d2 :  π ((n1 / d1) *ᵣ (n2 / d2) = (n2 / d2) *ᵣ  (n1 / d1) ) ≔
begin
assume n1 d1 n2 d2;
simplify *ᵣ;
refine @feq2 int int rat (frac) (n1 * n2) (n2 * n1)  _ (d1 * d2) (d2 * d1)  _ 
{ rewrite *_com; reflexivity }
{ rewrite *_com; reflexivity }
end;

symbol ᵣ+_com_div n1 d1 n2 d2 :  π ((n1 / d1) ᵣ+ (n2 / d2) = (n2 / d2) ᵣ+  (n1 / d1) ) ≔
begin
assume n1 d1 n2 d2;
simplify ᵣ+;
apply @feq2 int int rat (frac) ((n1 * d2) + (n2 * d1)) ((n2 * d1) + (n1 * d2))  _ (d1 * d2) (d2 * d1) _ 
{ rewrite +_com; reflexivity }
{ rewrite *_com; reflexivity }
end;

symbol ᵣ+_assoc_div n1 d1 n2 d2 n3 d3 :  π ((n1 / d1 ᵣ+ n2 /d2) ᵣ+ n3 / d3 = (n1 / d1) ᵣ+ n2 / d2 ᵣ+  n3 / d3) ≔
begin
    assume n1 d1 n2 d2 n3 d3;
    simplify ᵣ+;
admitted;


symbol ᵣ+_com x y :  π (x ᵣ+ y = y ᵣ+  x) ≔
begin
    refine ind_Rat (λ u, `∀ y, (u ᵣ+ y) = (y ᵣ+ u)) _;
    assume n1 d1;
    refine ind_Rat (λ u, (frac n1 d1 ᵣ+ u) = (u ᵣ+ frac n1 d1)) _;
    assume n2 d2;
    simplify frac;
    set N1 ≔ (sign d1 * Z_red_Stein n1 d1);
    set D1 ≔ (sign d1 * Z_red_Stein d1 n1);
    set N2 ≔ (sign d2 * Z_red_Stein n2 d2);
    set D2 ≔ (sign d2 * Z_red_Stein d2 n2);
    refine ᵣ+_com_div N1 D1 N2 D2
end;

symbol ᵣ*_com x y :  π (x *ᵣ y = y *ᵣ x) ≔
begin
    refine ind_Rat (λ u, `∀ y, (u *ᵣ y) = (y *ᵣ u)) _;
    assume n1 d1;
    refine ind_Rat (λ u, (frac n1 d1 *ᵣ u) = (u *ᵣ frac n1 d1)) _;
    assume n2 d2;
     simplify frac;
    set N1 ≔ (sign d1 * Z_red_Stein n1 d1);
    set D1 ≔ (sign d1 * Z_red_Stein d1 n1);
    set N2 ≔ (sign d2 * Z_red_Stein n2 d2);
    set D2 ≔ (sign d2 * Z_red_Stein d2 n2);
    refine *ᵣ_com_div N1 D1 N2 D2
end;

opaque symbol *_neutral_l x : π ((1 * x) = x) ≔
begin
  induction {reflexivity} {reflexivity} {reflexivity}
end;

opaque symbol *_cancel_l x : π ((0 * x) = 0) ≔
begin
  induction {reflexivity} {reflexivity} {reflexivity}
end;

opaque symbol div_add_neutral_l n d : π ((0 / 1 ᵣ+ n / d) = n / d) ≔
begin
assume n1 d1;
simplify;
change π ((sign (_1 * d1) * Z_red_Stein (n1 * _1) (_1 * d1)) / (sign (1 * d1) * Z_red_Stein (_1 * d1) (n1 * _1)) = (n1 / d1));
rewrite *_neutral_l;
rewrite *_neutral;
admit
end;

opaque symbol div_add_neutral_r n d : π ((n / d ᵣ+ 0 / 1) = n / d) ≔
begin
admitted;

opaque symbol ᵣ+_neutral_frac_l x : π ((frac 0 1 ᵣ+ x) = x) ≔
begin
    refine ind_Rat (λ u, ((frac 0 _1 ᵣ+ u) = u)) _;
    assume n d;
    simplify;
    set N ≔ (sign d * Z_red_Stein n d);
    set D ≔ (sign d * Z_red_Stein d n);
    change  π (((sign (_1 * D) * Z_red_Stein (N * _1) (_1 * D)) / (sign (_1 * D) * Z_red_Stein (_1 * D) (N * _1))) = (N / D));
    rewrite *_neutral_l;
    rewrite *_neutral;
    have HD: π (sign D = 1 ∨ sign D = — 1) { refine sign_case D };
    have Hd: π (sign d = 1 ∨ sign d = — 1) { refine sign_case d };
    apply ∨ₑ HD
    {
        assume heq; rewrite heq;
        apply ∨ₑ Hd
        {
            assume heq2;
            admit
        }
        {admit}
    }
    {admit}
end;

opaque symbol ᵣ+_neutral_l x : π ((frac 0 1 ᵣ+ x) = x) ≔
begin
admitted;

opaque symbol ᵣ+_neutral_r x : π ((x ᵣ+ frac 0 1) = x) ≔
begin
admitted;

opaque symbol ᵣ+_neutral_div_l x : π ((0 / 1 ᵣ+ x) = x) ≔
begin
    refine ind_Rat (λ u, (((0 / _1) ᵣ+ u) = u)) _;
    assume x y;
    simplify ᵣ+;
    change π (frac ((0 * (sign y * Z_red_Stein y x)) + ((sign y * Z_red_Stein x y) * _1)) (_1 * (sign y * Z_red_Stein y x)) = frac x y);
    rewrite *_neutral;
    rewrite *_neutral_l;
    rewrite *_cancel_l;
    simplify +;
    admit
end;

opaque symbol ᵣ+_neutral_div_r x : π ((x ᵣ+ 0 / 1) = x) ≔
begin
admitted;

opaque symbol ᵣ*_neutral_l x : π ((frac 1 1 *ᵣ x) = x) ≔
begin
admitted;

opaque symbol ᵣ*_neutral_r x : π ((x *ᵣ frac 1 1) = x) ≔
begin
admitted;

opaque symbol ᵣ*_neutral_div_l x : π ((1 / 1 *ᵣ x) = x) ≔
begin
admitted;

opaque symbol ᵣ*_neutral_div_r x : π ((x *ᵣ 1 / 1) = x) ≔
begin
admitted;

symbol nze_frac : π (0 / 1 = frac 0 1) ≔
begin reflexivity end;

opaque symbol ᵣ+_assoc x y z :  π (((x ᵣ+ y) ᵣ+ z) = (x ᵣ+ (y ᵣ+ z))) ≔
begin
    refine ind_Rat (λ u, `∀ y, `∀ z, ((u ᵣ+ y) ᵣ+ z) = (u ᵣ+ (y ᵣ+ z))) _;
    assume n1 d1;
    refine ind_Rat (λ u, `∀ z, ((frac n1 d1 ᵣ+ u) ᵣ+ z) = (frac n1 d1 ᵣ+ (u ᵣ+ z))) _;
    assume n2 d2;
    refine ind_Rat (λ u, (frac n1 d1 ᵣ+ frac n2 d2) ᵣ+ u = frac n1 d1 ᵣ+ (frac n2 d2 ᵣ+ u)) _;
    assume n3 d3;
    simplify frac;
    set N1 ≔ (sign d1 * Z_red_Stein n1 d1);
    set D1 ≔ (sign d1 * Z_red_Stein d1 n1);
    set N2 ≔ (sign d2 * Z_red_Stein n2 d2);
    set D2 ≔ (sign d2 * Z_red_Stein d2 n2);
    set N3 ≔ (sign d3 * Z_red_Stein n3 d3);
    set D3 ≔ (sign d3 * Z_red_Stein d3 n3);
    refine ᵣ+_assoc_div N1 D1 N2 D2 N3 D3
end;


symbol ᵣ≐: ℚ → ℚ → Comp; notation ᵣ≐ infix 10;
rule ($n1 / $d1) ᵣ≐ ($n2 / $d2) ↪ $n1 * $d2 ≐ $n2 * $d1;


opaque symbol distr*ᵣᵣ+ x y z : π(x *ᵣ (y ᵣ+ z) = x *ᵣ y ᵣ+ x *ᵣ z) ≔
begin
admitted;