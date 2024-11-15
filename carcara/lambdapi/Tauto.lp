require open Stdlib.Prop;
require open Stdlib.FOL;
require open Stdlib.Eq;
require open Stdlib.Nat;
require Stdlib.Bool;
require open Stdlib.Set;
// require open lambdapi.Classic;
// require open lambdapi.Alethe;
require open Stdlib.List;

inductive prop: TYPE ≔
|pTrue: prop
| pFalse: prop
| pAnd: prop → prop → prop
| pOr: prop → prop → prop
| pImpl: prop → prop → prop
//| pNot: prop → prop
| pOther: ℕ → prop
;

symbol propS: Set;

rule τ propS ↪ prop;


symbol o: Set;
rule τ o ↪ Prop;

symbol not_found: Prop; // Just a simple opaque definition to represent an error message.

// A denotation function converts our syntax into a semantic value
// The σ is the context which contains the mapping from variables to Props.
symbol propD (σ: 𝕃 o) (p: prop): Prop;
rule propD _ pTrue ↪ ⊤
with propD _ pFalse ↪ ⊥
with propD $ctx (pAnd $x $y) ↪  (propD $ctx $x) ∧ (propD $ctx $y)
with propD $ctx (pOr $x $y) ↪  (propD $ctx $x) ∨ (propD $ctx $y)
with propD $ctx (pImpl $x $y) ↪  (propD $ctx $x) ⇒ (propD $ctx $y)
//with propD $ctx (pNot $x) ↪  ¬ (propD $ctx $x)
with propD $ctx (pOther $i) ↪ nth not_found $ctx $i;

private symbol a: Prop;
private symbol b: Prop;
private symbol f: Prop → Prop;

type (a ⸬ f b ⸬ b ⸬ □);

private symbol ctx ≔ (a ⸬ f b ⸬ b ⸬ □);

assert ⊢ propD ctx (pOther 0) ≡ a;
assert ⊢ propD ctx (pOther 1) ≡ f b;
assert ⊢ propD ctx (pOther 2) ≡ b;
assert ⊢ propD ctx (pOther 3) ≡ not_found;

open Stdlib.Bool;

//FIXME: remove sequential by covering all the case
sequential symbol prop_eq (l r: prop): τ bool;
rule prop_eq pTrue pTrue ↪ true
with prop_eq pFalse pFalse ↪ true
with prop_eq (pAnd $a $b) (pAnd $c $d) ↪ (prop_eq $a $c) and (prop_eq $b $d)
with prop_eq (pOr $a $b) (pOr $c $d) ↪ (prop_eq $a $c) and (prop_eq $b $d)
with prop_eq (pImpl $a $b) (pImpl $c $d) ↪ (prop_eq $a $c) and (prop_eq $b $d)
with prop_eq (pOther $i) (pOther $j) ↪ (eqn $i $j)
with prop_eq $x $y ↪ false;

assert ⊢ prop_eq (pOr (pOther 0) (pOther 1)) (pOr (pOther 0) (pOther 1)) ≡ true;
assert ⊢ prop_eq (pOr (pOther 0) (pOther 1)) (pOr (pOther 1) (pOther 0)) ≡ false;

// Decidable equality on terms
opaque symbol prop_eq_sound (a b: prop): π (istrue (prop_eq a b)) → π (a = b)  ≔
begin
    induction
    { induction { reflexivity } { assume H; apply ⊥ₑ H; } { assume b' H c' H2 H3; apply ⊥ₑ H3 }  { assume b' H c' H2 H3; apply ⊥ₑ H3 } { assume b' H c' H2 H3; apply ⊥ₑ H3 }  { assume idx H;  apply ⊥ₑ H } } 
    { induction { assume H; apply ⊥ₑ H; } { reflexivity }  { assume b' H c' H2 H3; apply ⊥ₑ H3 }  { assume b' H c' H2 H3; apply ⊥ₑ H3 } { assume b' H c' H2 H3; apply ⊥ₑ H3 }  { assume idx H;  apply ⊥ₑ H } } 
    {
        assume a' H b' H2;
        //assume c Hc;
        induction
        {assume H3; apply ⊥ₑ H3; }
        {assume H3; apply ⊥ₑ H3; }
        { assume c' H' d' H2' H3; apply ⊥ₑ H3; }
        { assume c' H' d' H2';  assume H3; apply ⊥ₑ H3; }
        { assume c' H' d' H2';  assume H3; apply ⊥ₑ H3; }
        //{ assume x H3 H4; apply ⊥ₑ H4 }
        { assume i;  assume H3; apply ⊥ₑ H3; }
    }
    {
        assume a' H b' H2;
        induction
        {assume H3; apply ⊥ₑ H3; }
        {assume H3; apply ⊥ₑ H3; }
        { assume c' H' d' H2';  assume H3; apply ⊥ₑ H3; }
        { assume c' H' d' H2' H3; apply ⊥ₑ H3 }
        { assume c' H' d' H2';  assume H3; apply ⊥ₑ H3; }
        //{ assume x H3 H4; apply ⊥ₑ H4 }
        { assume i;  assume H3; apply ⊥ₑ H3; }
    }
    {
        assume a' H b' H2;
        induction
        {assume H3; apply ⊥ₑ H3; }
        {assume H3; apply ⊥ₑ H3; }
        { assume c' H' d' H2';  assume H3; apply ⊥ₑ H3; }
        { assume c' H' d' H2';  assume H3; apply ⊥ₑ H3; }
        { assume c' H' d' H2' H3; apply ⊥ₑ H3 }
        //{ assume x H3 H4; apply ⊥ₑ H4 }
        { assume i;  assume H3; apply ⊥ₑ H3; }
    }
    // {
    //     assume x H;
    //     induction
    //     { assume H2; apply ⊥ₑ H2 }
    //     { assume H2; apply ⊥ₑ H2 }
    //     { assume c' H' d' H2';  assume H3; apply ⊥ₑ H3; }
    //     { assume c' H' d' H2';  assume H3; apply ⊥ₑ H3; }
    //     { assume c' H' d' H2' H3; apply ⊥ₑ H3 }
    //     { assume x' H3 H4; apply ⊥ₑ H4  }
    //     { assume x' H2; apply ⊥ₑ H2 }
    // }
    {
        assume i;
        induction
        { assume H; apply ⊥ₑ H;  }
        { assume H; apply ⊥ₑ H;  }
        { assume x; assume H x' H2 Hbot; apply ⊥ₑ Hbot; }
        { assume x; assume H x' H2 Hbot; apply ⊥ₑ Hbot; }
        { assume x; assume H x' H2 Hbot; apply ⊥ₑ Hbot; }
        //{ assume x H3 H4; apply ⊥ₑ H4 }
        {
            assume j;
            assume H;
            rewrite (eqn_correct i j H);
            reflexivity  
        }
    }
end;

symbol knows (p: prop) (c: 𝕃 propS): 𝔹 ≔ ∈ prop_eq p c;

sequential symbol learn (p: prop) (c: 𝕃 propS) : 𝕃 propS;
rule learn pTrue $c ↪ $c
with learn pFalse $c ↪ pFalse ⸬ □
with learn (pAnd $l $r) $c ↪ learn $l (learn $r $c)
with learn $p $c ↪ $p ⸬ $c; //HACK: for simplicity

symbol provable (goal: prop) (known: 𝕃 propS) : 𝔹;
rule provable pTrue _ ↪ true
with provable pFalse $known ↪ knows pFalse $known
// with provable (pNot pTrue) $known ↪ false
// with provable (pNot pFalse) $known ↪ true
// with provable (pNot (pAnd $l $r)) $known ↪ not ((provable $l $known) and (provable $r $known))
// with provable (pNot (pOr $l $r)) $known ↪ not (provable $l $known) or (provable $r $known)
// with provable (pNot (pImpl $l $r)) $known ↪ not (provable $r (learn $l $known))
// with provable (pNot (pNot $x)) $known ↪ not (not (provable $x $known))
// with provable (pNot (pOther $x)) $known ↪ not (provable (pOther $x) $known)
with provable (pAnd $l $r) $known ↪ (provable $l $known) and (provable $r $known)
with provable (pOr $l $r) $known ↪ (provable $l $known) or (provable $r $known)
with provable (pImpl $l $r) $known ↪ provable $r (learn $l $known)
with provable (pOther $i) $known ↪ (knows (pOther $i) $known) or (knows pFalse $known);

assertnot ⊢ provable (pAnd (pOther 0) pFalse) ((pOther 0) ⸬ □) ≡ true;
assert ⊢ provable (pAnd (pOther 0) pTrue) ((pOther 0) ⸬ □) ≡ true;

symbol foldr [a b: Set] : (τ a → τ b → τ b) → τ b → 𝕃 a → τ b;
rule foldr $f $z □ ↪ $z
with foldr $f $z ($x ⸬ $xs) ↪ $f $x (foldr $f $z $xs);

symbol All: 𝕃 propS → prop ≔ foldr (pAnd) pTrue;

symbol I: π ⊤;

opaque symbol learn_sound (ctx: 𝕃 o) (p: prop) (c: 𝕃 propS): π (propD ctx (All c)) → π ( propD ctx p) → π ( propD ctx (All (learn p c)))
≔ begin
    assume σ;
    induction
    { assume c; assume H; assume Htop; apply H }
    { assume c; assume H H2; refine ⊥ₑ H2  }
    { assume a IH b IH2 ctx H2 H3;
        apply ∧ᵢ 
        { refine  ∧ₑ₁ H3 } 
        {  apply ∧ᵢ { apply ∧ₑ₂ H3 } { refine H2 } }
    }
    { assume a IH b IH2 ctx H2 H3; 
        apply ∧ᵢ 
        { apply ∨ₑ H3 { assume H0; apply ∨ᵢ₁; refine H0 } { assume H0; apply ∨ᵢ₂; refine H0 }  }
        { refine H2 }
    }
    {
        assume a IH b IH2 ctx H2 H3;
        apply ∧ᵢ 
        { refine H3 }
        { refine H2 }
    }
    // {
    //     simplify;
    //     assume p H H2 H3 HD;
    //     apply ∧ᵢ 
    //     { refine HD }
    //     { refine H3 }
    // }
    {
        assume i Γ H1 H2;
        apply ∧ᵢ { refine H2 } { refine H1 }
    }
end;


opaque symbol knows_sound (σ: 𝕃 o) (c: 𝕃 propS) (p: prop) : π (((knows p c) = true) ⇒ (propD σ (All c)) ⇒  (propD σ p)) ≔
begin 
    assume σ p c;
    admit
    //admit //induction on c
    // Case □ we have knows p □ = true that leads to a contradiction 
    // Case x::xs
    // Assume knows p (x::xs) = true and propD σ (All (x::xs)) show propD σ p
    // By using List.in_cons we have  beq x y or ∈ beq x l)
end;

opaque symbol andb_true_iff [p q] : π((p and q) = true) → π(p = true ∧ q = true) ≔
begin
  induction
  { induction
    { assume h; apply ∧ᵢ { reflexivity } { reflexivity } }
    { assume h; apply ⊥ₑ (false≠true  h); }
  }
  {  assume q h;  apply ⊥ₑ (false≠true  h) }
end;

opaque symbol not_and_true_iff [p q] : π(not (p and q) = true) → π(not p = true ∨ not q = true) ≔
begin
    admit
end;

opaque symbol not_true_iff [p] : π(not p = true) → π(p = false) ≔
begin
    admit
end;

opaque symbol or_true_iff [p q] : π((p or q) = true) → π(p = true ∨ q = true) ≔
begin
    induction
    { assume p H; apply ∨ᵢ₁; reflexivity }
    { assume q h;  apply ∨ᵢ₂; apply h }
end;

// Main theorem
opaque symbol provable_sound: Π (goal: prop), Π  (hyps: 𝕃 propS),
    π (provable goal hyps = true) → 
    Π (ctx: 𝕃 o), π (propD ctx (All hyps)) →
    π (propD ctx goal) ≔
begin
    induction
    { assume ctx H σ H2; apply I }
    { assume ctx H σ H2; apply (knows_sound σ ctx pFalse H);  apply H2 }
    { assume a IH1 b IH2 ctx' H σ H2;
        have G: π ((provable a ctx' = true) ∧ (provable b ctx' = true) ) {
            refine (@andb_true_iff _ _ H); 
        };
        apply ∧ᵢ
        { refine (IH1 ctx' (∧ₑ₁ G)) σ H2 }
        { refine (IH2 ctx' (∧ₑ₂ G)) σ H2 };
    }
    {
        assume a IH1 b IH2 ctx' H σ H2;
        have G: π ((provable a ctx' = true) ∨ (provable b ctx' = true) ) {
            refine (@or_true_iff _ _ H); 
        };
        apply ∨ₑ G
        {  assume Ga; apply ∨ᵢ₁; refine (IH1 ctx' Ga σ H2) }
        { assume Gb; apply ∨ᵢ₂; refine (IH2 ctx' Gb σ H2) };
    }
    {
        assume a IH1 b IH2 ctx H σ H2 Ha;
        apply (IH2 (a ⸬ ctx) H σ);
        apply ∧ᵢ
        { apply Ha }
        { apply H2 }
    }
    //{
        //admit
        // induction
        // { simplify; assume IH hyps Hrefl σ Hσ H1; apply ⊥ₑ (false≠true Hrefl) }
        // { simplify; assume IH hyps Hrefl σ Hσ H1; refine H1 }
        // {
        //     simplify; assume a IHa b IHb H ctx Hrefl σ H3 Haandb;
        //     have G: π (not (provable a ctx) = true ∨ not (provable b ctx) = true)
        //     {
        //         refine (@not_and_true_iff (provable a ctx) (provable b ctx) Hrefl)
        //     };
        //     apply ∨ₑ G
        //     {
        //         simplify;
        //         assume Ha;
        //         have G2: π (provable a ctx = false) {
        //             apply not_true_iff Ha
        //         };
        //         have G3: π ((provable a ctx and provable b ctx) = true) {

        //         };
        //     }
        //     { }
        // }
        // {admit}
        // {admit}
        // {admit}
        // {admit}       
    //}
    {
       assume i hyps IH σ H2;
       have G: π ((∈ prop_eq (pOther i) hyps = true)  ∨ (∈ prop_eq pFalse hyps = true) ) {
        refine (@or_true_iff _ _ IH); 
       };
       apply ∨ₑ G
       { assume Gl; apply (knows_sound σ hyps (pOther i) Gl H2); }
       { assume Gr; refine (@⊥ₑ (nth not_found σ i) (knows_sound σ hyps (pFalse) Gr H2))  }
    }
end;

opaque symbol provable_apply:  Π (goal: prop), π (provable goal □ = true) → Π (σ: 𝕃 o), π (propD σ goal) ≔
begin
    assume goal H σ;
    apply provable_sound goal □ H σ; apply I
end;

//HACK: Refactor
sequential symbol peq: Prop → Prop → 𝔹;
rule peq $x $x ↪ true
with peq $x $y ↪ false;

sequential symbol allVars : τ (list o) → Prop →  τ (list o);
rule allVars $σ ⊤ ↪ $σ
with allVars $σ ⊥ ↪ $σ
with allVars $σ (¬ $x) ↪ (allVars $σ $x)
with allVars $σ ($l ∧ $r) ↪
    let σ' ≔ (allVars $σ $l) in 
    (allVars σ' $r)
with allVars $σ ($l ∨ $r) ↪
    let σ' ≔ (allVars $σ $l) in 
    (allVars σ' $r)
with allVars $σ ($l ⇒ $r) ↪
    let σ' ≔ (allVars $σ $l) in 
    (allVars σ' $r)
with allVars $σ $t ↪ if (∈ (peq) $t $σ) $σ ($t ⸬ $σ)
;

assert ⊢ (allVars □ (a ∧ (¬ b ) ∧ ⊤ ∧ ⊥ ∧ a ∨ b)) ≡ b ⸬ a ⸬ □;

sequential symbol reifybis : 𝕃 o  →  Prop → prop;
rule reifybis $σ ⊤ ↪ pTrue
with reifybis $σ ⊥ ↪ pFalse
with reifybis $σ ($a ∧ $b) ↪ if (∈ (peq) $a $σ)
                                // then
                                (pAnd (pOther (index (peq) $a $σ)) (reifybis $σ $b))
                                // else
                                (pAnd (reifybis $σ $a) (reifybis $σ $b))
with reifybis $σ ($a ∨ $b) ↪ if (∈ (peq) $a $σ)
                                // then
                                (pOr (pOther (index (peq) $a $σ)) (reifybis $σ $b))
                                // else
                                (pOr (reifybis $σ $a) (reifybis $σ $b))
with reifybis $σ ($a ⇒ $b) ↪ if (∈ (peq) $a $σ)
                                // then
                                (pImpl (pOther (index (peq) $a $σ)) (reifybis $σ $b))
                                // else
                                (pImpl (reifybis $σ $a) (reifybis $σ $b))
with reifybis $σ $t  ↪  pOther (index (peq) $t $σ)
;

symbol reify: Prop →  τ propS ≔ λ p, reifybis (allVars □ p) p;

assert ⊢ allVars □ ((a ∨ (f a)) ∧ (a ⇒ b)) ≡ b ⸬ (f a) ⸬ a ⸬ □;

assert ⊢ reify (⊤ ∧ (⊤ ∨ ⊥)) ≡ pAnd pTrue (pOr pTrue pFalse);
assert a b f ⊢ reify ((a ∨ (f a)) ∧ (a ⇒ b)) ≡ pAnd (pOr (pOther 2) (pOther 1)) (pImpl (pOther 2) (pOther 0));

symbol reify_coe: Prop →  τ propS;
rule reify_coe $p ↪ reifybis (allVars □ $p) $p;

coerce_rule coerce Prop (τ propS) $p ↪ reify_coe $p;

symbol inj_propD p: π (propD (allVars □ p) (reify p) = p) ≔ begin reflexivity end;    


//NOTE: We do not have the tactic change in Lambdapi
constant symbol apply_reify [goal: Prop] : π (propD (allVars □ goal) (reify goal)) → π goal;


opaque symbol tauto : Π (goal: Prop), π (provable (reify goal) □ = true) →  π goal ≔
begin admit end;

symbol example1 : π (⊤ ∧ ⊤ ∨ ⊥) ≔
begin
    rewrite left inj_propD;
    type (provable_apply (reify ((⊤ ∧ ⊤) ∨ ⊥)) (eq_refl true) □);
    apply provable_apply (reify ((⊤ ∧ ⊤) ∨ ⊥)) (eq_refl true)  □ ; 
end;

 
symbol example2 p q : π (p ⇒ p ∧ ⊤ ∧ p ∨ q) ≔
begin
    assume p q;
    rewrite left inj_propD;
    apply tauto;
    reflexivity
end;

symbol example3 p : π (p ⇒ (p ∧ ⊥)) ≔
begin
    assume p;
    rewrite left inj_propD;
    apply tauto;
    admit
end;
