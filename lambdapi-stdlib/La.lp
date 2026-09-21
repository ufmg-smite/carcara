require open Stdlib.List Stdlib.PropExt;
require open Stdlib.ExtraRules;
require open lambdapi.Rat;

inductive G: TYPE ≔
| Cst: ℚ → G
| Var: ℕ → ℚ → G
;

symbol rec_G : Π p0: (G → Prop), (Π x0: ℚ, π (p0 (Cst x0))) → (Π x0: ℕ, Π x2: ℚ, π (p0 (Var x0 x2))) → Π x: G, π (p0 x);

constant symbol grp : Set;
rule τ grp ↪ G;

// multiplication by a constant

symbol mul: ℚ → 𝕃 grp → 𝕃 grp;

rule mul $k ((Cst $l) ⸬ $xs) ↪ mul ($k *ᵣ $l) $xs
with mul $k ((Var $i $l) ⸬ $xs) ↪ Var $i ($k *ᵣ $l) ⸬ (mul $k $xs)
with mul _ □ ↪ □;

// opposite

symbol opp ≔ mul (—ᵣ 1⫽1);


/* evaluation of an arithmetic expression wrt a list of values for variables
variables with indexes not in the list are raterpreted by 0 */

symbol nth ≔ nth (0⫽1);

symbol val_grp: τ grp →  𝕃 rat → ℚ;
rule val_grp (Cst $k) _ ↪ $k
with val_grp (Var $i $k) $l ↪ ((nth $l $i) *ᵣ $k)
;

symbol val: τ(list grp × list rat) → ℚ;

rule val (□ ‚ _) ↪ 0⫽1
with val (($x ⸬ $xs) ‚ $l) ↪ (val_grp $x $l) ᵣ+ (val ($xs ‚ $l));

symbol va l x ≔ val (x ‚ l);

// some useful type (use inductive instead?)

constant symbol R : TYPE;
constant symbol Index : ℕ → R;
constant symbol New : ℕ → R;

symbol case [a] : R → (ℕ → τ a) → (ℕ → τ a) → τ a;

rule case (Index $i) $f _ ↪ $f $i
with case (New $i) _ $g ↪ $g $i;

/* index of a value in a list: returns New if the value is not
definitionally equivalent to some element of the list */

sequential symbol index: ℕ → Π [a], τ a → τ(list a) → R;

rule index $k _ □ ↪ New $k
with index $k $x ($x ⸬ _) ↪ Index $k
with index $k $x ($y ⸬ $l) ↪ index ($k Stdlib.Nat.+ Stdlib.Nat._1) $x $l;

/* reification: given a Lambdapi term x of type ℚ, compute an
expression in G and a list of values whose evaluation is equal to
x. WARNING: rfy is sequential. */

sequential symbol rfy: τ(list rat) → ℚ → τ(list grp × list rat);

// addition
rule rfy $l ($x ᵣ+ $y) ↪
  let x ≔ rfy $l $x in let y ≔ rfy (x ₂) $y in ((x ₁) ++ (y ₁)) ‚ (y ₂)

// opposite
with rfy $l (—ᵣ $x) ↪ let x ≔ rfy $l $x in opp (x ₁) ‚ (x ₂)

// substraction
with rfy $l ($x ᵣ- $y) ↪ rfy $l ($x ᵣ+ —ᵣ $y)

// constants
with rfy $l 0 ↪ (Cst 0 ⸬ □) ‚ $l
with rfy $l ((Zpos $n) / (Zpos $d)) ↪ (Cst ((Zpos $n) / (Zpos $d)) ⸬ □) ‚ $l
with rfy $l ((Zneg $n) / (Zpos $d)) ↪ (Cst ((Zneg $n) / (Zpos $d)) ⸬ □) ‚ $l
with rfy $l (0 / _) ↪ (Cst (0 / 1) ⸬ □) ‚ $l

// multiplication by a constant
with rfy $l ((Zpos $n / Zpos $d) *ᵣ $x) ↪ let x ≔ rfy $l $x in (mul (Zpos $n / Zpos $d) (x ₁)) ‚ (x ₂)
with rfy $l ((Zneg $n / Zpos $d) *ᵣ $x) ↪ let x ≔ rfy $l $x in (mul (Zneg $n / Zpos $d) (x ₁)) ‚ (x ₂)
with rfy $l ($x *ᵣ ((Zpos $n) / (Zpos $d))) ↪ let x ≔ rfy $l $x in (mul (((Zpos $n) / (Zpos $d))) (x ₁)) ‚ (x ₂)
with rfy $l ($x *ᵣ ((Zneg $n) / (Zpos $d))) ↪ let x ≔ rfy $l $x in (mul (((Zneg $n) / (Zpos $d))) (x ₁)) ‚ (x ₂)

//other cases are abstracted by a variable
with rfy $l $x ↪
  case (index _0 $x $l) (λ i, (Var i (1⫽1) ⸬ □) ‚ $l) (λ i, (Var i (1⫽1) ⸬ □) ‚ ($l ++ ($x ⸬ □)))
;

symbol reify ≔ rfy □;

symbol compN : ℕ → ℕ → Comp;

rule compN _0 _0 ↪ Eq
with compN _0 (_ +1) ↪ Lt
with compN (_ +1) _0 ↪ Gt
with compN ($x +1) ($y +1) ↪ compN $x $y;

symbol compG : G → G → Comp;
rule compG (Var $i $k) (Var $j $k2) ↪ compN $i $j
with compG (Var _ _) (Cst _) ↪ Gt
with compG (Cst _) (Var _ _)  ↪ Lt
with compG (Cst $c1) (Cst $c2)  ↪ $c1 ᵣ≐ $c2;


symbol split [a: Set] (l : τ (list a)): τ(list a × list a);
rule split □ ↪ (□ ‚ □)
with split ($x ⸬ □) ↪ (($x ⸬ □) ‚ □)
with split ($x ⸬ $y ⸬ $l) ↪  
    let res ≔  (split $l) in
        ($x ⸬ (res ₁)) ‚ ($y ⸬ (res ₂));


symbol list_ind2_principle [A : Set]  :
  Π (P : τ (list A) → Prop),
    π (P □) →
    (Π (a: τ A), π (P (a ⸬ □))) →
    (Π (a b : τ A) (l : τ (list A)), π (P l) →  π (P (a ⸬ b ⸬ l))) →
    Π (l : τ (list A)), π (P l);

opaque symbol ++_eq_+ l x y : π (val ((x ++ y) ‚ l) =  val (x ‚ l) ᵣ+ val (y ‚ l)) ≔
begin
assume l;
induction
{
  assume y;
  simplify;
  change π (val (y ‚ l) = (frac 0 1 ᵣ+ val (y ‚ l)));
  rewrite ᵣ+_neutral_frac_l;
  reflexivity
}
{
  assume x xs ih;
  simplify;
  assume y;
  rewrite ih y;
  rewrite ᵣ+_assoc;
  reflexivity
}
end;

opaque symbol split_correct l gs : π (val (((split gs ₁) ++ (split gs ₂)) ‚ l) = val (gs ‚ l)) ≔
begin
assume l;
refine list_ind2_principle (λ u, (val (((split u ₁) ++ (split u ₂)) ‚ l) = val (u ‚ l))) _ _ _
{reflexivity}
{reflexivity}
{
  assume a b tl ih;
  simplify;
  rewrite left ih;
  rewrite ++_eq_+;
  rewrite ++_eq_+;
  simplify;
  rewrite left .[in x in (_ ᵣ+ x ) = _] ᵣ+_assoc;
  rewrite  .[in x in (_ ᵣ+ (x ᵣ+ _) ) = _] ᵣ+_com;
  rewrite .[in x in (_ ᵣ+ x ) = _] ᵣ+_assoc;
  reflexivity
}
end;

symbol merge  (l1 l2 : τ (list grp)): τ (list grp);
rule merge □ □ ↪ □
with merge □ $l2 ↪ $l2
with merge $l1 □ ↪ $l1
with merge (Cst $c1 ⸬ $l1') (Cst $c2 ⸬ $l2') ↪ (Cst ($c1 ᵣ+ $c2) ⸬ merge $l1' $l2')
with merge (Cst $c ⸬ $l1') (Var $i $k ⸬ $l2') ↪ (Cst $c ⸬ merge $l1' (Var $i $k ⸬ $l2'))
with merge (Var $i $k ⸬ $l1') (Cst $c ⸬ $l2') ↪ (Cst $c ⸬ merge (Var $i $k ⸬ $l1') $l2')
with merge ((Var $i $k1) ⸬ $l1') ((Var $j $k2) ⸬ $l2') ↪
    case_Comp (compN $i $j)
        (Var $i ($k1 ᵣ+ $k2) ⸬ merge $l1' $l2')
        ((Var $i $k1) ⸬ merge $l1' (Var $j $k2 ⸬ $l2'))
        ((Var $j $k2) ⸬ merge (Var $i $k1 ⸬ $l1') $l2')
;

opaque symbol compN_correct x y : π (compN x y = Eq ⇒ x = y) ≔
begin
induction
{ induction
  {assume h; reflexivity}
  {assume y hy h; apply ⊥ₑ; apply Lt≠Eq h}
}
{ assume x hx; induction
  {assume h; apply ⊥ₑ; apply Gt≠Eq h}
  {assume y hy h; apply feq (+1); apply hx y h }
}
end;

opaque symbol merge_correct l g1 g2 : π (val ((merge  g1 g2) ‚ l ) = val (g1 ‚ l) ᵣ+ val (g2 ‚ l)) ≔
begin
    assume l;
    induction
    { simplify; assume x; change π (val (x ‚ l) = (frac 0 1 ᵣ+ val (x ‚ l))); rewrite ᵣ+_neutral_frac_l;  reflexivity }
    {
      induction
      {
        assume k1 xs ih1;
        induction
        {
          simplify;
          //change π ((k1 ᵣ+ val (xs ‚ l)) = ((k1 ᵣ+ val (xs ‚ l)) ᵣ+ frac 0 1));
          change π ((k1 ᵣ+ val (xs ‚ l)) = ((k1 ᵣ+ val (xs ‚ l)) ᵣ+ (0 / _1)));
          rewrite ᵣ+_neutral_div_r (k1 ᵣ+ val (xs ‚ l));
          reflexivity
        }
        {
          induction
          {
            assume k2 ys ih2;
            simplify; rewrite ih1;
            rewrite ᵣ+_assoc;
            rewrite  left .[x in _ ᵣ+ x = _] ᵣ+_assoc;
            rewrite ᵣ+_com k2;
            rewrite  .[x in _ ᵣ+ x = _] ᵣ+_assoc;
            rewrite left ᵣ+_assoc;
            reflexivity
          }
          {
            assume i k2 ys ih2;
            simplify; rewrite ih1;
            simplify;
            rewrite left ᵣ+_assoc;
            reflexivity
          }
        }
      }
      {
        assume i k1 xs ih1;
        induction
        {
          simplify val;
          simplify 0⫽1;
          rewrite ᵣ+_neutral_div_r;
          reflexivity          
        }
        {
          induction
          {
            assume K ys ih2;
            simplify;
            rewrite ih2;
            simplify;
            rewrite ᵣ+_com;
            rewrite ᵣ+_assoc;
            rewrite ᵣ+_com K;
            reflexivity
          }
          {
            assume j k2 ys ih2;
            simplify;
            refine ind_Comp (λ u, (compN i j) = u ⇒ val (case_Comp (compN i j) (Var i (k1 ᵣ+ k2) ⸬ merge xs ys) (Var i k1 ⸬ merge xs (Var j k2 ⸬ ys)) (Var j k2 ⸬ merge (Var i k1 ⸬ xs) ys) ‚ l) = (((nth l i *ᵣ k1) ᵣ+ val (xs ‚ l)) ᵣ+ ((nth l j *ᵣ k2) ᵣ+ val (ys ‚ l)))) _ _ _ (compN i j) _
            {
              simplify;
              assume heq;
              rewrite heq;
              simplify;
              rewrite compN_correct i j heq;
              rewrite distr*ᵣᵣ+;
              rewrite ih1;
              rewrite ᵣ+_assoc;              
              set XS ≔ val (xs ‚ l);
              set YS ≔ val (ys ‚ l);
              rewrite  left .[x in _ ᵣ+ x = _] ᵣ+_assoc;
              rewrite .[x in _ ᵣ+ (x ᵣ+ _) = _] ᵣ+_com; 
              rewrite .[x in _ ᵣ+ x = _] ᵣ+_assoc;
              rewrite left .[x in x = _] ᵣ+_assoc;
              reflexivity
            }
            {
              simplify;
              assume hlt;
              rewrite hlt;
              simplify;
              rewrite ih1;
              simplify;
              rewrite ᵣ+_assoc;
              rewrite left ᵣ+_assoc;
              reflexivity
            }
            {
              assume hgt;
              rewrite hgt;
              simplify;
              rewrite ih2;
              simplify;
              rewrite ᵣ+_com;
              rewrite ᵣ+_assoc;
              rewrite ᵣ+_com (val (ys ‚ l));
              reflexivity
            }
            {reflexivity}
          }
        }
      }  
  }
end;


symbol mergesort:  τ (list grp) →  τ (list grp);
rule mergesort □ ↪ □
with mergesort ($x ⸬ □) ↪ ($x ⸬ □)
with mergesort ($x ⸬ $y ⸬ $l) ↪ 
    let s ≔ split ($x ⸬ $y ⸬ $l) in
    let l1 ≔ s ₁ in
    let l2 ≔ s ₂ in
        merge (mergesort l1) (mergesort l2);      

opaque symbol rec_𝕃 : Π [a: Set], Π l: 𝕃 a, Π p: (𝕃 a → Prop), π (p □) → (Π x0: τ a, Π l': 𝕃 a, π (p (x0 ⸬ l'))) → π (p l) ≔ 
begin
  assume a l P H1 H2;
  refine @ind_𝕃 a P H1 (λ x l' ih, H2 x l') l
end;

opaque symbol case_l [a] x (l: 𝕃 a) n : π ((size (x ⸬ l)) Stdlib.Nat.≤ (n +1)) → π (size l Stdlib.Nat.≤ n) ≔
begin
  assume a x l n;
  refine λ x, x;
end;

opaque symbol size_split [a] (l: 𝕃 a) : π (size ((split l) ₁) Stdlib.Nat.≤ size l) ≔
begin
  assume a;
  refine list_ind2_principle (λ u, istrue (size (split u ₁) Stdlib.Nat.≤ size u)) _ _ _
  {apply ⊤ᵢ}
  {assume y; apply ⊤ᵢ}
  {
    simplify;
    assume x y l ih;
    apply @leq_trans (size (split l ₁)) (size l) (size l +1) ih _;
    refine leqnSn (size l)
  }
end;

opaque symbol size_split2 [a] (l: 𝕃 a) : π (size ((split l) ₂) Stdlib.Nat.≤ size l) ≔
begin
  assume a;
  refine list_ind2_principle (λ u, istrue (size (split u ₂) Stdlib.Nat.≤ size u)) _ _ _
  {apply ⊤ᵢ}
  {assume y; apply ⊤ᵢ}
  {
    simplify;
    assume x y l ih;
    apply @leq_trans (size (split l ₂)) (size l) (size l +1) ih _;
    refine leqnSn (size l)
  }
end;

opaque symbol mergesort_correct_aux n l g : π (size g Stdlib.Nat.≤ n)  →  π (val ((mergesort g) ‚ l ) = val ( g ‚ l)) ≔
begin
    induction
    {
        assume l;
        assume g h;
        type ≤0 (size g) h;
        rewrite size0nil g (≤0 (size g) h);
        reflexivity
    }
    {
      assume n ihn l g;
      refine rec_𝕃 g (λ u, (size u Stdlib.Nat.≤ (n +1)) ⇒ ((val ( (mergesort u) ‚ l) = val ( u ‚ l)))) _ _
      {
        simplify;
        reflexivity
      }
      {
        assume x g';
        refine rec_𝕃 g' (λ u, (size (x ⸬ u) Stdlib.Nat.≤ (n +1)) ⇒ ((val ( (mergesort (x ⸬ u)) ‚ l) = val ( (x ⸬ u) ‚ l)))) _ _
        {reflexivity}
        {
          assume y g'' inv1;
          simplify;
          rewrite (merge_correct l (mergesort (x ⸬ ((split g'') ₁))) (mergesort (y ⸬ ((split g'') ₂))));
          have tmp3x: π (istrue (size (x ⸬ (split g'' ₁)) Stdlib.Nat.≤ n)) {
            apply @leq_trans
            (size (split g'' ₁) +1)
            (size g'' +1)
            n
            _
            inv1;
            apply size_split g''
          };
          rewrite ihn l (x ⸬ (split g'' ₁)) tmp3x;
          have tmp3y: π (istrue (size (y ⸬ (split g'' ₂)) Stdlib.Nat.≤ n)) {
            simplify;
            apply @leq_trans
            (size (split g'' ₂) +1)
            (size g'' +1)
            n
            _
            inv1;
            simplify;
            apply size_split2 g''
          };
          rewrite ihn l (y ⸬ (split g'' ₂)) tmp3y;
          simplify;
          rewrite ᵣ+_assoc;
          rewrite left .[x in (_ ᵣ+ x) = _] ᵣ+_assoc;
          rewrite ᵣ+_com  (val ((split g'' ₁) ‚ l)) (val_grp y l);
          rewrite  ᵣ+_assoc;
          rewrite left ++_eq_+ l (split g'' ₁) (split g'' ₂);
          rewrite split_correct;
          reflexivity
        }
      }
    }
end;

symbol mergesort_correct l g ≔ mergesort_correct_aux (size g) l g (Stdlib.Nat.≤_refl (size g));


symbol remove0 : τ(list grp) → τ(list grp);

rule remove0 □ ↪ □
with remove0 (Cst (0 / _) ⸬ $l) ↪ remove0 $l
with remove0 (Cst (Zpos H / Zpos $d) ⸬ $l) ↪ Cst (Zpos H / Zpos $d) ⸬ remove0 $l
with remove0 (Cst (Zpos $n / Zpos $d) ⸬ $l) ↪ Cst (Zpos $n / Zpos $d) ⸬ remove0 $l
with remove0 (Cst (Zneg $n / Zpos $d) ⸬ $l) ↪ Cst (Zneg $n / Zpos $d) ⸬ remove0 $l
with remove0 (Var _ (0 / _) ⸬ $l) ↪ remove0 $l
with remove0 (Var $i (Zpos H / Zpos $d) ⸬ $l) ↪ Var $i (Zpos H / Zpos $d) ⸬ remove0 $l
with remove0 (Var $i (Zpos $n / Zpos $d) ⸬ $l) ↪ Var $i (Zpos $n / Zpos $d) ⸬ remove0 $l
with remove0 (Var $i (Zneg $n / Zpos $d) ⸬ $l) ↪ Var $i (Zneg $n / Zpos $d) ⸬ remove0 $l
;


opaque symbol remove0_correct l gs : π (val ((remove0 gs) ‚ l) = val (gs ‚ l)) ≔
begin
  assume l;
  induction // on l
  {
    simplify;
    reflexivity
  }
  {
    induction // on g
    {
      // // Case Cst k
      // induction 
      // // Case Z0
      // { assume  gs ih;  simplify; apply ih }
      // // Case Zpos
      // { assume c gs ih; simplify; rewrite ih; reflexivity }
      // // Case Zneg
      // { assume c gs ih; simplify;  rewrite ih; reflexivity }
    }
    {
      // Case Var i k
      // assume i;
      // induction // on k
      // {assume gs ih; simplify; rewrite ih; reflexivity} // Case Z0
      // { assume c gs ih; simplify; rewrite ih; reflexivity } // Case Zpos
      // { assume c gs ih; simplify; rewrite ih; reflexivity } // Case Zneg
    }
  }
admitted;

//compute mergesort ((Var Nat._3 2) ⸬ (Var Nat._2 2) ⸬ (Var Nat._1 2) ⸬ Cst 10 ⸬ □);

symbol norm_speed x ≔ (remove0 (mergesort x));

symbol varmax : 𝕃 grp → ℕ;

rule varmax ((Cst _) ⸬ $xs) ↪ (varmax $xs)
with varmax ((Var $k _) ⸬ $xs) ↪ max $k (varmax $xs)
with varmax □ ↪ _0;

opaque symbol eq_trans [a] (x y z:τ a) : π(x = y ⇒ y = z ⇒ x = z) ≔
begin
assume a x y z xy yz; rewrite xy; refine yz
end;

opaque symbol norm_correct (x: 𝕃 grp) l : π(val((norm_speed x) ‚ l) = val(x ‚ l)) ≔
begin
  assume x l; simplify; apply eq_trans (val (remove0 (mergesort x) ‚ l)) (val (mergesort x ‚ l)) (val (x ‚ l))
  { apply remove0_correct l (mergesort x) }
  {
    apply eq_trans (val ((mergesort (x)) ‚ l)) (val (( x) ‚ l)) (val (x ‚ l))
    {apply mergesort_correct l x}
    {reflexivity}
  }
end;

symbol ≐_decides_neq [x y] : π ((x ᵣ≐ y) ≠ Eq ⇒ x ≠ y) ≔
begin
admit
end;

symbol eta_prod [a b] (x:τ(a × b)): π(x = (x ₁) ‚ (x ₂));

opaque symbol reify_correct x: π(val(reify x) = x) ≔
begin
refine ind_Rat (λ u, (val (reify u) = u)) _;
induction
{assume y; simplify; rewrite div_0_num (sign y * sign y); reflexivity }
{assume p y; simplify reify; simplify rfy;
  change π (val (case (index Stdlib.Nat._0 (frac (Zpos p) y) □) (λ i, (Var i (1 / 1) ⸬ □) ‚ □) (λ i, (Var i (1 /1 ) ⸬ □) ‚ ((frac (Zpos p) y) ⸬ □))) = frac (Zpos p) y);
  simplify val; simplify val_grp; simplify nth;  simplify val; 
  simplify 0⫽1;
  rewrite ᵣ+_neutral_div_r;
  rewrite ᵣ*_neutral_div_r;
  reflexivity
}
{
  assume p y; simplify reify; simplify rfy;
  change π (val (case (index Stdlib.Nat._0 (frac (Zneg p) y) □) (λ i, (Var i (1 / 1) ⸬ □) ‚ □) (λ i, (Var i (1 /1 ) ⸬ □) ‚ ((frac (Zneg p) y) ⸬ □))) = frac (Zneg p) y);
  simplify val; simplify val_grp; simplify nth;  simplify val; 
  simplify 0⫽1;
  rewrite ᵣ+_neutral_div_r;
  rewrite ᵣ*_neutral_div_r;
  reflexivity
}
end;


symbol l1 x y : π(((2 *ᵣ x) ᵣ+ y) ᵣ- ((2 *ᵣ x) ᵣ+ y) ≠ (1 /1 )) ≔
begin
  assume x y;
  refine ≐_decides_neq _;
  rewrite left .[z in z ᵣ≐ _] reify_correct;
  set e ≔ reify (((2 *ᵣ x) ᵣ+ y) ᵣ- ((2 *ᵣ x) ᵣ+ y));
  compute e;
  rewrite .[z in val z] eta_prod;
  rewrite left norm_correct (e ₁) (e ₂);
  simplify;
  refine Lt≠Eq
end;