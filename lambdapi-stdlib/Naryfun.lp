require open Stdlib.HOL Stdlib.Nat Stdlib.Impred;

inductive Sets : ℕ → TYPE ≔
| ι  : Sets 0
| ⭆ : Π [n : ℕ], Set → Sets n → Sets (n +1);



symbol sets (n: τ nat): Set;
rule τ (sets $n) ↪ Sets $n;

notation ⭆ infix right 10;

symbol arrows n : Sets n → Set → Set;
rule arrows 0 _ $b ↪ $b
with arrows ($n +1) ($t ⭆ $ts) $b ↪ $t ⤳ (arrows $n $ts $b);

symbol Arr [n] (dom: Sets n) (cod: Set) : TYPE ≔ τ (@arrows n dom cod);

compute Arr (o ⭆ o ⭆ ι) o;

assert ⊢ (∧) : Arr (o ⭆ o ⭆ ι) o;

symbol SetsUniform n (t: Set): Sets n;
rule SetsUniform 0 $t ↪ ι
with SetsUniform ($n +1) $t ↪ $t ⭆ (SetsUniform $n $t);

symbol ArrU n (a: Set) ≔ Arr (SetsUniform n a) a;


// The function congₙ will compute a proof of the form : (f g : A₁ → .. → Aₙ → B) →
// a₁ ≡ b₁ → ... → aₙ ≡ bₙ →
// f a₁ .. aₙ ≡ g b₁ ... bₙ
symbol Cong n [ts: Sets n] [R] (f g: Arr ts R): Prop;
rule Cong 0 $f $g ↪ $f = $g
with @Cong ($n +1) ($t ⭆ $ts) $R $f $g ↪ `∀ (x : τ $t), `∀ (y : τ $t), (x = y) ⇒ @Cong $n $ts $R ($f x) ($g y);

symbol f1: Arr (o ⭆ o ⭆ o ⭆ o ⭆ ι) o;
symbol f2: ArrU 4 o;

assert ⊢ f1 : τ (o ⤳ o ⤳ o ⤳ o ⤳ o);
assert ⊢ f2 : τ (o ⤳ o ⤳ o ⤳ o ⤳ o);
assert ⊢ Arr (o ⭆ o ⭆ o ⭆ o ⭆ ι) o ≡ τ (o ⤳ o ⤳ o ⤳ o ⤳ o);

// The congruence lemma is then obtained by stating that
// the n-ary function f is congruent with itself. We prove it by
// induction on n, pattern-matching on the proofs of equality
// as we go along.
symbol congₙ  [D: Set] n [ts: Sets n] (f: Arr ts D): π (@Cong n ts D f f) ≔
begin
  assume D n;
   refine ind_Sets (λ n, λ u, `∀ f, @Cong n u D f f) _ _ (n) {
      reflexivity
    } {
      assume m t ts ih;
      assume f t1 t2 hrefl;
      rewrite hrefl;
      refine (ih (f t2))
    }
end;

private symbol testCong a b c d x y w z : π (a = x) → π (b = y) → π (c = w) → π (d = z) → π (f1 a b c d = f1 x y w z) ≔
begin
  assume a b c d x y w z heq1 heq2 heq3 heq4;
  refine @congₙ o 4 (o ⭆ o ⭆ o ⭆ o ⭆ ι) (f1) a x heq1 b y heq2 c w heq3 d z heq4;
end;

private symbol testCong2 a b c d x y w z : π (a = x) → π (b = y) → π (c = w) → π (d = z) → π (f1 a b c d = f1 x y w z) ≔
begin
  assume a b c d x y w z heq1 heq2 heq3 heq4;
  refine @congₙ o 4 (o ⭆ o ⭆ o ⭆ o ⭆ ι) (f1) a x heq1 b y heq2 c w heq3 d z heq4;
end;


// Pointwise lifting of a unary function can be defined uniformly for any operation of type (A → B) and
// an n-ary function whose domain match and codomain is respectively B. It is defined by induction on the arity
// n of the input functions.
symbol lift [A B: Set] (n: ℕ) [dom: Sets n] : (τ A → τ B) → Arr dom A → Arr dom B;
rule lift 0 $op $f ↪ $op $f
with @lift $A $B ($n +1) ($t ⭆ $ts) $op $f ↪ λ x, @lift $A $B $n $ts $op ($f x);

// Pointwise lifting of a binary function can be defined uniformly for any operation of type (A → B → C) and any pair
// of n-ary functions whose domains match and codomains are
// respectively A and B. It is defined by induction on the arity
// n of the input functions.
symbol lift2 [A B C: Set] (n: ℕ) [dom: Sets n] : (τ A → τ B → τ C) → Arr dom A → Arr dom B → Arr dom C;
rule lift2 0 $op $f $g ↪ $op $f $g
with @lift2 $A $B $C ($n +1) ($t ⭆ $ts) $op $f $g ↪ λ (x: τ $t), @lift2 $A $B $C $n $ts $op ($f x) ($g x);

// We may for instance want to map a unary function on
// the result of an n-ary one. Note that this empowers us to
// partially apply any n-ary function to a value x in its k-th
// argument by choosing to see it as a k-ary function and mapping (_$ x) on it.
symbol mapₙ [a b] n [dom: Sets n]: (τ a → τ b) → Arr dom a → Arr dom b;
rule mapₙ 0 $f $v ↪ $f $v
with @mapₙ $a $b ($n +1) ($t ⭆ $ts) $op $f ↪ λ (x: τ $t), @mapₙ $a $b $n $ts $op ($f x);