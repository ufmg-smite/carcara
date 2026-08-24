# "Local" elaboration
Carcara has a number of small elaboration procedures for specific rules, that simplify steps in some
small local way. These are grouped in the `local` elaboration pass. The rules affected by this are:
- `eq_transitive`
- `trans`
- `eq_congruent`
- `cong`
- `resolution`
- `eq_mp`

## Transitivity rules
The `eq_transitive` and `trans` rules may sometimes contain the transitivity chain in an incorrect
order. Additionally, the premise equalities might be flipped. For example, for `trans`, you may
have:
```
(assume h1 (= a b))
(assume h2 (= c d))
(assume h3 (= c b))
(step t4 (cl (= a d)) :rule trans :premises (h1 h2 h3))
```

In this case, the `local` elaboration pass will change the order of `t4`'s premises so the
transitivity chain is well ordered; and add an auxiliary step to flip the `h3` equality. After
elaboration, we will have:
```
(assume h1 (= a b))
(assume h2 (= c d))
(assume h3 (= c b))
(step t4.t1 (cl (= b c)) :rule symm :premises (h3))
(step t4 (cl (= a d)) :rule trans :premises (h1 t4.t1 h2))
```

A similar procedure is applied for the `eq_transitive` rule.

## Congruence rules
In some applications of the `eq_congruent` and `cong` rules, the premise equalities may be flipped.
In this case, Carcara will make this symmetry reasoning explicit. For example, the proof:
```
(assume h1 (= b a))
(assume h2 (= c d))
(step t3 (cl (= (and a c) (and b d))) :rule cong :premises (h1 h2))
```
will become
```
(assume h1 (= b a))
(assume h2 (= c d))
(step t3.t1 (cl (= a b)) :rule symm :premises (h1))
(step t3 (cl (= (and a c) (and b d))) :rule cong :premises (t3.t1 h2))
```
after elaboration. A similar elaboration is applied for the `eq_congruent` rule.

In the specific case where the `cong` rule is used over the `=` operator, the argument order might
also be flipped in one of the conclusion terms. For example, the following step is valid according
to the Alethe specification:
```
(assume h1 (= x y))
(step t2 (cl (= (= 0 x) (= y 0))) :rule cong :premises (h1))
```
To simplify this, the `local` elaboration will add `eq_symmetric` and `trans` auxiliary steps,
resulting in the following:
```
(assume h1 (= x y))
(step t2.t1 (cl (= (= 0 x) (= x 0))) :rule eq_symmetric)
(step t2.t2 (cl (= (= x 0) (= y 0))) :rule cong :premises (h1))
(step t2 (cl (= (= 0 x) (= y 0))) :rule trans :premises (t2.t1 t2.t2))
```

## `resolution` rule
In Alethe, `resolution` steps do not need to provide the pivots used in the resolution chain. For
example, in the following proof, the step `t4` omits the pivots:
```
(step t1 (cl p (not q)) :rule hole)
(step t2 (cl (not p)) :rule hole)
(step t3 (cl q r) :rule hole)
(step t4 (cl r) :rule resolution :premises (t1 t2 t3))
```

During elaboration, Carcara can find which pivots were used and add them to the proof step as
arguments. For each pivot, two arguments are provided: the pivot term, and a boolean indicating
whether it appears on the left-hand clause with positive polarity. For the example above, the
elaborated step will be:
```
(step t4 (cl r) :rule resolution :premises (t1 t2 t3) :args (p true q false))
```

## `eq_mp` rule
The `eq_mp` rule is not part of the Alethe specification. It is an extra rule, equivalent to
CPC's `EQ_RESOLVE`, that derives `F2` from `F1` and `(= F1 F2)`:
```
(assume h1 p)
(assume h2 (= p q))
(step t3 (cl q) :rule eq_mp :premises (h1 h2))
```
During elaboration, it is replaced by a `resolution` step taking the original
premises and a new `equiv_pos2` step:
```
(assume h1 p)
(assume h2 (= p q))
(step t3.t1 (cl (not (= p q)) (not p) q) :rule equiv_pos2)
(step t3 (cl q) :rule resolution :premises (t3.t1 h2 h1) :args ((= p q) false p false))
```
In the odd case where `q` is exactly `(not p)` this pattern would break the
resolution, so instead the elaboration is done with a resolution step that
considers just the equivalence premise and relies on implicit duplicate
elimination (which can be further eliminated by other elaboration passes if they
are active). The `equiv_pos2` step is nested one level deeper here, so that its
id does not clash with the ones used by the `uncrowd` pass when it adds the
`contraction` step that removes the duplicate:
```
(assume h1 p)
(assume h2 (= p (not p)))
(step t3.t1.t1 (cl (not (= p (not p))) (not p) (not p)) :rule equiv_pos2)
(step t3 (cl (not p)) :rule resolution :premises (t3.t1.t1 h2) :args ((= p (not p)) false))
```
