# Polyequality elaboration
In Alethe, we call "polyequality" the notion of equivalence between terms modulo the reordering
of equalities. For example, we say that the terms `(or (= a b) c)` and `(or (= b a) c)` are
"polyequal", despite the equality term being flipped.

When checking an Alethe proof, a checker often needs to reason modulo polyequality. The `refl`
rule, for example, allows the two terms to be syntactically different, if they are equivalent by
polyequality. The following step is valid:
```
(step t1 (cl (= (or (= a b) c) (or (= b a) c))) :rule refl)
```

The `polyeq` elaboration step can be used to remove all such instances where polyequality reasoning
is required. For exemple, calling `carcara elaborate --pipeline polyeq` on the above step will
transform it into the following steps:
```
(step t1.t1 (cl (= (= a b) (= b a))) :rule eq_symmetric)
(step t1.t2 (cl (= (or (= a b) c) (or (= b a) c))) :rule cong :premises (t1.t1))
```

In this case, Carcara added an `eq_symmetric` step to equate the two flipped equalities, and used a
`cong` step to construct the original conclusion of `t1`. The exact elaboration differs by rule. The
rules affected by this elaboration step are:
- `assume`
- `refl`
- `forall_inst`
- `subproof`
- `ite_intro`
- `bfun_elim`
