# Resolution uncrowding
Besides [finding resolution pivots](./local.md#resolution-rule), Carcara is also able to refine
`resolution` steps by _uncrowding_ them. This refers the process of making the implicit removal of
duplicates explicit, by the addition of `contraction` steps.

More specifically, the `uncrowd` elaboration pass will find all spots in the resolution chain where
a pivot is used to remove a duplicate literal. Then, it breaks the resolution chain at that point,
and adds a contraction step. Consider, for example, the following proof:
```
(step t1 (cl a b) :rule hole)
(step t2 (cl (not b) a) :rule hole)
(step t3 (cl (not a)) :rule hole)
(step t4 (cl) :rule resolution :premises (t1 t2 t3) :args (b true a true))
```

Here, the `a` pivot is duplicated after resolving `t1` and `t2`, but is removed by the single `(not
a)` literal in `t3`. After elaboration, the resulting proof will be:
```
(step t1 (cl a b) :rule hole)
(step t2 (cl (not b) a) :rule hole)
(step t3 (cl (not a)) :rule hole)
(step t4.t1 (cl a a) :rule resolution :premises (t1 t2) :args (b true))
(step t4.t2 (cl a) :rule contraction :premises (t4.t1))
(step t4 (cl) :rule resolution :premises (t4.t2 t3) :args (a true))
```

The resolution chain was broken after `t2`, with `t4.t1` containing the two duplicate `a` literals
explicitly. Then, a contraction step was added (`t4.t2`) to deduplicate them. Finally, the
resolution chain continues in `t4`, reaching the same conclusion.

Besides adding `contraction` steps, the uncrowding elaboration pass may also add a `reordering` step
at the end of the resolution chain, to make any implicit reordering of clause literals explicit.

If the option `--uncrowd-rotate` is given, Carcara will try to further minimize the number of
`contraction` steps added by reordering the resolution premises when possible, in an effort to make
a single `contraction` step deduplicate multiple pivots.
