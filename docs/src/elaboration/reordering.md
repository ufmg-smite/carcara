# Reordering elimination
For many use cases of Alethe like proof translation or reconstruction in proof assistants, clause
reordering steps can be challenging to deal with. With that in mind, Carcara has an elaboration step
that can completely remove all `reordering` steps from a proof.

This is done by replacing the `reordering` step with its premise and, anytime it is used as a
premise in another step, recomputing the clause of the step that used it. As an exmple, consider the
following proof:
```
(step t1 (cl a b c) :rule hole)
(step t2 (cl b a c) :rule reordering :premises (t1))
(step t3 (cl b a c d) :rule weakening :premises (t2))
```
Here, step `t2` will be eliminated, such that step `t3` uses `t1` directly as its premise. However,
simply changing the premise clause of step `t4` would make it invalid[^1]. To avoid this, Carcara
must also recompute the conclusion of `t3`, resulting in the following proof:
```
(step t1 (cl a b c) :rule hole)
(step t3 (cl a b c d) :rule weakening :premises (t1))
```
Of course, if any step further down in the proof uses `t3` as a premise, it will also need to
be recomputed, and these changes will propagate down the proof.

[^1]: Strictly speaking, the step would not be invalid according to the semantics of Alethe, which
are entirely agnostic to clause ordering. However, when elaborating a proof, we aim to ensure a more
strict semantics, in which clause ordering is maitained in rules such as `weakening`.
