# Proof slicing
The `carcara slice` command can be used to extract an individual step from a proof, along with
its transitive premises. Besides the usual arguments for parsing and printing the proof, this
command also takes a `--from` argument which gives the step id from which to slice, and an optional
`--max-distance`/`-d` argument, that specifies how many layers of transitive premises the slice
should include.

## Example
Consider the following Alethe proof:
```
(assume a0 a)
(step t0 (cl a b) :rule hole :premises (a0))
(step t1 (cl b a) :rule hole :premises (t0))
(step t2 (cl a b (not a)) :rule hole :premises (t0))
(anchor :step t3)
(assume t3.a0 (not a))
(step t3.t0 (cl b) :rule hole :premises (t3.a0 t1))
(step t3.t1 (cl b b) :rule hole :premises (t3.t0))
(step t3.t2 (cl (or b b)) :rule hole :premises (t3.t1))
(step t3 (cl (not (not a)) (or b b)) :rule subproof :discharge (t3.a0))
(step t4 (cl a (or b b)) :rule hole :premises (t3))
(step t5 (cl) :rule hole :premises (t4 a0 t2))
```
Calling `carcara slice --from t1 -d 1` on it will result in the steps:
```
(assume a0 a)
(step t0 (cl a b) :rule hole :premises (a0))
(step t1 (cl b a) :rule hole :premises (t0))
(step slice_end (cl) :rule hole :premises (t1) :args ("trust"))
```
Note that, to make sure the slice is still a valid proof, Carcara added a dummy `slice_end` step
that concludes the empty clause.

You can also slice from inside a subproof. Calling `carcara slice --from t3.t0` on the proof above
results in the slice:
```
(step t1 (cl b a) :rule hole :args ("trust"))
(anchor :step t3)
(assume t3.a0 (not a))
(step t3.t0 (cl b) :rule hole :premises (t3.a0 t1))
(step t3.t2 (cl (or b b)) :rule hole :premises (t3.t0) :args ("trust"))
(step t3 (cl (not (not a)) (or b b)) :rule subproof :discharge (t3.a0))
(step slice_end (cl) :rule hole :premises (t3) :args ("trust"))
```
A few things of note:
- Since we did not pass `--max-distance`/`-d`, the slice only included the direct premises of
`t3.t2`, and no transitive premises. For example, `t0`, which is a transitive premise of `t3.t2` via
`t1`, was not included.
- To keep any context that might be introduced in an `anchor`, the slice included all `anchor`s
surrounding the sliced step (in this case, `(anchor :step t3)`).
- To ensure that the resulting proof is still valid, the slice has to include the `t3` step that
concludes the subproof, as well as the previous step (`t3.t2`) which is implicitly referenced by
`t3`.
