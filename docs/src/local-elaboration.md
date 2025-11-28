# "Local" elaboration
Carcara has a number of small elaboration procedures for specific rules, that simplify steps in some small local way. These are grouped in the `local` elaboration step. The rules affected by this are:
- `eq_transitive`
- `trans`
- `cong`
- `resolution`

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

In this case, the `local` elaboration step will change the order of `t4`'s premises so the transitivity chain is well ordered; and add an auxiliary step to flip the `h3` equality. After elaboration, we will have: 
```
(assume h1 (= a b))
(assume h2 (= c d))
(assume h3 (= c b))
(step t4.t1 (cl (= b c)) :rule symm :premises (h3))
(step t4 (cl (= a d)) :rule trans :premises (h1 t4.t1 h2))
```

A similar procedure is applied for the `eq_transitive` rule.

## `cong` rule
In the specific case where the `cong` rule is used over the `=` operator, the argument order might
be flipped in one of the terms. For example, the following step is valid according to the Alethe
specification:
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
In Alethe, `resolution` steps do not need to provide the pivots used in the resolution chain. For example, in the following proof, the step `t4` omits the pivots:
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

