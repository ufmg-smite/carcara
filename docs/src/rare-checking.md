# Checking Rare rewrites

SMT solvers can produce proofs that may depend on rare rules. In general, rare rules have the following format:

```
(declare-rare-rule bool-implies-de-morgan ((x1 Bool) (y1 Bool))
  :args (x1 y1)
  :conclusion (= (not (=> x1 y1)) (and x1 (not y1)))
)
```

First, we have a set of arguments and a conclusion. We can substitute the arguments into the conclusion. The substitution can be any first-order term available in the Alethe context.

```
(step st191.t1 
  (cl (= (not (=> (not (member$ ?v0 ?v1)) (= ?v0 ?v2)))
         (and (not (member$ ?v0 ?v1)) (not (= ?v0 ?v2)))))
  :rule rare_rewrite
  :args ("bool-implies-de-morgan" (not (member$ ?v0 ?v1)) (= ?v0 ?v2)))
```

Arguments can also be polymorphic:

```lisp
(declare-rare-rule eq-refl ((@T0 Type) (t1 @T0))
  :args (t1)
  :premises ()
  :conclusion (= (= t1 t1) true))
```

We use `@Type` to denote an argument that is a polymorphic type. Polymorphic arguments are not passed in the `:args` field of the step statement:

```lisp
(step t264
  (cl (= (= (op e3 e3) (op e3 e3)) true))
  :rule rare_rewrite
  :args ("eq-refl" (op e3 e3)))
```

## Flags

We use the `--rare-file` flag to pass the rare file, for example:

```bash
carcara check your_file.smt2.alethe your_file.smt2 --rare-file your_rare_file.rare
```

Note that Carcara will only be able to check your proofs if every rewrite rule mentioned in the Alethe file is also present in your rare file.
