# Term diff
Often, Carcara will determine that a proof is invalid because two terms that were supposed to be
equal weren't. These errors can be very hard to debug, especially if the terms are large and their
difference is subtle. To help in that, Carcara is able to produce a _diff_ whenever it encounters a
term equality error, via the `--diff` flag, accepted by the `check` and `elaborate` commands.

You can also produce a term diff by calling the `carcara diff <problem> <terms>` command directly.
It takes an SMT-LIB problem file and a file containing two SMT-LIB/Alethe terms, and produces the
diff between the terms. See `carcara diff --help` for more details.

## Example
The diff between the terms `(and (= 0 1) false)` and `(and (= 1 0) false (not true))` is displayed as:
```diff
 (and
   (=
-    0
     1
+    0
   )
   false
+  (not true)
 )
```
