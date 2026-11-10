# Using external checking tools
To support checking of non-standard rules, Carcara is able to call into external tools, delegating
the checking of specific rules.

To do this, use the `-x <rule>=<checker>` option, which takes a rule name and an external checking
tool as a value. To check multiple rules this way, you may use the `-x` option multiple times.
If you need to pass options to the checking tool, you must surround the `-x` value in quotes. For
example:
```bash
carcara check proof.alethe problem.smt2 \
    -x cong=check-cong.sh \
    -x "discombobulate=discombobulator.py --fast"
```

This will check every `cong` step using the `check-cong.sh` script, and every step of the
(non-standard) `discombobulate` rule by calling `discombobulator.py --fast`.

## Format
Carcara will send, to the stdin of the checker process, the step's conclusion, arguments, and
premises, in the following format:
```
<conclusion>
<arguments>
(
<premises>
)
```
where `<conclusion>` and `<arguments>` are parenthesised lists of terms separated by spaces,
and `<premises>` is a sequence of such lists, each representing the conclusion of one of the step's
premises.

### Example
Say we use an external checker to check step `t2` in the following proof:
```
(step t0 (cl p1 p2) :rule hole)
(step t1 (cl p3 p4) :rule hole)
(step t2 (cl c1 c2 c3) :rule discombobulate :premises (t0 t1) :args (a1 a2))
```

Carcara will send the following to the external checker's stdin:
```
(c1 c2 c3)
(a1 a2)
(
(p1 p2)
(p3 p4)
)
```

If the checker returns a successful exit code and outputs `true` to stdout, `t2` will be considered
valid.
