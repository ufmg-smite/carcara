# Checking proofs with Carcara
To check a proof file with Carcara, use the `check` command, passing both the proof file and the
original SMT-LIB problem file:
```
carcara check example.smt2.alethe example.smt2
```

If the problem filename is exactly the proof filename minus `.alethe`, you can omit it, and Carcara
will infer it:
```
carcara check example.smt2.alethe
```

When checking a proof, Carcara will report one of three outcomes:
- `valid`: The proof was fully checked, and no errors were found.
- `invalid`: An error was found in part of the proof; an error message will have been printed.
- `holey`: No errors were found, but the proof contained one or more "holes". These can be either
explicit applications of the `hole` rule, or steps that use an unknown or unsupported rule.

See `carcara check --help` for a full list of options.

## Dealing with unknown rules
By default, Carcara will return a checking error when encountering a rule it does not recognize.
If instead you want to ignore such rules, you can use the `--ignore-unknown-rules`/`-i` flag.
Alternatively, you can use the `--allowed-rules` option to pass a specific list of unkown rules to
allow. For example:
```
carcara check example.smt2.alethe --allowed-rules foo bar
```

If a proof uses a rule that is allowed by either `--ignore-unknown-rules` or `--allowed-rules`, it
will be considered `holey`.

## The `lia_generic` rule
Carcara does not check steps that use the `lia_generic` rule. This is an extremely coarse-grained
rule from the Alethe format, and is in general NP-hard to check. If you need to validate proofs
that contain this rule, you can use Carcara's proof elaboration to call an external tool that can
elaborate these steps into a series of easier-to-check steps. For more details, see [the proof
elaboration chapter](elaboration.md).

## Parallel checking
Using the `--num-threads`/`-u` option, you can control how many concurrent threads Carcara will use
to check the proof. If the given value is greater than 1, Carcara will split the proof steps among
that many worker threads, and check them in parallel. Note that proof parsing, which is oftentimes a
bottleneck in Carcara, will still be sequential.
