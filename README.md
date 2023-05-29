# Carcara

Carcara is a proof checker and elaborator for SMT proofs in the [Alethe format](https://verit.gitlabpages.uliege.be/alethe/specification.pdf).

## Building

To build Carcara, you will need Rust and Cargo 1.67 or newer. Build the project with `cargo build`.
When running on large proofs, we recommend compiling with optimizations enabled: `cargo build
--release`.

To build and install Carcara, run `cargo install --profile release-lto --path cli`. This will build
the project with all optimizations enabled, and install the CLI binary in `$HOME/.cargo/bin`.

## Using Carcara
### Checking a proof file

To check a proof file, use the `check` command, passing both the proof file and the original
SMT-LIB problem file.
```
carcara check example.smt2.proof example.smt2
```

If the problem file name is exactly the proof file name minus `.proof`, you can omit it:
```
carcara check example.smt2.proof
```

By default, Carcara will return a checking error when encountering a rule it does not recognize. If
instead you want to ignore such rules, pass the `--skip-unknown-rules` flag.

The `--strict` flag will enable a "strict checking" mode. See the [strict
checking](#strict-checking) section for more details.

See `carcara help check` for more options.

### Proof elaboration

You can elaborate a proof file using the `elaborate` command.
```
carcara elaborate example.smt2.proof example.smt2
```
This command will check the given proof while elaborating it, and print the elaborated proof to
standard output. The `--print-with-sharing` flag controls whether the elaborated proof will be
printed using term sharing.

By default, elaboration of `lia_generic` steps using cvc5 is disabled. To enable it, pass the
`--lia-via-cvc5` flag. You will need to have a working binary of cvc5 in your PATH.

Many of the same flags used in the `check` command also apply to the `elaborate` command. See
`carcara help elaborate` for more details.

### Running benchmarks

The `bench` command is used to run benchmarks. For example, the following command will run a
benchmark on three proof files.

```
carcara bench a.smt2.proof b.smt2.proof c.smt2.proof
```

The command takes as arguments any number of proof files or directories. If a directory is passed,
the benchmark will be run on all `.proof` files in that directory. This command assumes that the
problem file associated with each proof is in the same directory as the proof, and that they follow
the pattern `<filename>.smt2`/`<filename>.smt2.proof`.

The benchmark will parse and check each file, and record performance data. If you pass the
`--elaborate` flag, the proofs will also be elaborated (though the resulting elaborated proof is
discarded).

The benchmark results are simply printed to the screen by default. Instead, if you pass the
`--dump-to-csv` flag, they will be recorded in two csv files, `runs.csv` and `by-rule.csv`.

By default, Carcara will check/elaborate each file only once. You can increase the number of runs
using the `-n`/`--num-runs` option. By default, all benchmarks are run on a single thread. You can
enable multiple threads using the `-j`/`--num-threads` option.

See `carcara help bench` for more options.


## "Strict" checking

Strict checking mode can be enabled by using the `--strict` flag when checking. Currently, this only
affects a few rules.

For the `assume` and `refl` rules, if strict checking is enabled, the implicit reordering of
equalities is not allowed in those steps.

For the `resolution` and `th_resolution` rules, if strict checking is enabled, the steps must
provide the resolution pivots as arguments. The expected format is that, for each binary resolution
step, two arguments must be provided: the pivot used, and a boolean argument indicating whether the
pivot is in the left-hand (`true`) or right-hand (`false`) clause. For example:
```
(step t1 (cl p q) :rule hole)
(step t2 (cl (not q) (not r)) :rule hole)
(step t3 (cl (not s) r) :rule hole)
(step t4 (cl (not (not s))) :rule hole)
(step t5 (cl p) :rule resolution :premises (t1 t2 t3 t4)
     :args (q true r false (not s) true))
```

The intended invariant of strict checking is that any proof that has been elaborated by Carcara can
be checked strictly. Strict checking may also improve perfomance.
