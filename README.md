# Carcará

Carcará is a proof checker and elaborator for SMT proofs in the Alethe format.

### Building and running

Build the project with `cargo build`. To build and run the built binary, use `cargo run -- [ARGS]`.
For example, you can check a proof file using `cargo run -- check <proof file> <problem file>`,
where `<proof file>` is the file name of the proof in the Alethe format, and `<problem file>` is the
original problem file in SMT-LIB format. You can omit the problem file name, and the checker will
try to infer it from the proof file name.

If the proof file is large, we recommend using the `--release` flag in `cargo` to turn on all
optimizations:

```
$ cargo run --release -- check <proof file> <problem file>
```

Note that arguments passed before the `--` are considered arguments for `cargo`, while arguments
after the `--` are arguments for the checker itself.

See `cargo run -- help` for a detailed list of arguments and subcommands.

### Running tests

You can use the `generate-examples.sh` script to generate the test examples using veriT. The script
uses the `VERIT` environment variable to determine the location of the veriT binary.

```
$ VERIT=/path/to/veriT scripts/generate-examples.sh
```

After generating the test examples, run `cargo test --release` to run all unit and integration
tests.

### Running benchmarks

The `bench` subcommand is used to run benchmarks. For example, this command will run a benchmark on
all proof files in the `test-examples/simple-tests` directory, doing 50 runs on each file:

```
$ cargo run --release -- bench -n 50 test-examples/simple-tests
```
