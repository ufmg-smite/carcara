# Carcará

Carcará is a proof checker and elaborator for SMT proofs in the Alethe format.

### Building and running

Carcará requires Rust 1.67 or newer. Build the project with `cargo build`. To build and run the
built binary, use `cargo run -- [ARGS]`. For example, you can check a proof file using `cargo run --
check <proof file> <problem file>`, where `<proof file>` is the file name of the proof in the Alethe
format, and `<problem file>` is the original problem file in SMT-LIB format. You can also omit the
problem file name, and the checker will try to infer it from the proof file name.

If the proof file is large, we recommend using the `--release` flag in `cargo` to turn on all
optimizations:

```
$ cargo run --release -- check <proof file> <problem file>
```

Note that arguments passed before the `--` are considered arguments for `cargo`, while arguments
after the `--` are arguments for the checker itself.

See `cargo run -- help` for a detailed list of arguments and subcommands.

### Running tests

You can use the `scripts/generate-benchmarks.sh` script to generate test benchmarks using veriT. See
`scripts/generate-benchmarks.sh --help` for usage details. After generating the benchmarks, run
`cargo test --release` to run all unit and integration tests.
