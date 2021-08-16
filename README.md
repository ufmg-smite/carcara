# veriT Proof Checker

### Building and running

Build the project with `cargo build`. To build and run the built binary, use `cargo run -- [ARGS]`.
See `--help` for a detailed list of arguments and subcommands.

### Running tests

You can use the `generate-examples.sh` script to generate the test examples using veriT. The script
uses the `VERIT` environment variable to determine the location of the veriT binary.

```
$ VERIT=/path/to/veriT ./generate-examples.sh
```

After generating the test examples, run `cargo test --release` to run all unit and integration tests.

### Running benchmarks

The `bench` subcommand is used to run benchmarks. For example, this command will run a benchmark on
all proof files in the `test-examples/simple-tests` directory, doing 50 runs on each file:

```
$ cargo run --release -q -- bench -n 50 $(find test-examples/simple-tests -name '*.proof')
```

### Progress report

You can run a progress report with the `progress-report` subcommand. For example, running

```
$ cargo run --release -q -- progress-report -r $(find test-examples -name '*.proof')
```

will report which rules are implemented, of all rules used in the test examples. See
`verit-proof-checker progress-report --help` for more details.
