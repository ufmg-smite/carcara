# veriT Proof Checker

### Building and running

Build the project with `cargo build`. To build and run the built binary, use `cargo run -- [ARGS]`.
See `--help` for a detailed list of arguments and subcommands.

### Running tests

First, unzip the test examples with `unzip -q test-examples.zip`. Then run `cargo test` to run all
unit and integration tests.

### Progress report

You can run a progress report with the `progress-report` subcommand. For example, running

```
cargo run --release -q -- progress-report -r $(find test-examples -name '*.proof')
```

will report which rules are implemented, of all rules used in the test examples. See
`verit-proof-checker progress-report --help` for more details.
