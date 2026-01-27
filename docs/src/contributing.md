# Contributing

While Carcara is actively maintained by the folks at the SMITE research group at Universidade
Federal de Minas Gerais (UFMG), we gladly welcome external contributions.

If you wish to contribute to the project, please do so by opening a [pull request via
GitHub](https://github.com/ufmg-smite/carcara/pulls).

## Guidelines

In this project, we use [Clippy](https://github.com/rust-lang/rust-clippy) as a linter and
[Rustfmt](https://github.com/rust-lang/rustfmt) for code formatting. If you manage your Rust
toolchain using Rustup, you can install Clippy and Rustfmt by running:
```
rustup component add clippy rustfmt
```

Once they're installed, you can run `cargo fmt` to format your code according to the project
guidelines, or `cargo clippy` to detect possible problems using Clippy. You may also run `cargo
clippy --fix` to let Clippy try to automatically fix the detected issues.

When opening a pull request, make sure that your code compiles without warnings, and is formatted
with Rustfmt. Run `cargo test` to ensure your changes do not break any existing behaviour.
Additionally, we strive to support Rust versions as old as 1.87---please refrain from using features
introduced in newer versions of Rust.
