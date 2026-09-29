# Contributing

While Carcara is actively maintained by the folks at the SMITE research group at Universidade
Federal de Minas Gerais (UFMG), we gladly welcome external contributions.

If you wish to contribute to the project, please do so by opening a [pull request via
GitHub](https://github.com/ufmg-smite/carcara/pulls).

## Code guidelines

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
Additionally, we strive to support Rust versions as old as 1.93---please refrain from using features
introduced in newer versions of Rust.

## LLM usage policy

The usage of LLMs when contributing to Carcara is allowed, with certain limitations. In particular:

1. Using LLMs to create code is generally **not** allowed, with the exception of very trivial code
changes (fixing typos, renaming symbols, etc).
2. You **may** use LLMs to analyze code, review, give suggestions, or any other uses where you are the
only one who sees the output.
3. You **may not**  use LLMs to generate text in order to communicate with others. This includes
in-code comments, documentation, PR or issue descriptions, and commit messages.

These guidelines are intentionally somewhat vague, and specific cases are left to the maintainers'
discretion. Above all, we incentivize honestly disclosing your usage, and approaching in good faith.
