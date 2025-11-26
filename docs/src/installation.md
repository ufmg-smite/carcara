# Installation
## Building from source
To build Carcara from source, you will first need to install Rust and Cargo. Currently, Carcara
requires at least Rust version 1.87. Once you have installed an appropriate version of Rust, you can
download and install the latest version of Carcara by running the following command:
```
cargo install --git https://github.com/ufmg-smite/carcara.git
```
This will build the project and place the `carcara` binary in Cargo's binary directory
(`~/.cargo/bin` by default).

You can uninstall Carcara by running `cargo uninstall carcara-cli`.

## Pre-built binary
Alternatively, a pre-compiled executable for the `x86_64-unknown-linux-gnu` platform can be
downloaded from the [GitHub releases page](https://github.com/ufmg-smite/carcara/releases). To use
Carcara in other platforms or operating systems, or to use a more recent version of Carcara, we
recommend building from source.
