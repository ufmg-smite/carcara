# Carcara
Carcara is a proof checker and elaborator for SMT proofs in the [Alethe
format](https://verit.gitlabpages.uliege.be/alethe/specification.pdf).
A research paper describing Carcara has been [published at TACAS
2023](https://link.springer.com/chapter/10.1007/978-3-031-30823-9_19).

## Installation
To build Carcara, you will need Rust and Cargo 1.87 or newer. Clone this repository and build the
project by running `cargo build --release`. You may also run `cargo install --path cli` to build and
place the `carcara` binary in Cargo's binary directory (`~/.cargo/bin` by default).

Alternatively, you can install Carcara directly (without cloning this repository) by running:
```
cargo install --git https://github.com/ufmg-smite/carcara.git
```

## Usage
To check a proof file with Carcara, use the `check` command, passing both the proof file and the
original SMT-LIB problem file:
```
carcara check example.smt2.alethe example.smt2
```

Besides checking a proof, Carcara is also capable of _proof elaboration_. You can elaborate a proof
file using the `elaborate` command:
```
carcara elaborate example.smt2.alethe example.smt2
```

For more information, see the [full documentation](https://ufmg-smite.github.io/carcara).
