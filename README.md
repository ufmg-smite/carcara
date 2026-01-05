# Carcara
Carcara is a proof checker and elaborator for SMT proofs in the [Alethe
format](https://verit.gitlabpages.uliege.be/alethe/specification.pdf).
A research paper describing Carcara has been [published at TACAS
2023](https://link.springer.com/chapter/10.1007/978-3-031-30823-9_19).

## Installation
To build Carcara, you will need Rust and Cargo 1.87 or newer. You can download and install the
latest version of Carcara by running:
```
cargo install --git https://github.com/ufmg-smite/carcara.git
```
This will build the project and place the `carcara` binary in Cargo's binary directory
(`~/.cargo/bin` by default).

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
