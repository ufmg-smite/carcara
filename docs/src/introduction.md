# Introduction
Carcara is an independent proof checker and elaborator for SMT proofs in the [Alethe
format](https://verit.gitlabpages.uliege.be/alethe/specification.pdf), with a focus on performance
and usability. It can efficiently check Alethe proofs even in the presence of coarse-grained steps,
and reports detailed error messages in the case that the proof is invalid. Besides checking, Carcara
is capable of _elaborating_ proofs, by adding ommited detail and breaking down hard-to-check steps
into multiple simpler steps.

This project was developed in the SMITE research group, at Universidade Federal de
Minas Gerais (UFMG). A research paper describing Carcara has been [published at TACAS
2023](https://link.springer.com/chapter/10.1007/978-3-031-30823-9_19).

## License
The Carcara source code and documentation are released under the [Apache License, version
2.0](https://www.apache.org/licenses/LICENSE-2.0.html).
