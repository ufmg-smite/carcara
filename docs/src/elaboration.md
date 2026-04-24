# Proof elaboration
Besides checking a proof, Carcara is also capable of _proof elaboration_. You can elaborate a proof
file using the `elaborate` command:
```
carcara elaborate example.smt2.alethe example.smt2
```

This will check and elaborate the given proof, and print the elaborated proof to the standard
output. By default, Carcara will print proofs using term sharing, i.e., using the `(! ... :named
...)` syntax. You can change this behavior with the `--no-print-with-sharing`/`-v` option.

Many of the same options used in the `check` command also apply to the `elaborate` command. See
`carcara elaborate --help` for more details.

## Elaboration pipeline
The specific way in which Carcara elaborates the proof is controlled via a `--pipeline` option.
This takes a series of _elaboration passes_, and will apply them in the given order. The possible
elaboration passes are:
- [`polyeq`](./elaboration/polyeq.md)
- [`lia-generic`]()
- [`local`](./elaboration/local.md)
- [`uncrowd`]()
- [`reordering`]()
- [`hole`]()

By default, Carcara will attempt to apply all of these in the listed order.

### Example
The following command will elaborate the given proof file with the `uncrowd` and `polyeq`
elaboration passes, in that order:
```
carcara elaborate example.smt2.alethe --pipeline uncrowd polyeq
```
Note that, if you pass a positional argument (e.g. the proof filename) after the pipeline argument,
you need an extra `--` argument to denote the end of the pipeline list:
```
carcara elaborate --pipeline uncrowd polyeq -- example.smt2.alethe
```
