# Proof parsing/printing
You can use the `carcara parse` command to parse a proof file and print it back to standard output.
This can be used to validate if a proof is syntactically valid without checking any proof steps, or
to print the proof with some syntactical transformation applied.

## Adding/removing term sharing 
When printing a proof, Carcara automatically adds term sharing (i.e., the `(! ... :named ...)`
syntax). If you parse a proof that does not make use of term sharing with `carcara parse`, it will
by default be printed with term sharing added. Alternatively, you can remove term sharing from a
proof that uses it by passing the `--no-print-with-sharing`/`-v` option.

## Expanding `let` terms
You can use the `--expand-let-bindings` option to remove all `let` terms from the proof by inlining all attributed values. For example, the term
```
(let ((x 1)) (let ((y (+ x 2))) (+ y 3)))
```
will be expanded into
```
(+ (+ 1 2) 3)
```
