
require open Stdlib.Prop;
require open Stdlib.FOL;
require open Stdlib.Eq;
require open Stdlib.Set;
require open Stdlib.Z;
require open Stdlib.Pos;
require open Stdlib.Bool;
require open lambdapi.Classic;
require open lambdapi.Alethe;

constant symbol Ring : TYPE;
symbol ring : Set;
rule τ ring ↪ Ring;

right associative commutative symbol add : Ring → Ring → Ring;
constant symbol Z : Ring;
symbol const [a]: τ a → Ring;

symbol mul [a] : τ a → τ a → Ring;

symbol ≥? : τ ring → τ ring → 𝔹; notation ≥? infix 10;
symbol >? : τ ring → τ ring → 𝔹; notation >? infix 10;

sequential symbol reify [a] : τ a → Ring;