require open Stdlib.Z Stdlib.Rat;



symbol ⨥ [a]: τ a → τ a → τ a;
notation ⨥ infix right 20;

print Stdlib.Z.+;

rule @⨥ nat $x $y ↪ $x Stdlib.Nat.+ $y;
rule @⨥ int $x $y ↪ $x Stdlib.Z.+ $y;
rule @⨥ rat $x $y ↪ $x q+ $y;


symbol ⨱ [a]: τ a → τ a → τ a;
notation ⨱ infix right 22;

print Stdlib.Z.*;

rule @⨱ nat $x $y ↪ $x Stdlib.Nat.* $y;
rule @⨱ int $x $y ↪ $x Stdlib.Z.* $y;
rule @⨱ rat $x $y ↪ $x q* $y;

symbol ⨪ [a]: τ a → τ a → τ a;
notation ⨪ infix left 20;

print Stdlib.Z.-;

rule @⨪ nat $x $y ↪ $x Stdlib.Nat.- $y;
rule @⨪ int $x $y ↪ $x Stdlib.Z.- $y;
rule @⨪ rat $x $y ↪ $x q- $y;

symbol ~ [a]: τ a → τ a;
notation ~ prefix 24;

print Stdlib.Z.—;

rule @~ int $x ↪ Stdlib.Z.— $x;
rule @~ rat $x ↪ q~ $x;