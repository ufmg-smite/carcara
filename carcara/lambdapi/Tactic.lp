// define a type representing Lambdapi tactics

require open Stdlib.Set Stdlib.Prop Stdlib.Nat Stdlib.Eq Stdlib.List;
require open lambdapi.Classic lambdapi.Alethe;

constant symbol String : TYPE;
builtin "String" ≔ String;

constant symbol string : Set;
rule τ string ↪ String;


constant symbol Tactic : TYPE;

constant symbol #admit : Tactic;
builtin "admit" ≔ #admit;

symbol & : Tactic → Tactic → Tactic;
builtin "and" ≔ &;
notation & infix right 10;


constant symbol #apply [p] : πᶜ p → Tactic;
builtin "apply" ≔ #apply;

constant symbol #assume : τ (list string) → Tactic;
builtin "assume" ≔ #assume;

constant symbol #fail : Tactic;
builtin "fail" ≔ #fail;

constant symbol #generalize : Π [a], τ a → Tactic;
builtin "generalize" ≔ #generalize;

constant symbol #have : String → Π p, πᶜ p → Tactic;
builtin "have" ≔ #have;

constant symbol #induction : Tactic;
builtin "induction" ≔ #induction;

constant symbol #orelse : Tactic → Tactic → Tactic;
builtin "orelse" ≔ #orelse;

constant symbol #refine [p] : πᶜ p → Tactic;
builtin "refine" ≔ #refine;

constant symbol #reflexivity : Tactic;
builtin "reflexivity" ≔ #reflexivity;

constant symbol #remove : Π [a], πᶜ a → Tactic;
builtin "remove" ≔ #remove;

constant symbol #repeat : Tactic → Tactic;
builtin "repeat" ≔ #repeat;

constant symbol #rewrite [p] : πᶜ p → Tactic;
builtin "rewrite" ≔ #rewrite;

constant symbol #set : String → Π [a], τ a → Tactic;
builtin "set" ≔ #set;

constant symbol #simplify : /* Π [a], τ a → */ Tactic;
builtin "simplify" ≔ #simplify;

constant symbol #solve : Tactic;
builtin "solve" ≔ #solve;

constant symbol #symmetry : Tactic;
builtin "symmetry" ≔ #symmetry;

constant symbol #try : Tactic → Tactic;
builtin "try" ≔ #try;

constant symbol #why3 : /*τ (option string) →*/ Tactic;
builtin "why3" ≔ #why3;

////////////////////////////////// Tactic script defined //////////////

symbol nothing ≔ #try #fail;

symbol do : ℕ → Tactic → Tactic;

rule do 0 _ ↪ nothing
with do ($n +1) $t ↪ $t & (do $n $t);

symbol addnAC x y z : πᶜ ((x + y) + z = x + (y + z));

private symbol lemma x y z t : πᶜ (((x + y) + z) + t = x + (y + (z + t))) ≔
begin
  assume x y z t;
  eval do 2 (#rewrite addnAC); reflexivity
end;
