#!/bin/bash

timeout $timeout $VERIT $1 \
    --proof=$1.verit.alethe --proof-with-sharing \
    --proof-prune --proof-merge &> /dev/null

timeout $timeout $CVC5 $1 \
    --produce-proofs --dump-proofs \
    --proof-format-mode=alethe --proof-granularity=theory-rewrite \
    --proof-alethe-res-pivots --proof-elim-subtypes --print-arith-lit-token \
    > $1.cvc5.alethe 2> /dev/null

# If a complete proof could not be generated, we delete it
for proof in "$1.verit.alethe" "$1.cvc5.alethe"; do
    if [ -f $proof ]; then
        if ! grep -q -F '(cl)' $proof; then
            rm $proof
            exit
        fi
    fi
done
