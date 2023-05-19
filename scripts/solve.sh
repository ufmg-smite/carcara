#!/bin/bash

timeout $timeout $VERIT $1 \
    --proof-file-from-input --proof-with-sharing \
    --proof-prune --proof-merge &> /dev/null

# If a complete proof could not be generated, we delete it
if [ -f $1.proof ]; then
    if ! grep -q -F '(cl)' $1.proof; then
        rm $1.proof
        exit
    fi
fi
