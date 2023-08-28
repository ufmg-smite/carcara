#!/bin/bash

timeout $timeout $VERIT $1 \
    --proof=$1.alethe --proof-with-sharing \
    --proof-prune --proof-merge &> /dev/null

# If a complete proof could not be generated, we delete it
if [ -f $1.alethe ]; then
    if ! grep -q -F '(cl)' $1.alethe; then
        rm $1.alethe
        exit
    fi
fi
