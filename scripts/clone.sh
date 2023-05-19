#!/bin/bash

mkdir -p benchmarks/full

for logic in AUFLIA AUFLIRA QF_ALIA QF_AUFLIA QF_IDL QF_LIA QF_LRA QF_RDL \
    QF_UF QF_UFIDL QF_UFLIA QF_UFLRA UF UFIDL UFLIA UFLRA; do
    if [ ! -d benchmarks/full/$logic ]; then
        git clone --depth 1 \
            https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/$logic.git \
            benchmarks/full/$logic || exit 1
        rm -rf benchmarks/full/$logic/.git
    fi
done
