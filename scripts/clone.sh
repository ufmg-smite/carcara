#!/bin/bash

mkdir -p benchmarks/full

cd benchmarks || exit 1

for logic in AUFLIA AUFLIRA QF_ALIA QF_AUFLIA QF_IDL QF_LIA QF_LRA QF_RDL \
    QF_UF QF_UFIDL QF_UFLIA QF_UFLRA UF UFIDL UFLIA UFLRA; do
    if [ ! -d full/$logic ]; then
        curl "https://zenodo.org/records/11061097/files/${logic}.tar.zst" \
            | tar --zstd -x -C full --strip-components 1
    fi
done
