#!/usr/bin/bash

docker build -t starexec .
cargo clean

RUSTFLAGS="-C target-cpu=sandybridge" cross build \
    --target=x86_64-unknown-linux-gnu \
    --profile release-lto \
    || exit 1

rm -f ./bin/alethe-proof-checker
cp ../../target/x86_64-unknown-linux-gnu/release-lto/alethe-proof-checker ./bin/
tar czf alethe-proof-checker.tar.gz bin starexec_description.txt
