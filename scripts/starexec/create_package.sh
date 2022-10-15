#!/usr/bin/bash

docker build -t starexec .
cargo clean

RUSTFLAGS="-C target-cpu=sandybridge" cross build \
    --target=x86_64-unknown-linux-gnu \
    --profile release-lto \
    || exit 1

rm -f ./bin/carcara
cp ../../target/x86_64-unknown-linux-gnu/release-lto/carcara ./bin/
tar czf carcara.tar.gz bin starexec_description.txt
