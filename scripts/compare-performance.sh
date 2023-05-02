#!/usr/bin/env bash
# Compares the performance between the original single thread carcará and the multithread version
# Receives two arguments:
#  1st: the .smt_in file path
#  2nd: the proof folder path (without a final /)
#  3rd: number of times to execute a single proof check. $3 >= 1

DIR=$(realpath $1)
PROOF_FOLDER=$2
cur_dir=$(realpath $(realpath $(dirname ${BASH_SOURCE[0]}))/..)
FILE=$1
FILE_NAME=$(basename $(realpath $FILE))

# Defines stack size (128 * 1024 * 1024) for deep and big proofs
ulimit -s 134217728

cd $cur_dir
for i in $(seq 1 $3); do
    RESULT1=$(cargo run --quiet --profile release-with-debug -- check --stats --skip-unknown-rules "$PROOF_FOLDER/$FILE_NAME.proof" "$FILE" 2>/dev/null)
    echo "$RESULT1"
done

echo "";

cd $cur_dir
for i in $(seq 1 $3); do
    RESULT2=$(cargo run --quiet   --profile release-with-debug --features thread-safety -- check  --stats  --skip-unknown-rules -u 3 "$PROOF_FOLDER/$FILE_NAME.proof" "$FILE" 2>/dev/null)
    echo "$RESULT2"
done