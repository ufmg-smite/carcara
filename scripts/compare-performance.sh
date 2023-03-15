#!/usr/bin/env bash
# Compares the performance between the original single thread carcará and the multithread version
# Receives two arguments:
#  1st: the carcará original version directory path
#  2nd: the .smt_in file path
#  3rd: number of times to execute a single proof check. $3 >= 1

CARCARA=$(realpath $1)
DIR=$(realpath $2)
cur_dir=$(realpath $(dirname ${BASH_SOURCE[0]}))/..
FILE=$2

cd $cur_dir
echo "AAAA"
for i in seq 1 $3; do
    RESULT1=$(cargo run --quiet --release -- check --skip-unknown-rules "$FILE.proof" "$FILE" )
    # 2>/dev/null
    echo $RESULT1
done

cd $cur_dir
echo "bbbb"
for i in seq 1 $3; do
    RESULT2=$(cargo run --quiet --release --features thread-safety -- check --skip-unknown-rules -u 3 "$FILE.proof" "$FILE" 2>/dev/null)
    echo $RESULT2
done