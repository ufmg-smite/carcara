#!/usr/bin/env bash
# Verifies the correctness of the concurrent implementation of carcara comparing
#  the result generated by the single thread execution and a parallel execution.
# Receives a single argument that is the directory path that contains the files 
#  to be used in the test

DIR=$1

aaa=$(pwd);
FULL_DIR="$aaa/$DIR";
echo $FULL_DIR;
cd $FULL_DIR
count=0

for FILE in *.smt_in; do
    RESULT1=$(cargo run -- check --skip-unknown-rules "$FILE.proof" "$FILE" 2>/dev/null);
    RESULT2=$(cargo run -- check --skip-unknown-rules -u 3 "$FILE.proof" "$FILE" 2>/dev/null);
    
    DIF="EQUAL"
    if [ $RESULT1 != $RESULT2 ] 
    then
        DIF="DIF"
        count = count + 1
    fi

    echo "$FILE: $RESULT1 is $DIF";
done

echo;
echo "Different count: $count";