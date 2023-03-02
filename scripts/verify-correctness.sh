#!/usr/bin/env bash
# Verifies the correctness of the concurrent implementation of carcara comparing
#  the result generated by the single thread execution and a parallel execution.
# Receives two arguments:
#  1st: the carcará original version directory path
#  2nd: the directory path that contains the files to be tested

CARCARA=$(realpath $1)
DIR=$(realpath $2)
cur_dir=$(realpath $(dirname ${BASH_SOURCE[0]}))/..

echo "";
cd $cur_dir
global_count=0

for dir in $(find $DIR -maxdepth 6 -type d); do
    echo $'\e[1;34m'$dir$':\e[0m'

    count=0
    for FILE in $dir/*.smt_in; do
        cd $CARCARA
        RESULT1=$(cargo run --quiet -- check --skip-unknown-rules "$FILE.proof" "$FILE" &)
        cd $cur_dir
        RESULT2=$(cargo run --quiet --features thread-safety -- check --skip-unknown-rules -u 3 "$FILE.proof" "$FILE" &)
        echo "$(echo $RESULT1 | tr '\a' ' ') $(echo $RESULT2 | tr '\a' ' ')"
        RESULT1=$(echo $RESULT1 | tr '\a' ' ' | awk '{print $NF}')
        RESULT2=$(echo $RESULT2 | tr '\a' ' ' | awk '{print $NF}')

        if [ "$RESULT1" == "" ] || [ "$RESULT2" == "" ]; then
            echo;
            echo $'\e[1;31mPanicked at '$(basename $FILE)$'\e[0m';
            echo;
            exit 0;
        fi

        DIF="EQUAL"
        if [ "$RESULT1" != "$RESULT2" ]; then
            DIF="DIF"
            ((count = count + 1))
            ((global_count = global_count + 1))
            echo $''$(basename $FILE)$': '$RESULT1$' is \e[1;31m'$DIF$'\e[0m from '$RESULT2$'';
        else
            echo $''$(basename $FILE)$': '$RESULT1$' is \e[1;32m'$DIF$'\e[0m from '$RESULT2$'';
        fi
    done
    
    echo $'Difference count: \e[1;33m'$count$'\e[0m';
    echo;
done

echo;
echo $'Global count: \e[1;33m'$global_count$'\e[0m';