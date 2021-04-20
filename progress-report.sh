#!/usr/bin/sh

usage="Usage:
    $0 [COMMAND] [FILES]...

Commands:
    -h, --help      Show this message.
    -r, --rules     Count how many of the rules present in the given files are implemented.
    -f, --files     Count how many of the given files have all rules implemented."

if [ $# = 0 ] || [ $1 = "--help" ] || [ $1 = "-h" ]; then
    echo "$usage"
    exit
fi

TEMPFILE=$(mktemp)
TOTAL=0
IMPLEMENTED=0

if [ $1 = "--files" ] || [ $1 = "-f" ]; then
    cargo build --release 2> /dev/null
    for f in ${@:2}; do
        ./target/release/verit-proof-checker --print-used-rules "$f" > $TEMPFILE
        sort --unique $TEMPFILE -o $TEMPFILE

        ALL_IMPLEMENTED=true
        while read rule; do
            RESULT=$(./target/release/verit-proof-checker --is-rule-implemented "$rule")
            if [ $RESULT = "false" ]; then
                ALL_IMPLEMENTED=$(false)
                break
            fi
        done < $TEMPFILE

        if [ $ALL_IMPLEMENTED ]; then
            let IMPLEMENTED++
            echo -e "\e[1;32m$f"
        else
            echo -e "\e[0;31m$f"
        fi
        let TOTAL++
    done

    echo -e "\e[0;37m$IMPLEMENTED / $TOTAL files with all rules implemented"
elif [ $1 = "--rules" ] || [ $1 = "-r" ]; then
    cargo build --release 2> /dev/null
    for f in ${@:2}; do
        ./target/release/verit-proof-checker --print-used-rules "$f" >> $TEMPFILE
    done
    sort --unique $TEMPFILE -o $TEMPFILE

    while read rule; do
        RESULT=$(./target/release/verit-proof-checker --is-rule-implemented "$rule")
        if [ $RESULT = "true" ]; then
            let IMPLEMENTED++
            echo -e "\e[1;32m$rule"
        else
            echo -e "\e[0;31m$rule"
        fi
        let TOTAL++
    done < $TEMPFILE

    echo -e "\e[0;37m$IMPLEMENTED / $TOTAL rules implemented"
else
    echo "$usage"
fi

rm $TEMPFILE
