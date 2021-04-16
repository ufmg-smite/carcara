#!/usr/bin/sh
if [ $# = 0 ] || [ $1 = "--help" ] || [ $1 = "-h" ]; then
    echo "Usage: $0 [PROOF]..."
    exit
fi

cargo build --release 2> /dev/null
TEMPFILE=$(mktemp)

for f in $@; do
    ./target/release/verit-proof-checker --print-used-rules "$f" >> $TEMPFILE
done

TOTAL=0
IMPLEMENTED=0

while read rule; do
    RESULT=$(./target/release/verit-proof-checker --is-rule-implemented "$rule")
    if [ $RESULT = "true" ]; then
        let IMPLEMENTED++
        echo -e "\e[1;32m$rule"
    else
        echo -e "\e[0;31m$rule"
    fi
    let TOTAL++
done < <(sort $TEMPFILE | uniq)
echo -e "\e[0;37m$IMPLEMENTED / $TOTAL rules implemented"
rm $TEMPFILE
