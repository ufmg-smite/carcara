#!/usr/bin/bash
# Generates proofs for all problems in the "test-examples" directory. This
# generates two proofs for each problem -- one that uses sharing, and one that
# does not. If the problem path is "problem.smt_in", the proofs will be in
# "problem.smt_in.sharing.proof" and "problem.smt_in.proof"

if [[ -z "$VERIT" ]]; then
    echo "\$VERIT environment variable is not defined, using 'veriT' as default value"
    VERIT='veriT'
fi

if [ ! -d "test-examples" ]; then
    echo "'test-examples' directory not found, trying to unzip 'test-examples.zip'"
    unzip -q test-examples.zip || exit 1
fi

echo "starting to generate proofs"
find -name '*.smt_in' | parallel --halt now,fail=1 "$VERIT --proof={}.proof {} &> /dev/null"
echo "finished generating normal proofs"
find -name '*.smt_in' | parallel --halt now,fail=1 "$VERIT --proof-with-sharing --proof={}.sharing.proof {} &> /dev/null"
echo "finished generating proofs with sharing"

# These proof files are affected by a bug in veriT that makes some steps
# receive the wrong premises. Because of that, we ignore them in the tests
cd test-examples/simple-tests
for f in unsat-07-sko.smt_in*.proof unsat-06-single-pol-w-exit-sko-min.smt_in*.proof; do
    mv $f $f.ignore
done
