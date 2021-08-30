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

PROBLEM_FILES=$(find test-examples -name '*.smt_in')

echo "starting to generate proofs"

parallel \
    --halt now,fail=1 \
    "$VERIT --proof={}.proof {} &> /dev/null" \
    ::: $PROBLEM_FILES \
    || exit 1

echo "finished generating normal proofs"

parallel \
    --halt now,fail=1 \
    "$VERIT --proof-with-sharing --proof={}.sharing.proof {} &> /dev/null" \
    ::: $PROBLEM_FILES \
    || exit 1

echo "finished generating proofs with sharing"

# These proof files are affected by a bug in veriT that makes some steps
# receive the wrong premises. Because of that, we ignore them in the tests
cd test-examples/simple-tests
for f in unsat-07-sko.smt_in*.proof unsat-06-single-pol-w-exit-sko-min.smt_in*.proof; do
    mv $f $f.ignore
done

# These proof files use a lot of skolemization, which makes them _very_ large
# when not using sharing (around 100 MB or more). This makes testing and
# benchmarking very slow, so we also ignore them. The versions that do use
# sharing have a reasonable size, so we still use them
cd ../SH_problems_all_filtered/isabelle-mirabelle/HOL-Library
for f in smt_cvc4/x2020_07_24_08_31_41_624_5624252.smt_in.proof \
        smt_cvc4/x2020_07_24_08_26_18_466_5418232.smt_in.proof \
        smt_cvc4/x2020_07_24_08_48_06_447_6195044.smt_in.proof \
        smt_cvc4/x2020_07_24_08_47_08_749_6167628.smt_in.proof \
        smt_verit/x2020_07_24_07_33_17_819_7496284.smt_in.proof \
        smt_verit/x2020_07_24_07_20_04_726_6530710.smt_in.proof \
        smt_verit/x2020_07_24_03_43_17_557_8104336.smt_in.proof; do
    mv $f $f.ignore
done
