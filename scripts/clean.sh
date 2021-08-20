#!/usr/bin/bash

mkdir -p output && cd output || exit 1

logics="AUFLIA AUFLIRA QF_ALIA QF_AUFLIA QF_IDL QF_LIA QF_LRA QF_RDL QF_UF
    QF_UFIDL QF_UFLIA QF_UFLRA UF UFIDL UFLIA UFLRA"

for l in $logics; do
    # If there is a repository missing, try to clone it
    if [ ! -d $l ]; then
        git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/$l.git || exit 1
        rm -rf ./$l/.git
        rm ./$l/README.md
    fi
done

cd ..

if [ ! -d veriT-proofs ]; then
    echo "couldn't find 'veriT-proofs' directory, exiting"
    exit 1
fi

cd veriT-proofs

all_instances=$(find -name '*.smt2' -type d)
total=$(echo $all_instances | wc -w)
count=0

echo "starting to clean proofs"
echo -ne "[0 / $total]\r"
for f in $all_instances; do
    problem_path=../output/${f/non_incremental_/}

    if [ -f $problem_path ]; then
        # Delete every line in the `output.log` file until the line "unsat",
        # and put that in the proof file. If the problem is not "unsat", this
        # will delete every line, and the proof will be considered incomplete
        # in the next step, and will be removed
        sed '0,/^unsat$/d' $f/output.log > $problem_path.proof

        if ! grep -q '(cl)' $problem_path.proof; then
            # If the proof is incomplete, delete both the proof and the
            # original problem
            rm -f $problem_path $problem_path.proof
        else
            # Move the `run.out` file to the output directory, in case we need
            # it later
            cp $f/run.out $problem_path.run.out
        fi
    fi

    count=$(( $count + 1 ))
    echo -ne "[$count / $total]\r"
done

echo
echo "done!"
