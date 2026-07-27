#!/bin/bash

# Transpiles to Eunoia problem preludes and corresponding proof certificates,
# contained in $DIR. Uses $COMMAND to invoke 'carcara'.
BENCHMARK="$1"

# Check the value and perform actions
if [ "$BENCHMARK" = "cvc5" ]; then
    DIR="./cvc5_problems"
    # TODO: installation-dependent relative paths
    CARCARA_ELABORATE_COMMAND="../../../../../target/release/carcara elaborate 
                                            --pipeline polyeq local reordering uncrowd
                                            --expand-let-bindings 
                                            --pipeline=local 
                                            --no-print-with-sharing 
                                            --ignore-unknown-rules
                                            --allow-int-real-subtyping                      
                                            --rare-file ./alethe_signature/rules/rare_rules.rare"
else
    DIR="./verit_problems"
    # TODO: installation-dependent relative paths
    CARCARA_ELABORATE_COMMAND="../../../../../target/release/carcara elaborate 
                                            --pipeline polyeq local uncrowd reordering 
                                            --no-print-with-sharing 
                                            --ignore-unknown-rules
                                            --allow-int-real-subtyping                  
                                            --rare-file ./alethe_signature/rules/rare_rules.rare"
fi

CARCARA_TRANSLATE_COMMAND="../../../../../target/release/carcara translate eunoia"
ETHOS_COMMAND="../../../../../../ethos_fork/ethos/build/src/ethos"

# Loop through each file in the directory.
for PROBLEM in "$DIR"/*; do
    # Check if it's a regular file
    if [ -f "$PROBLEM" ]; then
        # Extract the file extension
        EXTENSION="${PROBLEM##*.}"

        # Check if the file has the .smt2 extension
        if [ "$EXTENSION" == "smt2" ]; then
            # Proof certificate's name
            PROOF_CERTIFICATE="${PROBLEM}_proof_certificate"

            EUNOIA_OUTPUT="${PROBLEM}.eo"
            echo "----------------------"
            echo "About to process $PROBLEM"
            
            # Elaborate proof certificate first.
            # Remove the "valid"/"holey" word from the beginning of the file
            ${CARCARA_ELABORATE_COMMAND} "$PROOF_CERTIFICATE" "$PROBLEM" | tail -n +2 > "${PROOF_CERTIFICATE}_elaborated"

            # Use Carcara to transpile to Eunoia, redirect the output to 
            # "$EUNOIA_OUTPUT" 
            ${CARCARA_TRANSLATE_COMMAND} "${PROOF_CERTIFICATE}_elaborated" "$PROBLEM" "--allow-int-real-subtyping" > "$EUNOIA_OUTPUT"

            # Check the return code of Carcara
            if [ $? -eq 0 ]; then
                ${ETHOS_COMMAND} "$EUNOIA_OUTPUT"
                if [ $? -eq 0 ]; then
                    # Print a success message
                    echo "Successfully processed $PROBLEM and saved output to $EUNOIA_OUTPUT"
                    echo ""
                else
                    # rm "$EUNOIA_OUTPUT"
                    echo "Ethos failed on file $EUNOIA_OUTPUT"
                    echo ""
                fi
            else
                rm "$EUNOIA_OUTPUT"
                echo "Carcara failed on file $PROBLEM"
                echo ""
            fi
        fi
    fi
done
