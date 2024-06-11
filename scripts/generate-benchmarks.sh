#!/bin/bash

function usage() {
    cat <<-EOF
Generates benchmarks for testing Carcara, using veriT and cvc5.

By default, this script looks for veriT and cvc5 in your \$PATH, but you can
override this by setting the \$VERIT and \$CVC5 environment variables.

USAGE:
    generate-benchmarks.sh [OPTIONS]

OPTIONS:
    -h, --help      Show this mesage.
    --full          Download and solve all benchmarks from the SMT-LIB
                    repositories. This may take a very long time.
    --clean         After running, remove all .smt2 files for which a proof
                    could not be generated.
    -t <timeout>    The time limit to solve each problem. (default: 10s)
    -j <jobs>       Maximum number of jobs to use. (default: number of CPUs)
EOF
}

benchmark_dir="benchmarks/small"
timeout="10s"
num_jobs="$(nproc)"
clean_flag=""

while [ $# -gt 0 ]; do
    case "$1" in
        -h | --help)
            usage
            exit 0
            ;;
        --full) benchmark_dir="benchmarks" ;;
        --clean) clean_flag="true" ;;
        -j)
            if [ "$#" -lt 2 ]; then
                echo "missing argument value"
                exit 1
            fi
            num_jobs="$2"
            shift
            ;;
        -t)
            if [ "$#" -lt 2 ]; then
                echo "missing argument value"
                exit 1
            fi
            timeout="$2"
            shift
            ;;
        *)
            echo "invalid argument: '$1'"
            echo
            usage
            exit 1
            ;;
    esac
    shift
done

export timeout

if [ -z "$VERIT" ]; then
    if ! command -v veriT &> /dev/null; then
        echo "veriT not found"
        echo "make sure that it is in your \$PATH, or that the \$VERIT environment variable is set"
        exit 1
    fi
    export VERIT="veriT"
fi

if [ -z "$CVC5" ]; then
    if ! command -v cvc5 &> /dev/null; then
        echo "cvc5 not found"
        echo "make sure that it is in your \$PATH, or that the \$CVC5 environment variable is set"
        exit 1
    fi
    export CVC5="cvc5"
fi

if [ ! -d "benchmarks/small" ]; then
    echo "creating small benchmarks set..."
    unzip -q benchmarks.zip || exit 1
fi

if [ "$benchmark_dir" = "benchmarks" ]; then
    echo "WARNING: running on the full benchmark set. This may take a while."
    echo "cloning benchmark repositories..."
    bash scripts/clone.sh || exit 1
fi

echo "generating proofs..."
find $benchmark_dir -name '*.smt2' | xargs -P $num_jobs -n 1 bash -c 'scripts/solve.sh $0'

if [ -n "clean_flag" ]; then
    echo "cleaning up..."
    for f in $(find $benchmark_dir -name '*.smt2'); do
        if [ ! -f $f.verit.alethe ] && [ ! -f $f.cvc5.alethe ]; then
            rm -f $f
        fi
    done
fi

echo "done :)"
