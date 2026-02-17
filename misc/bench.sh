#!/usr/bin/env bash
set -euo pipefail

CPU=1
RUNS=50

RLSF_DIR="$HOME/bench/rlsf"
VERUS_DIR="$HOME/bench/rlsf_verus"

BINARY_NAME="bench"

OUTDIR="results_$(date +%Y%m%d_%H%M%S)"
mkdir -p "$OUTDIR"

echo "[*] Checking CPU governor..."
cpupower frequency-info | grep "performance" || {
    echo "WARNING: governor is not performance"
}

echo "[*] THP status:"
cat /sys/kernel/mm/transparent_hugepage/enabled

echo "[*] ASLR status:"
cat /proc/sys/kernel/randomize_va_space

build_project () {
    DIR=$1
    echo "[*] Building in $DIR"
    cd "$DIR"
    RUSTFLAGS="-C target-cpu=native -C lto" cargo build --release
}

build_project "$RLSF_DIR"
build_project "$VERUS_DIR"

run_bench () {
    NAME=$1
    DIR=$2

    cd "$DIR"
    BIN="target/release/$BINARY_NAME"

    echo "[*] Running $NAME"

    for i in $(seq 1 $RUNS); do
        echo "Run $i/$RUNS"

        taskset -c $CPU \
        perf stat -x, -e \
        cycles,instructions,branches,branch-misses,cache-misses,dTLB-load-misses \
        "$BIN" \
        2>> "../../$OUTDIR/${NAME}_perf.csv"

    done
}

run_bench "rlsf" "$RLSF_DIR"
run_bench "verus" "$VERUS_DIR"

echo "[*] Done."
echo "Results saved in $OUTDIR/"
