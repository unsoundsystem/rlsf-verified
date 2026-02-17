#!/usr/bin/env bash
set -euo pipefail

CPU=1
RUNS=50
RT_PRIO=99

BENCH_PROJ="./rlsf-verified-tests"
OUTDIR="results_$(date +%Y%m%d_%H%M%S)"
mkdir -p "$OUTDIR"

SIZES=("64b" "32b" "16b" "8b")
KINDS=("original" "verified")   # ← ここで両方回す

echo "[*] Checking CPU governor..."
cpupower frequency-info | grep -q "performance" || {
  echo "WARNING: governor is not performance"
}

echo "[*] THP status:"
cat /sys/kernel/mm/transparent_hugepage/enabled

echo "[*] ASLR status:"
cat /proc/sys/kernel/randomize_va_space

command -v chrt >/dev/null || { echo "ERROR: chrt not found"; exit 1; }
command -v perf >/dev/null || { echo "ERROR: perf not found"; exit 1; }

########################################
# build
########################################
build_project () {
  echo "[*] Building in $BENCH_PROJ"
  pushd "$BENCH_PROJ" >/dev/null

  for s in "${SIZES[@]}"; do
    for k in "${KINDS[@]}"; do
      bin="alt${s}-${k}"
      echo "  - build $bin"
      # TODO: add `-C lto` version
      RUSTFLAGS="-C target-cpu=native" \
        cargo build --release --bin "$bin"
    done
  done

  popd >/dev/null
}

########################################
# run
########################################
run_bench () {
  pushd "$BENCH_PROJ" >/dev/null

  for s in "${SIZES[@]}"; do
    for k in "${KINDS[@]}"; do

      BIN="target/release/alt${s}-${k}"

      if [[ ! -x "$BIN" ]]; then
        echo "ERROR: binary not found: $BIN"
        exit 1
      fi

      echo "[*] Running size=$s kind=$k"

      for ((i=1; i<=RUNS; i++)); do
        echo "  Run $i/$RUNS"

        echo "${k},${s},run=${i}" >> "../$OUTDIR/meta.log"

        sudo chrt -f "$RT_PRIO" \
          taskset -c "$CPU" \
          perf stat -x, -e \
          cycles,instructions,branches,branch-misses,cache-misses,dTLB-load-misses,minor-faults \
          "$BIN" \
          2>> "../$OUTDIR/perf_${k}.csv"

      done
    done
  done

  popd >/dev/null
}

########################################

build_project
run_bench

echo "[*] Done."
echo "Results saved in $OUTDIR/"
