#!/bin/bash
set -euo pipefail

PROJ_ROOT=$(realpath "$(dirname "$0")/..")
OUTPUT_DIR="${1:-$PROJ_ROOT/misc/ir_output}"
BENCH_DIR="$PROJ_ROOT/benches"
FUNCS=(allocate deallocate link_free_block unlink_free_block)
# Mangled name patterns (Rust uses length-prefixed encoding)
declare -A MANGLE_PAT
MANGLE_PAT[allocate]="8allocate17h"
MANGLE_PAT[deallocate]="10deallocate17h"
MANGLE_PAT[link_free_block]="15link_free_block17h"
MANGLE_PAT[unlink_free_block]="17unlink_free_block17h"

mkdir -p "$OUTPUT_DIR/functions"

echo "[*] Output directory: $OUTPUT_DIR"

# Target functions are generic (Tlsf<FLLEN, SLLEN>), so we need monomorphised IR
# from a concrete binary, not the library crate alone.
# We use RUSTFLAGS="--emit=llvm-ir" to get IR for all crates including dependencies.
# Building a single small binary (alt32b) is sufficient.
cd "$BENCH_DIR"

# --- Step 1: opt3 (release) ---
echo "[*] Building all (opt3, release)..."
cargo clean --release 2>/dev/null || true
RUSTFLAGS="--emit=llvm-ir" cargo build --release --bin alt32b-verified --bin alt32b-original 2>&1 | tail -3

# Find the monomorphised IR files
# The binary deps contain the final monomorphised code
verified_ll=$(find target/release/deps -name "alt32b_verified-*.ll" | head -1)
original_ll=$(find target/release/deps -name "alt32b_original-*.ll" | head -1)

# If not found as binary IR, try the rlsf crate IR (may have monomorphised via LTO/codegen-units=1)
if [ -z "$verified_ll" ]; then
  verified_ll=$(find target/release/deps -name "rlsf_verified-*.ll" | head -1)
fi
if [ -z "$original_ll" ]; then
  original_ll=$(find target/release/deps -name "rlsf-*.ll" | grep -v verified | head -1)
fi

if [ -z "$verified_ll" ]; then echo "ERROR: verified opt3 .ll not found"; exit 1; fi
if [ -z "$original_ll" ]; then echo "ERROR: original opt3 .ll not found"; exit 1; fi

cp "$verified_ll" "$OUTPUT_DIR/verified_opt3.ll"
cp "$original_ll" "$OUTPUT_DIR/original_opt3.ll"
echo "[*] verified_opt3.ll: $(basename "$verified_ll") ($(wc -l < "$OUTPUT_DIR/verified_opt3.ll") lines)"
echo "[*] original_opt3.ll: $(basename "$original_ll") ($(wc -l < "$OUTPUT_DIR/original_opt3.ll") lines)"

# --- Step 2: opt0 (debug) ---
echo "[*] Building all (opt0, debug)..."
cargo clean 2>/dev/null || true
RUSTFLAGS="--emit=llvm-ir" cargo build --bin alt32b-verified --bin alt32b-original 2>&1 | tail -3

verified_ll=$(find target/debug/deps -name "alt32b_verified-*.ll" | head -1)
original_ll=$(find target/debug/deps -name "alt32b_original-*.ll" | head -1)

if [ -z "$verified_ll" ]; then
  verified_ll=$(find target/debug/deps -name "rlsf_verified-*.ll" | head -1)
fi
if [ -z "$original_ll" ]; then
  original_ll=$(find target/debug/deps -name "rlsf-*.ll" | grep -v verified | head -1)
fi

if [ -z "$verified_ll" ]; then echo "ERROR: verified opt0 .ll not found"; exit 1; fi
if [ -z "$original_ll" ]; then echo "ERROR: original opt0 .ll not found"; exit 1; fi

cp "$verified_ll" "$OUTPUT_DIR/verified_opt0.ll"
cp "$original_ll" "$OUTPUT_DIR/original_opt0.ll"
echo "[*] verified_opt0.ll: $(basename "$verified_ll") ($(wc -l < "$OUTPUT_DIR/verified_opt0.ll") lines)"
echo "[*] original_opt0.ll: $(basename "$original_ll") ($(wc -l < "$OUTPUT_DIR/original_opt0.ll") lines)"

# --- Step 3: list all defines to help find mangled names ---
echo "[*] Scanning for target functions..."
for opt in opt3 opt0; do
  for side in original verified; do
    echo "  === ${side}_${opt} ==="
    for func in "${FUNCS[@]}"; do
      grep "^define" "$OUTPUT_DIR/${side}_${opt}.ll" | grep "${MANGLE_PAT[$func]}" | head -1 || true
    done
    [ -z "$(grep "^define" "$OUTPUT_DIR/${side}_${opt}.ll" | grep -E "$(IFS='|'; echo "${MANGLE_PAT[*]}")" | head -1)" ] && echo "    (none)" || true
  done
done

# --- Step 4: extract functions ---
echo "[*] Extracting functions..."

extract_func() {
  local ir_file=$1 func_pattern=$2 out_file=$3
  # Match function name pattern, allowing for mangled generics
  local mangled
  local mangle_key="${MANGLE_PAT[$func_pattern]}"
  mangled=$(grep "^define" "$ir_file" | grep "$mangle_key" | head -1 | sed 's/.*@\([^ (]*\).*/\1/' || true)
  if [ -z "$mangled" ]; then
    echo "  WARN: $func_pattern not found in $(basename "$ir_file")"
    touch "$out_file"
    return
  fi
  # Escape special regex chars in mangled name for awk
  local escaped
  escaped=$(printf '%s' "$mangled" | sed 's/[.[\*^$()+?{|\\]/\\&/g')
  awk "/^define.*${escaped}/,/^}/" "$ir_file" > "$out_file"
  local n
  n=$(wc -l < "$out_file")
  echo "  $(basename "$ir_file"):$func_pattern -> $n lines ($mangled)"
}

for opt in opt3 opt0; do
  for func in "${FUNCS[@]}"; do
    extract_func "$OUTPUT_DIR/original_${opt}.ll" "$func" "$OUTPUT_DIR/functions/original_${opt}_${func}.ll"
    extract_func "$OUTPUT_DIR/verified_${opt}.ll" "$func" "$OUTPUT_DIR/functions/verified_${opt}_${func}.ll"
  done
done

# --- Step 5: diff ---
echo "[*] Computing diffs..."
for opt in opt3 opt0; do
  for func in "${FUNCS[@]}"; do
    orig="$OUTPUT_DIR/functions/original_${opt}_${func}.ll"
    veri="$OUTPUT_DIR/functions/verified_${opt}_${func}.ll"
    diff -u "$orig" "$veri" > "$OUTPUT_DIR/functions/diff_${opt}_${func}.ll" 2>/dev/null || true
  done
done

# --- Step 6: summary ---
echo "[*] Generating summary..."
{
  for opt in opt3 opt0; do
    echo "=== $opt ==="
    for func in "${FUNCS[@]}"; do
      orig="$OUTPUT_DIR/functions/original_${opt}_${func}.ll"
      veri="$OUTPUT_DIR/functions/verified_${opt}_${func}.ll"
      orig_n=0; veri_n=0; diff_n=0
      [ -s "$orig" ] && orig_n=$(wc -l < "$orig")
      [ -s "$veri" ] && veri_n=$(wc -l < "$veri")
      [ -s "$OUTPUT_DIR/functions/diff_${opt}_${func}.ll" ] && diff_n=$(wc -l < "$OUTPUT_DIR/functions/diff_${opt}_${func}.ll")
      printf "%-25s original=%5d  verified=%5d  diff_lines=%5d\n" "$func" "$orig_n" "$veri_n" "$diff_n"
    done
    echo
  done
} | tee "$OUTPUT_DIR/summary.txt"

echo "[*] Done. Results in $OUTPUT_DIR/"
