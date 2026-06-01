#!/bin/bash
# Verify each operation in the standalone overlaid-list port.
# Modelled on misc/check.sh.
set -e

VERUS_PATH=$(realpath $(dirname "$0")/../../../verus/source/target-verus/release/verus)
LIB=$(realpath $(dirname "$0")/lib.rs)
VERUS_SINGULAR_PATH=/usr/bin/Singular

funcs=(
    # ========== block ==========
    "block BlockPerm::wf"
    "block BlockPerm::wf_freelink"

    # ========== OVList1 (singly-linked, owns perms) ==========
    "ovlist1 OVList1::new"
    "ovlist1 OVList1::push_front"
    "ovlist1 OVList1::pop_front"
    # OVList1::remove - TODO, currently #[verifier::external_body]

    # ========== OVList2 (doubly-linked, perms by reference) ==========
    "ovlist2 OVList2::new"
    "ovlist2 OVList2::push_front"
    "ovlist2 OVList2::pop_front"
    # OVList2::remove - TODO, currently #[verifier::external_body]

    # ========== OVList (composition of list1 + list2 + shared perms) ==========
    "ovlist OVList::new"
    "ovlist OVList::push_front_1"
    "ovlist OVList::pop_front_1"
    "ovlist OVList::push_front_2"
    "ovlist OVList::pop_front_2"
    "ovlist OVList::remove_1"
    "ovlist OVList::remove_2"
)

run() {
    echo "Checking misc/ovls/ port"
    for item in "${funcs[@]}"; do
        set -- $item
        local module=$1
        local func=$2
        echo "=== Verifying $func at $module ==="
        VERUS_SINGULAR_PATH=$VERUS_SINGULAR_PATH $VERUS_PATH "$LIB" \
            --verify-only-module $module \
            --verify-function $func \
            --crate-type=lib \
            --triggers-mode silent \
            --rlimit=500
    done
    echo
    echo "All targets verified."
}

run
