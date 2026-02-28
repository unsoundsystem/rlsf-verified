#!/bin/bash
set -ex

VERUS_PATH=$(realpath $(dirname "$0")/../../verus/source/target-verus/release/verus)
PROJ=$(realpath $(dirname "$0")/..)
VERUS_SINGULAR_PATH=/usr/bin/Singular

funcs=("linked_list Tlsf::link_free_block" "mapping Tlsf::map_floor")

cd $PROJ

run() {
    echo "Checking for regression"
    for item in "${funcs[@]}"; do
        set -- $item
        echo "Verifying $2 at $1"
        VERUS_SINGULAR_PATH=$VERUS_SINGULAR_PATH $VERUS_PATH src/lib.rs \
            --verify-only-module $1 \
            --verify-function lib::$2 \
            --crate-type=lib \
            --expand-errors \
            --multiple-errors=10 \
            --triggers-mode silent \
            --log=smt
    done
}

run
