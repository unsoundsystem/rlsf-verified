VERUS=/home/shinaikakishita/projects/tlsf-verif/verus/source

if [ `uname` == "Darwin" ]; then
    DYN_LIB_EXT=dylib
elif [ `uname` == "Linux" ]; then
    DYN_LIB_EXT=so
fi

# Run rustdoc.
# Note the VERUSDOC environment variable.

RUSTC_BOOTSTRAP=1 VERUSDOC=1 rustdoc \
  --extern builtin=$VERUS/target-verus/debug/libbuiltin.rlib \
  --extern verus_builtin=$VERUS/target-verus/debug/libverus_builtin.rlib \
  --extern verus_builtin_macros=$VERUS/target-verus/debug/libverus_builtin_macros.$DYN_LIB_EXT \
  --extern verus_state_machines_macros=$VERUS/target-verus/debug/libverus_state_machines_macros.$DYN_LIB_EXT \
  --edition=2018 \
  --cfg verus_keep_ghost \
  --cfg verus_keep_ghost_body \
  --cfg 'feature="std"' \
  --cfg 'feature="alloc"' \
  '-Zcrate-attr=feature(register_tool)' \
  '-Zcrate-attr=register_tool(verus)' \
  '-Zcrate-attr=register_tool(verifier)' \
  '-Zcrate-attr=register_tool(verusfmt)' \
  --crate-type=lib \
  ./src/lib.rs

# Run the post-processor.

$VERUS/target/debug/verusdoc
