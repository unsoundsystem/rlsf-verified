VERUS=$(realpath ../../verus/source)
BUILD_TYPE=debug
RUSTDOC=$HOME/.rustup/toolchains/1.79.0-x86_64-unknown-linux-gnu/bin/rustdoc

if [ `uname` == "Darwin" ]; then
    DYN_LIB_EXT=dylib
elif [ `uname` == "Linux" ]; then
    DYN_LIB_EXT=so
fi

# Run rustdoc.
# Note the VERUSDOC environment variable.

RUSTC_BOOTSTRAP=1 VERUSDOC=1 $RUSTDOC \
  --extern vstd=$VERUS/target-verus/$BUILD_TYPE/libvstd.rlib \
  --extern builtin=$VERUS/target-verus/$BUILD_TYPE/libbuiltin.rlib \
  --extern builtin_macros=$VERUS/target-verus/$BUILD_TYPE/libbuiltin_macros.$DYN_LIB_EXT \
  --extern state_machines_macros=$VERUS/target-verus/$BUILD_TYPE/libstate_machines_macros.$DYN_LIB_EXT \
  --edition=2018 \
  --cfg verus_keep_ghost \
  --cfg verus_keep_ghost_body \
  --cfg 'feature="std"' \
  --cfg 'feature="alloc"' \
  '-Zcrate-attr=feature(register_tool)' \
  '-Zcrate-attr=register_tool(verus)' \
  '-Zcrate-attr=register_tool(verifier)' \
  '-Zcrate-attr=register_tool(verusfmt)' \
  '-Zcrate-attr=feature(rustc_attrs)' \
  '-Zcrate-attr=feature(unboxed_closures)' \
  '-Zcrate-attr=allow(internal_features)' \
  '-Zcrate-attr=allow(unused_braces)' \
  --crate-type=lib \
  $1


# Run the post-processor.

$VERUS/target/$BUILD_TYPE/verusdoc
