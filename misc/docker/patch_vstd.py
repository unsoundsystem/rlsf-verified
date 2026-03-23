#!/usr/bin/env python3
"""Patch vstd to make u64_trailing_zeros opaque (revealable) instead of closed."""
import sys
import re

path = sys.argv[1]
with open(path) as f:
    t = f.read()

# 1) closed -> opaque open
t = t.replace(
    'pub closed spec fn u64_trailing_zeros',
    '#[verifier::opaque]\npub open spec fn u64_trailing_zeros')

# 2) Add reveal(u64_trailing_zeros) at the start of axiom_u64_trailing_zeros body
t = re.sub(
    r'(pub broadcast proof fn axiom_u64_trailing_zeros\(i: u64\)\n'
    r'.*?'           # ensures block
    r'    decreases i,\n'
    r'\{\n)',
    r'\g<1>    reveal(u64_trailing_zeros);\n',
    t,
    count=1,
    flags=re.DOTALL)

with open(path, 'w') as f:
    f.write(t)

print('Patched', path)
