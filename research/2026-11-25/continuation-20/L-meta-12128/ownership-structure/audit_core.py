#!/usr/bin/env python3
"""Reproduce the finite data checked during the live L-meta-12128 lease.

This does not synthesize circuits, allocate tasks, or run Lean. The formal
research lemma is separately recorded with its ordinary Lean result.
"""
from itertools import combinations
import json

T = 4276676736 * 2**32 + 4269860864
f = lambda x: bool(T >> x & 1)
assert all(not f(x) or f(x | (1 << i)) for x in range(64) for i in range(6))
minimal_true = [x for x in range(64) if f(x) and all(
    not f(x & ~(1 << i)) for i in range(6) if x >> i & 1)]
assert all(x.bit_count() >= 3 for x in minimal_true)
H = sum(1 << x for x in range(64) if f(x ^ 8))
tables = [H]
steps = []
for p in [5, 3]:
    old = tables[-1]
    new = sum(1 << x for x in range(64) if old >> (x & ~(1 << p)) & 1)
    change = next(x for x in range(64) if bool(old >> x & 1) != bool(new >> x & 1))
    nonzero = next(x for x in range(64) if new >> x & 1)
    steps.append({'variable': p, 'change_witness': change, 'nonzero_witness': nonzero})
    tables.append(new)
assert tables == [16788998196968685800, 9294867679535825128, 18374379617126377704]
assert [s['change_witness'] for s in steps] == [47, 11]
assert [s['nonzero_witness'] for s in steps] == [3, 3]
core = [0, 1, 2, 4]
assert not (H & 1)
assert all(not (tables[-1] >> (1 << i) & 1) for i in core)
assert all(tables[-1] >> ((1 << i) | (1 << j)) & 1 for i, j in combinations(core, 2))
assert all(bool(tables[-1] >> x & 1) == (sum((x >> i) & 1 for i in core) >= 2)
           for x in range(64))
assert all(f(x | 32) == (x.bit_count() >= 3) for x in range(32))
print(json.dumps({
    'target_table': T,
    'minimal_true_masks': minimal_true,
    'flip_variable': 3,
    'six_input_tables': tables,
    'seven_input_lifts_ignoring_input6': [x + (x << 64) for x in tables],
    'restriction_steps': steps,
    'core': core,
    'x5_true_equals_MAJ5_all32': True,
    'has_physical_11_gate_lower_proof_in_this_artifact': False,
}, indent=2))
