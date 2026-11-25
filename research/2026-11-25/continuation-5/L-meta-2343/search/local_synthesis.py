#!/usr/bin/env python3
"""Generate the exact 52+234 samples and structured 62-gate suffix seeds.

The free input is one OR of two raw variables.  The full star construction has
64 gates, and treating one actual leaf-OR as free leaves 63 suffix gates.  A
single further leaf-OR deletion makes a 62-gate near miss.  No lower-bound claim
is made by this heuristic generator or its companion search.
"""
from itertools import combinations
from pathlib import Path
import json

OUT = Path(__file__).resolve().parent
D = {0, 1, 3, 9}
edges = [(p, l) for p in range(13) for l in range(13) if (p-l) % 13 in D]
quads = [q for q in combinations(range(13), 4)
         if all(sum((p-l) % 13 in D for p in q) <= 2 for l in range(13))]
positive = [(1 << p) | (1 << (13+l)) for p, l in edges]
negative = [sum(1 << p for p in q) | sum(1 << (13+l) for l in range(13)
             if all((p-l) % 13 not in D for p in q)) for q in quads]
rows = positive + negative
assert (len(positive), len(negative), len(set(rows))) == (52, 234, 286)
target = (1 << 52)-1


def evaluate(gates, pair):
    wires = [sum(((x >> k) & 1) << r for r, x in enumerate(rows)) for k in range(26)]
    wires.append(wires[pair[0]] | wires[pair[1]])
    for op, a, b in gates:
        wires.append((wires[a] & wires[b]) if op == 0 else (wires[a] | wires[b]))
    return wires[-1]


def star_seed(dual=False):
    adj = lambda c: [p if dual else 13+p for p in range(13)
                     if ((p-c) if dual else (c-p)) % 13 in D]
    pair = adj(0)[:2]
    gates = []
    def gate(op, a, b):
        w = 27 + len(gates)
        gates.append((op, a, b))
        return w
    terms = []
    for c in range(13):
        near = adj(c)
        a = 26 if c == 0 else gate(1, near[0], near[1])
        b = gate(1, near[2], near[3])
        join = gate(1, a, b)
        terms.append(gate(0, c+13 if dual else c, join))
    acc = terms[0]
    for t in terms[1:]:
        acc = gate(1, acc, t)
    assert len(gates) == 63 and evaluate(gates, pair) == target
    return gates, pair


def remove_alias(gates, j, side):
    dead = 27+j
    alias = gates[j][1+side]
    def remap(w):
        if w == dead: w = alias
        return w-(w > dead)
    return [(op, remap(a), remap(b)) for i, (op,a,b) in enumerate(gates) if i != j]


seeds = []
for dual in [False, True]:
    gates, pair = star_seed(dual)
    (OUT/('baseline_'+str(int(dual))+'.json')).write_text(json.dumps(
        {'free_or': pair, 'gates': gates, 'output': 89, 'size': 63,
         'all_286_rows_pass': True}, indent=2)+'\n')
    for j, (op, a, b) in enumerate(gates):
        if op == 1 and a < 26 and b < 26:
            for side in [0, 1]:
                seed = remove_alias(gates, j, side)
                got = evaluate(seed, pair)
                fp = (got & ~target).bit_count()
                fn = (target & ~got).bit_count()
                assert len(seed) == 62 and fp == 0 and fn == 1
                seeds.append({'dual': dual, 'free_or': pair, 'deleted_gate': j,
                              'kept_side': side, 'gates': seed})

(OUT/'samples.json').write_text(json.dumps({'difference_set': sorted(D), 'edges': edges,
    'quadrangles': quads, 'positive': positive, 'negative': negative,
    'positive_count': 52, 'negative_count': 234, 'total': 286}, indent=2)+'\n')
(OUT/'seeds.json').write_text(json.dumps(seeds)+'\n')
with (OUT/'search-input.txt').open('w') as f:
    f.write(f'{len(rows)} {len(seeds)}\n')
    f.write(' '.join(map(str, rows))+'\n')
    for s in seeds:
        f.write(' '.join(map(str, s['free_or']))+'\n')
        for gate in s['gates']: f.write(' '.join(map(str, gate))+'\n')
print(json.dumps({'positive':52,'negative':234,'total':286,'seeds':len(seeds),
                  'each_seed':{'suffix_size':62,'false_positive':0,'false_negative':1}}))
