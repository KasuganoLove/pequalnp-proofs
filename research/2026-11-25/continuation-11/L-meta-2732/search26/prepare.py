"""Build exact Heawood extremal rows and 26-gate heuristic seeds.

Reads the public task's edge list.  This does not assert nonexistence.
"""
from pathlib import Path
import json
import random
import re

HERE = Path(__file__).resolve().parent
edges = [tuple(map(int, p)) for p in re.findall(r'\(\((\d+) : ℕ\), \((\d+) : ℕ\)\)',
                                              (HERE.parent/'statement.txt').read_text())]
assert len(edges) == len(set(edges)) == 21
assert all(0 <= u < 7 <= v < 14 for u, v in edges)
negative = {m for m in range(1 << 14) if not any((m >> u & 1) and (m >> v & 1) for u, v in edges)}
maxfalse = sorted(m for m in negative if all((m | (1 << v)) not in negative
                                            for v in range(14) if not (m >> v & 1)))
positive = [(1 << u) | (1 << v) for u, v in edges]
rows = positive + maxfalse
assert len(maxfalse) == 37 and len(rows) == 58
(HERE/'rows.txt').write_text(f'{len(rows)} {len(positive)}\n'+' '.join(map(str, rows))+'\n')
rng = random.Random(273220261125)

def build_star(right):
    gates = []
    centers = list(range(7, 14)) if right else list(range(7))
    rng.shuffle(centers)
    terms = []
    def add(op, a, b):
        gates.append([op, min(a, b), max(a, b)])
        return 13 + len(gates)
    for v in centers:
        neighbors = [a if b == v else b for a, b in edges if a == v or b == v]
        assert len(neighbors) == 3
        rng.shuffle(neighbors)
        s = add(1, neighbors[0], neighbors[1])
        s = add(1, s, neighbors[2])
        terms.append(add(0, v, s))
    while len(terms) > 1:
        a = terms.pop(rng.randrange(len(terms)))
        b = terms.pop(rng.randrange(len(terms)))
        terms.append(add(1, a, b))
    assert len(gates) == 27
    return {'size': 27, 'output': terms[0], 'gates': gates}

def erase(seed, gate, operand):
    old = seed['gates']
    replacement = old[gate][operand]
    erased_wire = 14+gate
    def wire(v):
        if v == erased_wire: v = replacement
        return v-1 if v > erased_wire else v
    gates = [[op, wire(a), wire(b)] for k, (op, a, b) in enumerate(old) if k != gate]
    assert len(gates) == 26
    assert all(0 <= a < 14+k and 0 <= b < 14+k for k, (_, a, b) in enumerate(gates))
    return {'size': 26, 'output': wire(seed['output']), 'gates': gates}

seeds = []
for trial in range(128):
    star = build_star(bool(trial % 2))
    if trial == 0:
        (HERE/'known-27.json').write_text(json.dumps(star, indent=2)+'\n')
    for k in range(27):
        for operand in [1, 2]:
            seeds.append(erase(star, k, operand))
with (HERE/'seeds.txt').open('w') as f:
    f.write(str(len(seeds))+'\n')
    for seed in seeds:
        f.write(str(seed['output'])+'\n')
        for gate in seed['gates']: f.write(' '.join(map(str, gate))+'\n')
(HERE/'problem.json').write_text(json.dumps({
    'inputs': 14, 'edges': edges, 'gate_budget': 26,
    'minimal_true_rows': positive, 'maximal_false_rows': maxfalse,
    'negative_assignments': len(negative), 'training_rows': len(rows),
    'seed_count': len(seeds), 'seed_rng': 273220261125,
    'model': 'acyclic binary AND/OR; repeated inputs allowed; arbitrary output wire',
    'scope': 'bounded heuristic witness search only; no UNSAT claim'
}, indent=2)+'\n')
print(json.dumps({'rows': len(rows), 'positive': len(positive), 'maximal_false': len(maxfalse), 'seeds': len(seeds)}))
