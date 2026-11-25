"""Exact graph audit and symbolic113-gate control; no2^40 enumeration."""
from pathlib import Path
from collections import Counter
import hashlib
import itertools
import json
import re

P = Path(__file__).resolve().parent
gap = json.loads((P.parent / "gap.json").read_text())
edges = [(int(a), int(b)) for a, b in re.findall(r"\(x (\d+) && x (\d+)\)", gap["statement"])]
assert len(edges) == len(set(edges)) == 95
assert all(0 <= a < 21 <= b < 40 for a, b in edges)
adj = [set() for _ in range(40)]
for a, b in edges:
    adj[a].add(b)
    adj[b].add(a)
common = {(a, b): adj[a] & adj[b] for a, b in itertools.combinations(range(21), 2)}
four_cycles = sum(len(s) * (len(s) - 1) // 2 for s in common.values())
assert four_cycles == 0
six_cycles = []
for a, b, c in itertools.combinations(range(21), 3):
    intersections = [common[a, b], common[a, c], common[b, c]]
    if all(len(s) == 1 for s in intersections):
        lines = [next(iter(s)) for s in intersections]
        if len(set(lines)) == 3:
            six_cycles.append((a, b, c, *lines))

# Explicit matching saturating the smaller part gives a19-cover lower bound.
matched_left = {}
def augment(r, seen):
    for l in sorted(adj[r]):
        if l in seen:
            continue
        seen.add(l)
        if l not in matched_left or augment(matched_left[l], seen):
            matched_left[l] = r
            return True
    return False
for r in range(21, 40):
    assert augment(r, set())
matching = sorted((l, r) for l, r in matched_left.items())
assert len(matching) == 19 and len({r for _, r in matching}) == 19
assert all((l, r) in edges for l, r in matching)

# Recover the cyclic21-point incidence extension without assuming an isomorphism.
difference_set = [3, 5, 15, 18, 19]
full_lines = {i: {(i + d) % 21 for d in difference_set} for i in range(21)}
assert {(i, 21 + r) for i in range(21) for r in full_lines[i] if r < 19} == set(edges)
differences = Counter((a - b) % 21 for a in difference_set for b in difference_set if a != b)
assert differences == Counter({i: 1 for i in range(1, 21)})
deleted_line_points = {r: [i for i in range(21) if r in full_lines[i]] for r in [19, 20]}

# General monotone DNF antichain evaluator for an exact symbolic witness check.
def minimal(terms):
    answer = []
    for t in sorted(set(terms), key=lambda x: (x.bit_count(), x)):
        if not any((s & t) == s for s in answer):
            answer.append(t)
    return frozenset(answer)
wires = [frozenset([1 << i]) for i in range(40)]
gates = []
def gate(op, a, b):
    assert a < len(wires) and b < len(wires)
    if op == "or":
        result = minimal(wires[a] | wires[b])
    else:
        assert op == "and"
        result = minimal(x | y for x in wires[a] for y in wires[b])
    gates.append({"op": op, "inputs": [a, b]})
    wires.append(result)
    return len(wires) - 1
stars = []
for r in range(21, 40):
    neighbors = sorted(adj[r])
    signal = neighbors[0]
    for l in neighbors[1:]:
        signal = gate("or", signal, l)
    stars.append(gate("and", r, signal))
output = stars[0]
for s in stars[1:]:
    output = gate("or", output, s)
expected = frozenset((1 << a) | (1 << b) for a, b in edges)
assert len(gates) == 113 and wires[output] == expected
baseline = {"task": gap["id"], "raw_inputs": 40, "gates": gates, "output": output,
            "gate_count": len(gates), "AND_count": 19, "OR_count": 94,
            "verification": "Exact monotone DNF antichain equals all95 graph-edge monomials",
            "satisfies_public_112_bound": False}
(P / "baseline113.json").write_text(json.dumps(baseline, indent=2) + "\n")
result = {"task": gap["id"], "statement_sha256": hashlib.sha256(gap["statement"].encode()).hexdigest(),
          "vertices": 40, "edges": edges, "edge_count": 95,
          "bipartition": [list(range(21)), list(range(21, 40))],
          "left_degree_counts": dict(sorted(Counter(len(adj[i]) for i in range(21)).items())),
          "right_degree_counts": dict(sorted(Counter(len(adj[i]) for i in range(21, 40)).items())),
          "four_cycle_count": four_cycles, "six_cycle_count": len(six_cycles),
          "minimum_vertex_cover_number": 19, "minimum_vertex_cover": list(range(21, 40)),
          "matching_certificate": matching, "cyclic_difference_set": difference_set,
          "difference_multiset_is_each_nonzero_residue_once": True,
          "deleted_original_right_labels": [40, 41],
          "deleted_line_points_by_residue": deleted_line_points,
          "shared_point_of_deleted_lines": sorted(set(deleted_line_points[19]) & set(deleted_line_points[20])),
          "baseline_symbolically_verified": True, "baseline_gates": 113,
          "full_input_enumeration": False, "formal_lean_certificate": False,
          "unrestricted_circuit_lower_bound_claimed": False}
(P / "geometry.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({k: v for k, v in result.items() if k not in ["edges", "bipartition"]}, indent=2))
