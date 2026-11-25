#!/usr/bin/env python3
"""Bounded, independent truth-table checks for two nonminimum 5126 examples.

This script mirrors the *finite semantics* of IsAO2/BelowF/junk/TopForm/wmax.
It is not a Lean proof and does not search for a counterexample to L-meta-5126.
All gates have exactly two earlier inputs; all 2**4 assignments are checked.
"""
import itertools
import json
from pathlib import Path


def evaluate(n, gates, assignment):
    wires = [bool(assignment & (1 << v)) for v in range(n)]
    for op, a, b in gates:
        assert 0 <= a < len(wires) and 0 <= b < len(wires)
        assert op in {"and", "or"}
        wires.append(wires[a] and wires[b] if op == "and" else wires[a] or wires[b])
    return wires


def graph_value(edges, assignment):
    return any(assignment & (1 << a) and assignment & (1 << b) for a, b in edges)


def graph_checks(n, edges):
    adjacent = lambda a, b: (min(a, b), max(a, b)) in edges and a != b
    bipartitions = [s for s in range(1 << n)
                    if all(bool(s & (1 << a)) != bool(s & (1 << b)) for a, b in edges)]
    common = {f"{a},{b}": [w for w in range(n) if adjacent(a, w) and adjacent(b, w)]
              for a, b in itertools.combinations(range(n), 2)}
    assert bipartitions and all(len(ws) <= 1 for ws in common.values())
    return {"bipartition_mask": bipartitions[0], "common_neighbor_max": max(map(len, common.values()))}


def all_rectangles(n, truth):
    # Each vertex is outside both factors, in A, or in B. This enumerates all
    # disjoint A,B, including empty factors, with no symmetry quotient.
    matches = []
    examined = 0
    for labels in itertools.product(range(3), repeat=n):
        examined += 1
        a = sum(1 << v for v in range(n) if labels[v] == 1)
        b = sum(1 << v for v in range(n) if labels[v] == 2)
        if all((bool(x & a) and bool(x & b)) == truth[x] for x in range(1 << n)):
            matches.append({"A_mask": a, "B_mask": b})
    return {"examined": examined, "matches": matches}


def analyze(name, edges, gates, shorter, expected_junk, nonrectangle_gate=None):
    n = 4
    edges = sorted(tuple(sorted(e)) for e in edges)
    rows = [evaluate(n, gates, x) for x in range(1 << n)]
    small = [evaluate(n, shorter, x) for x in range(1 << n)]
    target = [bool(graph_value(edges, x)) for x in range(1 << n)]
    assert all(r[-1] == target[x] == small[x][-1] for x, r in enumerate(rows))
    assert len(shorter) < len(gates)
    junk = [j for j, (op, _, _) in enumerate(gates)
            if op == "and" and any(r[n+j] and not target[x] for x, r in enumerate(rows))]
    assert junk == expected_junk and len(junk) == 2
    assert all(not rows[1 << v][n+j] for j in junk for v in range(n))
    ancestors = []
    for _, a, b in gates:
        pred = {w-n for w in (a, b) if w >= n}
        ancestors.append(pred | set().union(*(ancestors[j] for j in pred)))
    ands = [j for j, g in enumerate(gates) if g[0] == "and"]
    tops = [j for j in ands if j not in junk]
    assert all(i not in ancestors[j] for i in tops for j in ands)
    assert ancestors[-1] == set(range(len(gates)-1))
    wmax = {str(j): [w for w in range(n)
                    if all(not (r[n+j] and r[w]) or target[x]
                           for x, r in enumerate(rows))] for j in junk}
    rect = {str(j): all_rectangles(n, [r[n+j] for r in rows]) for j in junk}
    if nonrectangle_gate is not None:
        assert not rect[str(nonrectangle_gate)]["matches"]
    pair_false_positives = {
        str(j): [[a, b] for a, b in itertools.combinations(range(n), 2)
                 if rows[(1 << a) | (1 << b)][n+j]
                 and not target[(1 << a) | (1 << b)]] for j in junk
    }
    return {
        "name": name, "n": n, "edges": edges,
        "gates": [{"op": op, "inputs": [a, b]} for op, a, b in gates],
        "output_wire": n + len(gates)-1,
        "smaller_correct_circuit": {
            "gates": [{"op": op, "inputs": [a, b]} for op, a, b in shorter],
            "output_wire": n + len(shorter)-1,
        },
        "rows_checked": 1 << n, "exact_graph_output": True,
        "is_ao2": True, **graph_checks(n, edges),
        "junk_gate_indices": junk, "junk_one_hot_off": True,
        "top_form": True, "every_gate_reaches_output": True,
        "not_least_reason": f"Explicit {len(shorter)}-gate competitor is smaller than {len(gates)} gates",
        "dirty_gate_wmax": wmax, "dirty_pair_false_positives": pair_false_positives,
        "rectangle_enumeration": rect,
        "rows": [{"assignment_mask": x, "target": target[x],
                  "gate_values": r[n:]} for x, r in enumerate(rows)],
    }


def main():
    nested = analyze(
        "nested_dirty_gate_not_a_rectangle", [(0, 2), (0, 3)],
        [("or", 0, 1), ("or", 2, 3), ("and", 4, 5),
         ("or", 0, 2), ("and", 6, 7), ("and", 8, 0)],
        [("or", 2, 3), ("and", 0, 4)], [2, 4], nonrectangle_gate=4)
    mutual = analyze(
        "two_empty_wmax_gates_filter_each_other", [(0, 3), (1, 2)],
        [("or", 0, 1), ("or", 2, 3), ("and", 4, 5),
         ("or", 0, 2), ("or", 1, 3), ("and", 7, 8), ("and", 6, 9)],
        [("and", 0, 3), ("and", 1, 2), ("or", 4, 5)], [2, 5])
    assert all(not s for s in mutual["dirty_gate_wmax"].values())
    assert all(mutual["rows"][x]["gate_values"][-1]
               == (mutual["rows"][x]["gate_values"][2]
                   and mutual["rows"][x]["gate_values"][5]) for x in range(16))
    result = {
        "purpose": "Sanity checks of intermediate structural inferences, not counterexamples to L-meta-5126",
        "validation": "Independent exhaustive Python, not Lean checked",
        "number_of_examples": 2,
        "total_assignment_rows_checked": 32,
        "disjoint_factor_pairs_checked_per_dirty_gate": 81,
        "examples": [nested, mutual],
    }
    out = Path(__file__).with_name("examples-results.json")
    out.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": "PASS", "examples": 2, "assignment_rows": 32,
                      "rectangle_factor_pairs": 324, "least_circuit_counterexamples": 0}))


if __name__ == "__main__":
    main()
