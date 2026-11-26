#!/usr/bin/env python3
"""Independent exhaustive verification of an already saved search candidate.

This performs no circuit search and emits no lower-bound certificate.
"""
import argparse
import hashlib
import json
from pathlib import Path

EDGES = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6),
         (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]


def target(mask):
    return any(mask & (1 << a) and mask & (1 << b) for a, b in EDGES)


def evaluate(circuit, mask):
    wires = [bool(mask & (1 << i)) for i in range(10)]
    for gate in circuit["gates"]:
        assert gate["op"] in {"and", "or"}
        assert len(gate["inputs"]) == 2
        a, b = gate["inputs"]
        assert 0 <= a < len(wires) and 0 <= b < len(wires)
        wires.append(wires[a] and wires[b] if gate["op"] == "and"
                     else wires[a] or wires[b])
    assert 0 <= circuit["output"] < len(wires)
    return wires[circuit["output"]]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("candidate", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    raw = args.candidate.read_bytes()
    circuit = json.loads(raw)
    positives = sorted((1 << a) | (1 << b) for a, b in EDGES)
    negatives = [m for m in range(1024) if not target(m) and all(
        m & (1 << v) or target(m | (1 << v)) for v in range(10))]
    errors = [{"mask": m, "expected": target(m), "actual": evaluate(circuit, m)}
              for m in range(1024) if evaluate(circuit, m) != target(m)]
    sample_errors = [e for e in errors if e["mask"] in positives + negatives]
    result = {
        "candidate_sha256": hashlib.sha256(raw).hexdigest(),
        "gate_count": len(circuit["gates"]),
        "checked_assignments": 1024,
        "positive_edge_masks": positives,
        "negative_maximal_independent_masks": negatives,
        "sample_errors": sample_errors,
        "all_input_error_count": len(errors),
        "all_input_error_masks": [e["mask"] for e in errors],
        "is_counterexample_to_2590": not errors and len(circuit["gates"]) <= 19,
        "scope": "Verification of one candidate only; no impossibility claim."
    }
    text = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
