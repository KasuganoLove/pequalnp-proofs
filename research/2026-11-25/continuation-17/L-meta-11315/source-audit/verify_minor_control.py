#!/usr/bin/env python3
"""Independently verify the saved six-input minor control on all 64 inputs."""
import json
from pathlib import Path
p = Path(__file__).resolve().parent
w = json.loads((p / "minor-nine-gate-control.json").read_text())
errors = []
for assignment in range(64):
    raw = [bool(assignment >> i & 1) for i in range(6)]
    wires = raw.copy()
    for op, a, b in w["gates"]:
        assert 0 <= a < len(wires) and 0 <= b < len(wires)
        assert op in {"and", "or"}
        wires.append(wires[a] and wires[b] if op == "and" else wires[a] or wires[b])
    expected = any(raw[a] and raw[b] for a, b in w["edges"])
    if wires[w["output"]] != expected:
        errors.append(assignment)
assert len(w["gates"]) == 9 and errors == []
print(json.dumps({"assignments": 64, "gates": 9, "errors": errors}))
