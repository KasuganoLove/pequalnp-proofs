"""Independent finite sample/first-layer checks; no recursive search."""
from pathlib import Path
from collections import Counter
import hashlib
import itertools
import json

P = Path(__file__).resolve().parent
E = [(0,3),(0,4),(1,4),(2,4),(0,5),(1,5),(3,5),(0,6),(1,6),(3,6),(5,6)]
def target(x):
    return any(x & (1 << a) and x & (1 << b) for a, b in E)
positive = sorted((1 << a) | (1 << b) for a, b in E)
negative = [x for x in range(128) if not target(x)]
maximal = [x for x in negative if all(x & (1 << i) or target(x | (1 << i)) for i in range(7))]
reports = []
for mode, ns in [("edges_all", negative), ("edges_maximal", maximal)]:
    problem = json.loads((P / f"{mode}-problem.json").read_text())
    assert positive == problem["positive_samples"] and ns == problem["negative_samples"]
    samples = positive + ns
    raw = [sum(((x >> i) & 1) << j for j, x in enumerate(samples)) for i in range(7)]
    assert raw == problem["raw_signatures"] and len(set(raw)) == 7
    initial = [s for s in range(128) if all((a ^ b) & s for a in positive for b in ns)]
    assert initial == problem["all_separating_initial_sublists"]
    pairs = list(itertools.product(positive, ns))
    half = len(pairs)
    packed = [sum(((a >> i) & 1) << k for k, (a, b) in enumerate(pairs)) |
              sum(((b >> i) & 1) << (half + k) for k, (a, b) in enumerate(pairs))
              for i in range(7)]
    for k in range(2 * half):
        x = sum(((row >> k) & 1) << i for i, row in enumerate(packed))
        assert target(x) == (k < half)
    reports.append({"mode": mode, "positives": len(positive), "negatives": len(ns),
                    "lean_width": 2 * half, "all_separating_initial_sublists": initial,
                    "all_seven_inputs_required": initial == [127],
                    "packed_rows_hex": [hex(x) for x in packed],
                    "all_packed_bits_and_target_labels_correct": True})
    if mode == "edges_all":
        full = (1 << len(samples)) - 1
        packed_full = (1 << (2 * half)) - 1
        low_mask = (1 << half) - 1
        def sep(ws):
            return all(any((w >> a & 1) != (w >> b & 1) for w in ws)
                       for a in range(len(positive)) for b in range(len(positive), len(samples)))
        def cut(ws):
            c = 0
            for w in ws:
                c |= ((w >> half) ^ w) & low_mask
            return c == low_mask
        children = []
        for i, j in itertools.combinations(range(7), 2):
            a, b, pa, pb = raw[i], raw[j], packed[i], packed[j]
            ops = [a & b, a | b, a & (full ^ b), b & (full ^ a)]
            pops = [pa & pb, pa | pb, pa & (packed_full ^ pb), pb & (packed_full ^ pa)]
            rest = [r for r in range(7) if r not in (i, j)]
            for op, (w, pw) in enumerate(zip(ops, pops)):
                for keep in range(4):
                    kept = ([i] if keep & 1 else []) + ([j] if keep & 2 else [])
                    state = [w] + [raw[r] for r in kept + rest]
                    pstate = [pw] + [packed[r] for r in kept + rest]
                    valid = sep(state)
                    assert valid == cut(pstate)
                    if valid:
                        children.append({"index": len(children), "pair": [i, j], "op": op,
                                         "keep_mask": keep, "extra": 3 - len(kept),
                                         "next_budget": 8, "retained_raw_order": kept + rest,
                                         "sample_signatures_hex": [hex(x) for x in state]})
        assert len(children) == 126
        (P / "edges_all-first-level.json").write_text(json.dumps(children, indent=2) + "\n")
        reports[-1]["first_level_count"] = len(children)
        reports[-1]["first_level_keep_counts"] = dict(Counter(c["keep_mask"] for c in children))
    else:
        model = json.loads((P / "edges_maximal-model.json").read_text())
        mismatch = []
        for x in range(128):
            w = [bool(x >> i & 1) for i in range(7)]
            for gate in model["gates"]:
                assert all(i < len(w) for i in gate["inputs"])
                if gate["op"] == "not":
                    w.append(not w[gate["inputs"][0]])
                elif gate["op"] == "and":
                    w.append(all(w[i] for i in gate["inputs"]))
                else:
                    assert gate["op"] == "or"
                    w.append(any(w[i] for i in gate["inputs"]))
            if w[model["output"]] != target(x):
                mismatch.append(x)
        assert mismatch == model["full_128_mismatches"]
        assert not set(samples) & set(mismatch)
        reports[-1]["sample_model_verified"] = True
        reports[-1]["full_target_mismatches"] = len(mismatch)
out = {"task": "L-meta-11315", "source_sha256": hashlib.sha256((P / "probe.cpp").read_bytes()).hexdigest(),
       "variants": reports, "recursive_search_run": False, "lean_run": False}
(P / "audit.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps([{k: v for k, v in r.items() if k != "packed_rows_hex"} for r in reports], indent=2))
