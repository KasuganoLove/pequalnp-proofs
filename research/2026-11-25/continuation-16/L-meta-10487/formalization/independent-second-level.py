#!/usr/bin/env python3
"""Expand exactly one further literal dispatch level for children73/76/83/85.

No recursive rejection, extra pruning, deduplication, or Lean execution occurs.
The first-level artifact is read-only and its frozen hash is verified twice.
"""
from collections import Counter
from hashlib import sha256
from itertools import combinations, product
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
FIRST = HERE / "independent-first-level.json"
FIRST_SHA = "ec0dce271bc98f74e13ea0f6077f9df37c34507641009da1f17b185b539a84a2"
assert sha256(FIRST.read_bytes()).hexdigest() == FIRST_SHA
first = json.loads(FIRST.read_text())
source = (HERE / first["source_file"]).read_bytes()
assert sha256(source).hexdigest() == first["source_sha256"]
rows_text = source.decode().split("def rows : List W :=", 1)[1].split("]", 1)[0]
rows = [int(s, 16) for s in re.findall(r"0x[0-9a-fA-F]+", rows_text)]
problem_bytes = (HERE.parent / "signed-probe/problem.json").read_bytes()
assert sha256(problem_bytes).hexdigest() == first["problem_sha256"]
problem = json.loads(problem_bytes)
edges = [tuple(e) for e in problem["edges"]]
N, WIDTH, HALF = 7, 3192, 1596
mask, half_mask, raw_mask = (1 << WIDTH) - 1, (1 << HALF) - 1, (1 << 128) - 1
assert len(rows) == N
raw_rows = [sum(((x >> i) & 1) << x for x in range(128)) for i in range(N)]


def label(x):
    return any((x >> a) & 1 and (x >> b) & 1 for a, b in edges)


positives = [x for x in range(128) if label(x)]
negatives = [x for x in range(128) if not label(x)]
sample_pairs = [
    (sum(((w >> q) & 1) << i for i, w in enumerate(rows)),
     sum(((w >> (HALF + q)) & 1) << i for i, w in enumerate(rows)))
    for q in range(HALF)
]
assert len(positives) == 114 and len(negatives) == 14
assert len(set(sample_pairs)) == HALF
assert set(sample_pairs) == set(product(positives, negatives))


def singles(xs):
    if not xs:
        return []
    a, *rest = xs
    return [(a, rest)] + [(b, [a] + bs) for b, bs in singles(rest)]


def pairs(xs):
    if not xs:
        return []
    a, *rest = xs
    return [(a, b, bs) for b, bs in singles(rest)] + [
        (b, c, [a] + bs) for b, c, bs in pairs(rest)
    ]


def ops(a, b, bitmask):
    return [a & b, a | b, a & (b ^ bitmask), b & (a ^ bitmask)]


def sep(w):
    return ((w >> HALF) ^ w) & half_mask


def cuts(ws):
    result = 0
    for w in ws:
        result |= sep(w)
    return result


def separates_all128(ws):
    def sig(x):
        return sum(((w >> x) & 1) << i for i, w in enumerate(ws))
    return {sig(p) for p in positives}.isdisjoint({sig(n) for n in negatives})


def write_compact_records(path, header, records):
    path.write_text(json.dumps(header, indent=2)[:-2] + ',\n  "children": [\n' +
                    ',\n'.join('    ' + json.dumps(r, separators=(',', ':')) for r in records) +
                    '\n  ]\n}\n')
    assert json.loads(path.read_text()) == {**header, "children": records}


op_names = ["a_and_b", "a_or_b", "a_and_not_b", "b_and_not_a"]
keep_names = ["none", "a", "b", "both"]
parent_summaries = []
for first_index in [73, 76, 83, 85]:
    parent = first["children"][first_index]
    assert parent["child_index"] == first_index
    a, b = parent["pair_indices"]
    op = parent["operator_index"]
    w = ops(rows[a], rows[b], mask)[op]
    raw_w = ops(raw_rows[a], raw_rows[b], raw_mask)[op]
    assert f"{raw_w:032x}" == parent["new_signal_truth_table128_hex"]
    parent_rows = [w if i == "w" else rows[i] for i in parent["frontier_recipe"]]
    parent_raw = [raw_w if i == "w" else raw_rows[i] for i in parent["frontier_recipe"]]
    extra, budget = parent["extra"], parent["budget"]
    assert extra == 3 and budget == 9 and len(parent_rows) == 7
    assert extra + len(parent_rows) == budget + 1
    assert cuts(parent_rows) == half_mask and separates_all128(parent_raw)
    ordered_pairs = pairs(list(range(len(parent_rows))))
    assert ordered_pairs == [
        (a, b, [i for i in range(len(parent_rows)) if i != a and i != b])
        for a, b in combinations(range(len(parent_rows)), 2)
    ]
    records, candidate_count = [], 0
    for pair_index, (a, b, rest) in enumerate(ordered_pairs):
        base = cuts([parent_rows[i] for i in rest])
        for op_index, (w2, raw_w2) in enumerate(zip(
                ops(parent_rows[a], parent_rows[b], mask),
                ops(parent_raw[a], parent_raw[b], raw_mask))):
            v = sep(w2) | base
            for keep_index in range(4):
                ordinal = candidate_count
                candidate_count += 1
                kept = ([a] if keep_index & 1 else []) + ([b] if keep_index & 2 else [])
                child_rows = [w2] + [parent_rows[i] for i in kept + rest]
                child_raw = [raw_w2] + [parent_raw[i] for i in kept + rest]
                guard = v
                for i in kept:
                    guard |= sep(parent_rows[i])
                assert guard == cuts(child_rows)
                separates = guard == half_mask
                assert separates == separates_all128(child_raw)
                if len(kept) > extra or not separates:
                    continue
                child_extra = extra - len(kept)
                assert child_extra + len(child_rows) == budget
                records.append({
                    "state_child_index": len(records),
                    "candidate_ordinal": ordinal,
                    "pair_index": pair_index,
                    "pair_indices": [a, b],
                    "operator_index": op_index,
                    "op": op_names[op_index],
                    "keep_index": keep_index,
                    "kept": keep_names[keep_index],
                    "kept_indices": kept,
                    "rest_indices": rest,
                    "frontier_recipe": ["w2"] + kept + rest,
                    "new_signal_truth_table128_hex": f"{raw_w2:032x}",
                    "budget": budget - 1,
                    "extra": child_extra,
                    "new_frontier_count": len(child_rows),
                    "room_sum": child_extra + len(child_rows),
                })
    assert candidate_count == 336
    header = {
        "scope": "One second-level expansion only, not recursive rejection or a formal proof",
        "first_level_sha256": FIRST_SHA,
        "first_child_index": first_index,
        "parent": parent,
        "index_convention": "pair/frontier indices refer to the ordered parent frontier; w2 is the selected new operation",
        "candidate_branches": candidate_count,
        "valid_children": len(records),
        "rejected_by_separation": candidate_count - len(records),
        "counts_by_keep": dict(Counter(r["kept"] for r in records)),
        "counts_by_operator": dict(Counter(r["op"] for r in records)),
        "all_child_room_equal_budget_plus_one": True,
        "independent_all128_separation_checks_agree": True,
    }
    output = HERE / f"independent-second-level-{first_index}.json"
    write_compact_records(output, header, records)
    parent_summaries.append({
        **{k: v for k, v in header.items() if k not in ("parent", "scope", "index_convention", "first_level_sha256")},
        "output_file": output.name,
        "output_bytes": output.stat().st_size,
        "output_sha256": sha256(output.read_bytes()).hexdigest(),
    })

assert sha256(FIRST.read_bytes()).hexdigest() == FIRST_SHA
summary = {
    "scope": "Exactly one further dispatch level for first-level indices73,76,83,85; no full search or Lean run",
    "first_level_source_sha256": first["source_sha256"],
    "frozen_first_level_json_sha256": FIRST_SHA,
    "first_level_artifact_unchanged": True,
    "script_file": Path(__file__).name,
    "script_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
    "order": "existing recursive pairs, then[a&b,a|b,a&~b,b&~a], then keep[none,a,b,both]",
    "optimizations": "none beyond the exact existing dispatch guards",
    "sample_pairs": HALF,
    "sample_orientation": "low half114positive inputs times high half14negative inputs",
    "total_candidates": sum(x["candidate_branches"] for x in parent_summaries),
    "total_valid_children_with_multiplicity": sum(x["valid_children"] for x in parent_summaries),
    "parents": parent_summaries,
}
(HERE / "independent-second-level.json").write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps(summary, indent=2))
