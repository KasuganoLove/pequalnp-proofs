#!/usr/bin/env python3
"""Expand one literal L9539 dispatch level; never run the recursive search.

The enumeration order matches dispatchChildren/children: pairs in list order,
then the four original signed operations, then keep none/a/b/both.  No sorting,
canonicalization, deduplication, constant skipping, or memoization is used.
"""
from collections import Counter
from hashlib import sha256
from itertools import combinations, product
import json
from pathlib import Path
import re


HERE = Path(__file__).resolve().parent
SOURCE = HERE / "L_meta_10486.literal.lean"
PROBLEM = HERE.parent / "signed-probe" / "problem.json"
OUT = HERE / "independent-first-level.json"
source_bytes = SOURCE.read_bytes()
source = source_bytes.decode()
rows_text = source.split("def rows : List W :=", 1)[1].split("]", 1)[0]
rows = [int(s, 16) for s in re.findall(r"0x[0-9a-fA-F]+", rows_text)]
problem = json.loads(PROBLEM.read_text())
edges = [tuple(e) for e in problem["edges"]]
N, WIDTH, HALF, BUDGET, EXTRA = 7, 3192, 1596, 10, 4
mask = (1 << WIDTH) - 1
half_mask = (1 << HALF) - 1
raw_mask = (1 << 128) - 1
assert len(rows) == N and all(0 <= w <= mask for w in rows)
assert EXTRA + len(rows) == BUDGET + 1


def label(x):
    return any((x >> a) & 1 and (x >> b) & 1 for a, b in edges)


positives = [x for x in range(128) if label(x)]
negatives = [x for x in range(128) if not label(x)]
assert len(positives) == 114 and len(negatives) == 14
sample_pairs = [
    (sum(((w >> q) & 1) << i for i, w in enumerate(rows)),
     sum(((w >> (HALF + q)) & 1) << i for i, w in enumerate(rows)))
    for q in range(HALF)
]
assert len(set(sample_pairs)) == HALF
assert set(sample_pairs) == set(product(positives, negatives))
raw_rows = [sum(((x >> i) & 1) << x for x in range(128)) for i in range(N)]
for w, raw in zip(rows, raw_rows):
    for q, (p, n) in enumerate(sample_pairs):
        assert ((w >> q) & 1) == ((raw >> p) & 1)
        assert ((w >> (q + HALF)) & 1) == ((raw >> n) & 1)


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


ordered_pairs = pairs(list(range(N)))
assert ordered_pairs == [
    (a, b, [i for i in range(N) if i != a and i != b])
    for a, b in combinations(range(N), 2)
]


def ops(a, b, bitmask):
    return [a & b, a | b, a & (b ^ bitmask), b & (a ^ bitmask)]


def cuts(ws):
    result = 0
    for w in ws:
        result |= ((w >> HALF) ^ w) & half_mask
    return result


def separates_all128(ws):
    def signature(x):
        return sum(((w >> x) & 1) << i for i, w in enumerate(ws))
    ps = {signature(p) for p in positives}
    ns = {signature(n) for n in negatives}
    return ps.isdisjoint(ns)


separating_root_sublists = []
for subset in range(1 << N):
    chosen = [i for i in range(N) if (subset >> i) & 1]
    packed_ok = cuts([rows[i] for i in chosen]) == half_mask
    raw_ok = separates_all128([raw_rows[i] for i in chosen])
    assert packed_ok == raw_ok
    if packed_ok:
        separating_root_sublists.append(chosen)
assert separating_root_sublists == [list(range(N))]

records = []
candidate_count = 0
op_names = ["a_and_b", "a_or_b", "a_and_not_b", "b_and_not_a"]
keep_names = ["none", "a", "b", "both"]
for pair_index, (a, b, rest) in enumerate(ordered_pairs):
    base = cuts([rows[i] for i in rest])
    for op_index, (w, raw_w) in enumerate(zip(
            ops(rows[a], rows[b], mask), ops(raw_rows[a], raw_rows[b], raw_mask))):
        v = (((w >> HALF) ^ w) & half_mask) | base
        for keep_index in range(4):
            candidate_ordinal = candidate_count
            candidate_count += 1
            kept = ([a] if keep_index & 1 else []) + ([b] if keep_index & 2 else [])
            cost = len(kept)
            available = cost <= EXTRA
            guard = v
            for i in kept:
                guard |= ((rows[i] >> HALF) ^ rows[i]) & half_mask
            ws = [w] + [rows[i] for i in kept + rest]
            raw_ws = [raw_w] + [raw_rows[i] for i in kept + rest]
            assert guard == cuts(ws)
            separates = guard == half_mask
            assert separates == separates_all128(raw_ws)
            if not (available and separates):
                continue
            child_extra = EXTRA - cost
            child_budget = BUDGET - 1
            assert child_extra + len(ws) == child_budget + 1
            records.append({
                "child_index": len(records),
                "candidate_ordinal": candidate_ordinal,
                "pair_index": pair_index,
                "pair_indices": [a, b],
                "operator_index": op_index,
                "op": op_names[op_index],
                "keep_index": keep_index,
                "kept": keep_names[keep_index],
                "kept_indices": kept,
                "rest_indices": rest,
                "frontier_recipe": ["w"] + kept + rest,
                "new_signal_truth_table128_hex": f"{raw_w:032x}",
                "budget": child_budget,
                "extra": child_extra,
                "new_frontier_count": len(ws),
                "room_sum": child_extra + len(ws),
                "cuts_full": True,
            })

assert candidate_count == 21 * 4 * 4
assert len(records) == 88
summary = {
    "scope": "One literal first-level expansion only; no recursive search or Lean run",
    "source_file": SOURCE.name,
    "source_sha256": sha256(source_bytes).hexdigest(),
    "problem_file": "../signed-probe/problem.json",
    "problem_sha256": sha256(PROBLEM.read_bytes()).hexdigest(),
    "recipe": "pairs rows in original recursive order; ops [a&b,a|b,a&~b,b&~a]; keep none,a,b,both; keep exactly dispatch guards; do not sort or deduplicate",
    "bit_width": WIDTH,
    "pair_width": HALF,
    "sample_orientation": "low1596 bits positive, high1596 bits negative",
    "cartesian_pairs_verified": len(sample_pairs),
    "independent_all128_separation_checks_agree": True,
    "root": {"budget": BUDGET, "extra": EXTRA, "frontier_count": N,
             "room_sum": EXTRA + N, "expected_room_sum": BUDGET + 1},
    "separating_initial_sublists": separating_root_sublists,
    "raw_pairs": len(ordered_pairs),
    "candidate_branches": candidate_count,
    "valid_children": len(records),
    "rejected_by_separation": candidate_count - len(records),
    "counts_by_keep": dict(Counter(r["kept"] for r in records)),
    "counts_by_operator": dict(Counter(r["op"] for r in records)),
    "all_child_room_equal_budget_plus_one": True,
    "children": records,
}
header = {k: v for k, v in summary.items() if k != "children"}
OUT.write_text(json.dumps(header, indent=2)[:-2] + ",\n  \"children\": [\n" +
               ",\n".join("    " + json.dumps(r, separators=(",", ":")) for r in records) +
               "\n  ]\n}\n")
assert json.loads(OUT.read_text()) == summary
print(json.dumps({k: v for k, v in summary.items() if k != "children"}, indent=2))
print("output_sha256", sha256(OUT.read_bytes()).hexdigest())
