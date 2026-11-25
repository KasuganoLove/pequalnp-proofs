"""Exact second successors of the eight one-retained first states; no search."""
from pathlib import Path
from collections import Counter
from functools import lru_cache
import hashlib
import itertools
import json

P = Path(__file__).resolve().parent
first = json.loads((P / "independent-first-level.json").read_text())
baseline = json.loads((P.parent / "ownership-signed/baseline.json").read_text())
positive = baseline["positive_assignments"]
negative = baseline["negative_assignments"]
pair_list = list(itertools.product(positive, negative))
half = len(pair_list)
assert half == 2160
full = (1 << 128) - 1
low_mask = (1 << half) - 1
fibres = [0] * 128
for k, (a, b) in enumerate(pair_list):
    fibres[a] |= 1 << k
    fibres[b] |= 1 << (k + half)
@lru_cache(None)
def packed(w):
    value = 0
    while w:
        bit = w & -w
        value |= fibres[bit.bit_length() - 1]
        w ^= bit
    return value
def raw_guard(ws):
    positives = sum(1 << x for x in positive)
    for q in negative:
        same = positives
        for w in ws:
            same &= w if w >> q & 1 else full ^ w
        if same:
            return False
    return True
def packed_guard(ws):
    cuts = 0
    for w in ws:
        pw = packed(w)
        cuts |= ((pw >> half) ^ pw) & low_mask
    return cuts == low_mask
groups = []
for parent_index in [1, 4, 7, 10, 29, 32, 54, 58]:
    parent = first[parent_index]
    signals = [int(x, 16) for x in parent["frontier_raw_signatures"]]
    extra = parent["extra"]
    assert extra == 2 and len(signals) == 7
    children = []
    for i, j in itertools.combinations(range(len(signals)), 2):
        a, b = signals[i], signals[j]
        rest_positions = [k for k in range(len(signals)) if k not in (i, j)]
        ops = [a & b, a | b, a & (full ^ b), b & (full ^ a)]
        for op, result in enumerate(ops):
            for keep in range(4):
                kept_positions = ([i] if keep & 1 else []) + ([j] if keep & 2 else [])
                cost = len(kept_positions)
                if cost > extra:
                    continue
                retained = kept_positions + rest_positions
                state = [result] + [signals[k] for k in retained]
                valid = raw_guard(state)
                assert valid == packed_guard(state)
                if valid:
                    assert extra - cost + len(state) == 8
                    children.append({"index": len(children), "pair_positions": [i, j],
                                     "op": op, "keep_mask": keep, "extra": extra - cost,
                                     "next_budget": 7, "retained_parent_positions": retained,
                                     "frontier_raw_signatures": [hex(x) for x in state]})
    groups.append({"parent_index": parent_index, "parent_extra": extra,
                   "parent_budget": 8, "child_count": len(children),
                   "keep_counts": dict(Counter(c["keep_mask"] for c in children)),
                   "children": children})
out = {"task": "L-meta-11315", "full_assignment_domain": 128, "paired_width": 4320,
       "first_level_source_sha256": hashlib.sha256((P / "independent-first-level.json").read_bytes()).hexdigest(),
       "all_raw_and_paired_guards_agree": True, "recursive_search_run": False,
       "groups": groups}
(P / "independent-second-level.json").write_text(json.dumps(out, indent=2) + "\n")
summary = [{k: v for k, v in group.items() if k != "children"} for group in groups]
(P / "independent-second-level-summary.json").write_text(json.dumps(summary, indent=2) + "\n")
print(json.dumps(summary, indent=2))
