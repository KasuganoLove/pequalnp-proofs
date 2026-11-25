#!/usr/bin/env python3
"""Independently check the29-sample promise and its210-pair Lean packing.

This only evaluates finite data and one dispatch level; it does not recurse,
run a solver, run Lean, or certify the C++ search result.
"""
from collections import Counter
from hashlib import sha256
from itertools import combinations, product
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
problem_bytes = (HERE / "problem.json").read_bytes()
source_bytes = (HERE / "probe.cpp").read_bytes()
problem = json.loads(problem_bytes)
source = source_bytes.decode()
old_problem = json.loads((HERE.parent / "signed-probe/problem.json").read_text())
edges = [tuple(e) for e in old_problem["edges"]]
assert problem["edges"] == old_problem["edges"]
cpp_edges_text = source.split("if(id==10487)edges=", 1)[1].split(";", 1)[0]
cpp_edges = [tuple(map(int, m)) for m in re.findall(r"\{(\d+),(\d+)\}", cpp_edges_text)]
assert cpp_edges == edges
assert "const U FULL=(U(1)<<29)-1;" in source
assert "U complement(U x){return FULL^x;}" in source


def target(x):
    return any((x >> a) & 1 and (x >> b) & 1 for a, b in edges)


positive = sorted((1 << a) | (1 << b) for a, b in edges)
negative = [x for x in range(128) if not target(x)]
assert len(positive) == len(set(positive)) == 15
assert len(negative) == 14
assert all(target(x) for x in positive)
assert positive == problem["positive_sample_assignments"]
assert negative == problem["negative_sample_assignments"]
samples = positive + negative
assert len(samples) == len(set(samples)) == 29
mask29, mask210, mask420 = (1 << 29) - 1, (1 << 210) - 1, (1 << 420) - 1
assert problem["domain_mask"] == mask29
assert problem["positive_mask"] == (1 << 15) - 1
raw29 = [sum(((x >> i) & 1) << k for k, x in enumerate(samples)) for i in range(7)]
assert raw29 == problem["raw_sample_masks"]
assert all(0 <= x <= mask29 for x in raw29)
assert len(set(min(x, mask29 ^ x) for x in raw29)) == 7
for witness in problem["raw_essentiality_witnesses"]:
    i, p, n = witness["input"], witness["positive"], witness["negative"]
    assert p in positive and n in negative and (p ^ n) == 1 << i
assert sorted(w["input"] for w in problem["raw_essentiality_witnesses"]) == list(range(7))


def separates29(ws):
    def sig(k):
        return sum(((w >> k) & 1) << i for i, w in enumerate(ws))
    return {sig(k) for k in range(15)}.isdisjoint({sig(k) for k in range(15, 29)})


separating_sublists = [
    subset for subset in range(128)
    if separates29([raw29[i] for i in range(7) if (subset >> i) & 1])
]
assert separating_sublists == problem["all_initial_separating_sublists"] == [127]
paired = list(product(positive, negative))
assert len(paired) == len(set(paired)) == 210
rows420 = [
    sum(((p >> i) & 1) << k for k, (p, _) in enumerate(paired)) |
    sum(((n >> i) & 1) << (210 + k) for k, (_, n) in enumerate(paired))
    for i in range(7)
]
for k, (p, n) in enumerate(paired):
    decoded_p = sum(((w >> k) & 1) << i for i, w in enumerate(rows420))
    decoded_n = sum(((w >> (210 + k)) & 1) << i for i, w in enumerate(rows420))
    assert (decoded_p, decoded_n) == (p, n)
    assert target(decoded_p) and not target(decoded_n)


def operations(a, b, mask):
    return [a & b, a | b, a & (mask ^ b), b & (mask ^ a)]


def cuts420(ws):
    result = 0
    for w in ws:
        result |= ((w >> 210) ^ w) & mask210
    return result


records = []
op_names = ["a_and_b", "a_or_b", "a_and_not_b", "b_and_not_a"]
keep_names = ["none", "a", "b", "both"]
for pair_index, (a, b) in enumerate(combinations(range(7), 2)):
    rest = [i for i in range(7) if i not in (a, b)]
    for op_index, (w29, w420) in enumerate(zip(
            operations(raw29[a], raw29[b], mask29),
            operations(rows420[a], rows420[b], mask420))):
        assert 0 <= w29 <= mask29
        for keep in range(4):
            kept = ([a] if keep & 1 else []) + ([b] if keep & 2 else [])
            ws29 = [w29] + [raw29[i] for i in kept + rest]
            ws420 = [w420] + [rows420[i] for i in kept + rest]
            cut = cuts420(ws420) == mask210
            assert cut == separates29(ws29)
            if cut:
                extra = 4 - len(kept)
                assert extra + len(ws29) == 10
                records.append({
                    "child_index": len(records), "pair_index": pair_index,
                    "pair_indices": [a, b], "operator_index": op_index,
                    "op": op_names[op_index], "keep_index": keep,
                    "kept": keep_names[keep], "kept_indices": kept,
                    "rest_indices": rest, "frontier_recipe": ["w"] + kept + rest,
                    "new_signal29_hex": f"{w29:08x}",
                    "budget": 9, "extra": extra, "new_frontier_count": len(ws29),
                })
assert len(records) == 108

data = {
    "scope": "Independent finite data and source-delta review only; no recursive search, Lean run, or formal certificate",
    "problem_sha256": sha256(problem_bytes).hexdigest(),
    "optimized_source_sha256": sha256(source_bytes).hexdigest(),
    "script_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
    "edges_exactly_equal_full128_frozen_problem": True,
    "positive_samples_are_exactly_all15_edge_assignments": True,
    "negative_samples_are_exactly_all14_full_target_negatives": True,
    "all29_assignments_distinct_and_correctly_labelled": True,
    "raw29_masks_match": True,
    "complement_mask": mask29,
    "canonical_raw_functions_pairwise_distinct": True,
    "all7_raw_inputs_have_verified_one_bit_essentiality_witness": True,
    "only_full_initial_sublist_separates": separating_sublists,
    "paired_lean_width": 420,
    "cross_pairs": 210,
    "pair_order": "positive-major Cartesian product, both input lists ascending",
    "orientation": "low210 bits positive, high210 bits negative; F(sample)=complement(goal)",
    "rows420_hex": [f"0x{w:0105x}" for w in rows420],
    "all420_sample_bits_verified": True,
    "literal_first_level_count": len(records),
    "literal_first_level_counts_by_keep": dict(Counter(r["kept"] for r in records)),
    "all_first_level_guards_match_between29_and420": True,
    "lower_bound_implication": "Every circuit computing the full128-input target also fits these29 selected samples; excluding circuits on this weaker sample promise excludes full-target circuits. No monotonicity assumption is used.",
    "limitation": "A circuit fitting only these29 samples need not compute the full target; the implication is used only for exclusion. C++ optimized search correctness is not thereby kernel-certified.",
}
(HERE / "independent-sample-audit.json").write_text(json.dumps(data, indent=2) + '\n')
header = {"scope": "Finite literal first-level data only; not recursive rejection", "width": 420,
          "pair_width": 210, "valid_children": len(records), "recipe": "pairs,ops,keep in unchanged original order"}
(HERE / "independent-first-level-420.json").write_text(json.dumps(header, indent=2)[:-2] + ',\n  "children": [\n' +
    ',\n'.join('    ' + json.dumps(r, separators=(',', ':')) for r in records) + '\n  ]\n}\n')
assert json.loads((HERE / "independent-first-level-420.json").read_text())["children"] == records
print(json.dumps({k: v for k, v in data.items() if k != "rows420_hex"}, indent=2))
