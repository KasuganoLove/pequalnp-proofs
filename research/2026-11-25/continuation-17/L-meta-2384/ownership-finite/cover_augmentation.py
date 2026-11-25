"""Exhaust all edge-deletion sets for the exact eleven-vertex graph of 2384.

Ordinary finite computation only.  No circuit assumptions are asserted here.
"""
from pathlib import Path
from collections import Counter, defaultdict
import hashlib
import json
import time

OUT = Path(__file__).resolve().parent
N = 11
E = [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10),
     (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9),
     (6, 7), (6, 10), (7, 9), (8, 9)]
V = (1 << N) - 1
M = 1 << len(E)
started = time.monotonic()
adj = [0] * N
for a, b in E:
    adj[a] |= 1 << b
    adj[b] |= 1 << a

# A largest G-independent subset of every induced vertex set.
alpha = [0] * (V + 1)
independent_witness = [0] * (V + 1)
for s in range(1, V + 1):
    bit = s & -s
    v = bit.bit_length() - 1
    without = s ^ bit
    available = without & ~adj[v]
    skip = independent_witness[without]
    take = independent_witness[available] | bit
    chosen = min((skip, take), key=lambda x: (-x.bit_count(), x))
    independent_witness[s] = chosen
    alpha[s] = chosen.bit_count()

# For each potential residual cover K, determine its uncovered ORIGINAL edges
# and the minimum number of extra vertices needed to extend this particular K.
uncovered = [0] * (V + 1)
augmentation = [0] * (V + 1)
addition = [0] * (V + 1)
best = [None] * M
for k in range(V + 1):
    u = sum(1 << i for i, (a, b) in enumerate(E)
            if not ((k >> a & 1) or (k >> b & 1)))
    i = V ^ k
    a = i ^ independent_witness[i]
    uncovered[k] = u
    augmentation[k] = a.bit_count()
    addition[k] = a
    candidate = (k.bit_count(), a.bit_count(), k)
    if best[u] is None or candidate < best[u]:
        best[u] = candidate

# K covers G-U iff uncovered(K) is a submask of U.  Subset-min convolution
# first minimizes |K|, then its extension cost, then its numeric mask.
for bit in range(len(E)):
    step = 1 << bit
    for u in range(M):
        if u & step:
            candidate = best[u ^ step]
            if candidate is not None and (best[u] is None or candidate < best[u]):
                best[u] = candidate

tau_g = N - alpha[V]
assert tau_g == 7
histogram = Counter()
by_u = defaultdict(list)
extension_gaps = Counter()
examples = {}
all_rows = []
for u, chosen in enumerate(best):
    assert chosen is not None
    tau, need, k = chosen
    a = addition[k]
    # Direct checks of the emitted witnesses, independently of the SOS update.
    assert uncovered[k] & ~u == 0
    assert uncovered[k | a] == 0
    assert k & a == 0 and a.bit_count() == need
    assert need >= tau_g - tau
    size_u = u.bit_count()
    minimum_r = size_u + need
    histogram[(size_u, tau, need)] += 1
    by_u[size_u].append((need, tau, u))
    gap = need - (tau_g - tau)
    extension_gaps[gap] += 1
    all_rows.append([u, tau, need, k, a, minimum_r])
    for name, condition in [
        ("smallest_nonzero_augmentation", need > 0),
        ("minimum_residual_cover_cannot_extend_to_minimum_full_cover", gap > 0),
        ("unqualified_u_le_r_lt_two_u_fails_with_r_at_least_two",
         size_u >= 2 and need > 0),
    ]:
        if condition and name not in examples:
            examples[name] = {
                "deleted_edge_mask": u,
                "deleted_edges": [e for i, e in enumerate(E) if u >> i & 1],
                "u_card": size_u,
                "residual_cover_number": tau,
                "minimum_augmentation": need,
                "minimum_r": minimum_r,
                "chosen_minimum_residual_cover": [v for v in range(N) if k >> v & 1],
                "chosen_addition": [v for v in range(N) if a >> v & 1],
                "r_for_failure": size_u if size_u >= 2 else None,
            }

serialized = json.dumps(all_rows, separators=(",", ":")).encode()
result = {
    "task": "L-meta-2384",
    "vertices": N,
    "edges": E,
    "edge_count": len(E),
    "full_graph_cover_number": tau_g,
    "edge_deletion_sets_exhausted": M,
    "meaning": "minimum_r(U)=|U|+min_{K minimum cover of G-U} minimum |A| with K union A covering G",
    "joint_histogram": [
        {"u_card": u, "residual_cover_number": tau,
         "minimum_augmentation": need, "count": count}
        for (u, tau, need), count in sorted(histogram.items())
    ],
    "augmentation_by_u_card": [
        {"u_card": u, "sets": len(values),
         "minimum_augmentation": min(t[0] for t in values),
         "maximum_augmentation": max(t[0] for t in values),
         "augmentation_counts": dict(sorted(Counter(t[0] for t in values).items()))}
        for u, values in sorted(by_u.items())
    ],
    "excess_over_cover_number_drop": dict(sorted(extension_gaps.items())),
    "exceptional_masks": [u for u, tau, need, _, _, _ in all_rows
                          if need > tau_g - tau],
    "examples": examples,
    "all_witness_rows_sha256": hashlib.sha256(serialized).hexdigest(),
    "all_witness_rows_json_bytes": len(serialized),
    "all_witness_rows_columns": ["U", "tau(G-U)", "augmentation", "K", "A", "minimum_r"],
    "elapsed_seconds": time.monotonic() - started,
    "formal_certificate": False,
    "circuit_constraints_used": False,
}
(OUT / "results.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({k: result[k] for k in [
    "edge_deletion_sets_exhausted", "full_graph_cover_number",
    "augmentation_by_u_card", "excess_over_cover_number_drop", "examples",
    "elapsed_seconds"]}, indent=2))
