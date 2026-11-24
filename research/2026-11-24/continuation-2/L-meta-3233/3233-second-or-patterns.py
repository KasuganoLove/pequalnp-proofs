from itertools import product
import json

# Wire 9 is the first OR output; wire 10 represents every not-yet-present index.
perm = [1, 0, 5, 8, 6, 2, 4, 7, 3, 9, 10]
edges = {frozenset(e) for e in [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]}
assert all(perm[perm[i]] == i for i in range(11))
assert {frozenset(perm[i] for i in e) for e in edges} == edges
assert {perm[4], perm[6]} == {4, 6}
wire = [frozenset([i]) for i in range(9)] + [frozenset([4, 6]), frozenset()]
inputs = [()] + [(i,) for i in range(11)] + list(product(range(11), repeat=2))
def signal(xs):
    return frozenset().union(*(wire[i] for i in xs))
def acted(s):
    return frozenset(perm[i] for i in s)
def key(s):
    return tuple(sorted(s))
canonical = [xs for xs in inputs if xs <= tuple(perm[i] for i in xs)]
all_signals = {signal(xs) for xs in inputs}
canonical_signals = {signal(xs) for xs in canonical}
representatives = {min(key(s), key(acted(s))) for s in all_signals}
assert len(all_signals) == 53 and len(canonical_signals) == 36
assert len(representatives) == 30
print(json.dumps({
    "bounded_input_lists": len(inputs),
    "ordered_canonical_input_lists": len(canonical),
    "distinct_or_signals": len(all_signals),
    "signals_after_posted_ordered_canonical_test": sorted(map(key, canonical_signals)),
    "semantic_orbit_representatives": sorted(representatives),
    "limitation": "Finite Boolean calculation only. Thirty orbit representatives require an additional sound normalization argument; the posted list-order condition alone leaves 36 signals. No gate lower bound follows from these counts."
}, indent=2))
