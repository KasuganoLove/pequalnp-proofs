"""Check the 7 remaining monotone gates after OR(0,2) for a six-wire separator.

Uses every true/false pair at Hamming distance one or two for the nine-input
edge function.  A pair agreeing on every selected wire defeats any decoder.
An active state retains only distinct nonconstant wire functions.  On a useful
binary step, each operand is either retained or consumed.  Reading the circuit
backwards justifies discarding dead gates and wires.  With r useful gates left,
an active state cannot contain more than 6+r distinct wires, since each binary
gate can lower its size by at most one.  The reachability search checks all
depths from zero to seven and deduplicates only exact active states.
"""

from collections import Counter
from itertools import combinations
from time import monotonic


EDGES = ((0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5),
         (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5))
ROWS = range(512)
RAW = tuple(sum(1 << x for x in ROWS if x & (1 << i)) for i in range(9))
SEED = RAW[0] | RAW[2]
ALL_ROWS = (1 << 512) - 1


def target(mask):
    return any(mask & (1 << a) and mask & (1 << b) for a, b in EDGES)


PAIRS = [(p, n) for p in ROWS if target(p) for n in ROWS
         if not target(n) and (p ^ n).bit_count() <= 2]
ALL_PAIRS = (1 << len(PAIRS)) - 1


def samples(word):
    return tuple(sum(1 << j for j, pair in enumerate(PAIRS) if word >> pair[k] & 1)
                 for k in (0, 1))


TABLE = {w: samples(w) for w in (*RAW, SEED)}


def check_raw_necessary():
    # Even if the decoder sees the seed, each of the nine raw input columns
    # must be in the initial active set. Exhibit a pair differing on that raw
    # column alone with an unchanged seed and different target values.
    for i in range(9):
        assert any((p ^ n) == 1 << i and ((SEED >> p) ^ (SEED >> n)) & 1 == 0
                   for p, n in PAIRS)


def keep_children(state, limit):
    width = len(state)
    carries = [TABLE[w][0] ^ TABLE[w][1] for w in state]
    for i, j in combinations(range(width), 2):
        wi, wj = state[i], state[j]
        others = 0
        for k, c in enumerate(carries):
            if k != i and k != j:
                others |= c
        for is_or in (False, True):
            new = wi | wj if is_or else wi & wj
            if new in (0, ALL_ROWS) or new in state:
                continue
            if new not in TABLE:
                a, b = TABLE[wi], TABLE[wj]
                TABLE[new] = (a[0] | b[0], a[1] | b[1]) if is_or else (
                    a[0] & b[0], a[1] & b[1])
            p, n = TABLE[new]
            base = others | (p ^ n)
            for keep_i, keep_j in ((False, False), (False, True),
                                    (True, False), (True, True)):
                if width - 1 + keep_i + keep_j > limit:
                    continue
                sep = base | (carries[i] if keep_i else 0) | (carries[j] if keep_j else 0)
                if sep != ALL_PAIRS:
                    continue
                nxt = [w for k, w in enumerate(state)
                       if (k != i or keep_i) and (k != j or keep_j)]
                yield tuple(sorted((*nxt, new)))


def check_root(seed_used):
    states = {tuple(sorted((*RAW, SEED) if seed_used else RAW))}
    start = monotonic()
    counts = []
    for depth in range(8):
        widths = Counter(map(len, states))
        counts.append(len(states))
        print(f"seed={seed_used} depth={depth} states={len(states)} "
              f"min_width={min(widths, default=None)}", flush=True)
        if widths and min(widths) <= 6:
            raise RuntimeError("Found a state requiring a full truth-table factorization check")
        if not states or depth == 7:
            break
        limit = 6 + 7 - (depth + 1)
        states = {child for state in states for child in keep_children(state, limit)}
    print(f"seed={seed_used} states_by_depth={counts} elapsed_s={monotonic()-start:.2f}")


if __name__ == "__main__":
    check_raw_necessary()
    print(f"full truth-table rows={len(ROWS)} sampled true/false pairs={len(PAIRS)}")
    for seed_used in (False, True):
        check_root(seed_used)
