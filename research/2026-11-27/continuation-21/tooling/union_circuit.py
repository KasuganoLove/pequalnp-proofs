#!/usr/bin/env python3
"""Generic common-subexpression synthesis of a family of set unions.

No target problem is embedded. Inputs are integer atom masks; output wires are
unions of the supplied singleton atoms. The result is checked by set semantics.
"""
from collections import Counter
from itertools import combinations
import random

def synthesize_unions(masks, width, seed=0):
    rng = random.Random(seed)
    work = [{i for i in range(width) if mask >> i & 1} for mask in masks]
    nodes = [1 << i for i in range(width)]
    gates = []
    known = {v:i for i,v in enumerate(nodes)}
    while True:
        freq = Counter(pair for terms in work for pair in combinations(sorted(terms),2))
        useful = [(p,f) for p,f in freq.items() if f>1]
        if not useful: break
        best = max(f for p,f in useful)
        choices = [p for p,f in useful if f == best]
        a,b = rng.choice(choices)
        mask = nodes[a] | nodes[b]
        if mask in known:
            k = known[mask]
        else:
            k = len(nodes)
            nodes.append(mask)
            gates.append((a,b))
            known[mask] = k
        for terms in work:
            if a in terms and b in terms:
                terms.difference_update((a,b))
                terms.add(k)
    outputs = []
    for terms, wanted in zip(work,masks):
        if wanted == 0:
            outputs.append(None)
            continue
        if wanted in known:
            outputs.append(known[wanted])
            continue
        order = list(terms)
        rng.shuffle(order)
        k = order[0]
        for b in order[1:]:
            mask = nodes[k] | nodes[b]
            if mask in known:
                k = known[mask]
            else:
                a = k
                k = len(nodes)
                nodes.append(mask)
                gates.append((a,b))
                known[mask] = k
        assert nodes[k] == wanted
        outputs.append(k)
    assert all((0 if w is None else nodes[w]) == m for w,m in zip(outputs,masks))
    used = set()
    def visit(w):
        if w is None or w < width or w in used: return
        used.add(w)
        for parent in gates[w-width]: visit(parent)
    for w in outputs: visit(w)
    remap = {i:i for i in range(width)}
    pruned = []
    for j,(a,b) in enumerate(gates):
        if width+j in used:
            remap[width+j] = width+len(pruned)
            pruned.append((remap[a],remap[b]))
    return {'width':width,'gates':pruned,'outputs':[None if w is None else remap[w] for w in outputs]}

def repeat_synthesis(masks,width,attempts=50):
    return min((synthesize_unions(masks,width,seed) for seed in range(attempts)),key=lambda r:len(r['gates']))
