"""Enumerate live states of optimal monotone programs on the x0=x4=0 restriction."""
from functools import cache
from itertools import combinations
from time import monotonic
from pathlib import Path
import json
import argparse

edges = ((0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5))
raw = tuple(sum(1<<row for row in range(512) if (row>>i)&1) for i in range(9))

mask = 494
vertices = [i for i in range(9) if mask >> i & 1]
roots = tuple(raw[i] for i in vertices)
subedges = [(a,b) for a,b in edges if a in vertices and b in vertices]
pos = [1 << a | 1 << b for a,b in subedges]
neg = [r for r in range(512) if r & mask == r and not any(r & p == p for p in pos)]
neg = [r for r in neg if not any(r != s and r & s == r for s in neg)]
target = 0
for a,b in subedges:
    target |= raw[a] & raw[b]
full = (1 << (len(pos)*len(neg))) - 1


@cache
def sep(w):
    n = sum(1 << j for j,r in enumerate(neg) if not w >> r & 1)
    return sum(n << (len(neg)*j) for j,r in enumerate(pos) if w >> r & 1)


def nexts(ws,cap):
    for i,a in enumerate(ws):
        for j in range(i+1,len(ws)):
            b = ws[j]
            rest = tuple(w for k,w in enumerate(ws) if k not in (i,j))
            missed = full
            for w in rest:
                missed &= ~sep(w)
            for z in (a&b,a|b):
                if z in ws:
                    continue
                without = missed & ~sep(z)
                for ka,kb in ((0,0),(1,0),(0,1),(1,1)):
                    if len(rest)+1+ka+kb > cap:
                        continue
                    if without & ~(sep(a) if ka else 0) & ~(sep(b) if kb else 0):
                        continue
                    yield tuple(sorted((*rest,z,*((a,) if ka else ()),*((b,) if kb else ())))),z


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument("--signals", action="store_true", help="Also compute all viable state layers")
    parser.add_argument("--out-dir", type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    args.out_dir.mkdir(parents=True,exist_ok=True)
    start=monotonic()
    # Associate each state with the possible first gate functions leading to it.
    layer = {tuple(sorted(roots)):0}
    tags = {}
    layers = {}
    for cap in range(11,0,-1):
        if args.signals:
            layers[cap]=set(layer)
        nxt = {}
        for i,(ws,history) in enumerate(layer.items(),1):
            for new,z in nexts(ws,cap):
                if cap==11 and z not in tags:
                    tags[z] = 1<<len(tags)
                nxt[new] = nxt.get(new,0) | (tags[z] if cap==11 else history)
            if len(nxt)>500000 or monotonic()-start > 150:
                print('BOUND',cap,i,len(layer),len(nxt),flush=True)
                raise SystemExit(2)
        print('remaining',cap,'parents',len(layer),'next',len(nxt),'seconds',round(monotonic()-start,2),flush=True)
        layer=nxt
    surviving=layer.get((target,),0)
    assert surviving, "No eleven-gate implementation was found"
    print('Possible first gates in 11-gate programs')
    for a,b in combinations(vertices,2):
        for op,z in [('AND',raw[a]&raw[b]),('OR',raw[a]|raw[b])]:
            if tags.get(z,0) & surviving:
                print(op,a,b)
    if layers:
        viable={(target,)}
        signals=set(roots)
        by_cap={0:viable}
        for cap in range(1,12):
            previous=set()
            for ws in layers.pop(cap):
                for child,z in nexts(ws,cap):
                    if child in viable:
                        previous.add(ws)
                        signals.add(z)
            viable=previous
            by_cap[cap]=viable
            print("reverse",cap,"feasible",len(viable),"signals",len(signals),flush=True)
        assert viable=={tuple(sorted(roots))}
        out=args.out_dir / "theta1922-optimal.json"
        ordered=sorted(signals)
        index={w:i for i,w in enumerate(ordered)}
        out.write_text(json.dumps([hex(w) for w in ordered]), encoding="utf-8")
        paths={cap:sorted(sum(1<<index[w] for w in ws) for ws in states)
               for cap,states in by_cap.items()}
        out.with_name("theta1922-states.json").write_text(json.dumps(paths),encoding="utf-8")
