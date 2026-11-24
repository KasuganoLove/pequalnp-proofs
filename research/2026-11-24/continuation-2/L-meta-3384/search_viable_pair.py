"""Coupled rewiring search over the recorded optimal monotone live-state DAG.

The source DAG is produced by theta_source.py. This is computational evidence;
it does not prove normalization of arbitrary Lean circuits or cover NOT gates.
"""
import json
from functools import cache
from itertools import combinations
from pathlib import Path
from time import monotonic

HERE=Path(__file__).resolve().parent
signals=[int(s,16) for s in json.loads((HERE/'theta/theta1922-optimal.json').read_text())]
index={w:i for i,w in enumerate(signals)}
raw=[sum(1<<r for r in range(512) if r>>i&1) for i in range(9)]
vertices=[1,2,3,5,6,7,8]
roots=tuple(sorted(index[raw[i]] for i in vertices))
edges=[(1,2),(2,3),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]
target=0
for a,b in edges:target|=raw[a]&raw[b]
goal=target|raw[1]|raw[5]
ONE=(1<<512)-1
counted=index[raw[3]]

def decode(mask):return tuple(i for i in range(len(signals)) if mask>>i&1)

layers={int(k):{decode(s) for s in states} for k,states in json.loads((HERE/'theta/theta1922-states.json').read_text()).items()}
sample_rows=[r for r in range(512) if r&17==0]
positive=[r for r in sample_rows if goal>>r&1 and not any((r^(1<<v)) in sample_rows and goal>>(r^(1<<v))&1 for v in vertices if r>>v&1)]
negative=[r for r in sample_rows if not goal>>r&1 and not any((r|(1<<v)) in sample_rows and not goal>>(r|(1<<v))&1 for v in vertices if not r>>v&1)]
FULL=(1<<(len(positive)*len(negative)))-1

@cache
def sep(w):
    row=sum(1<<j for j,r in enumerate(negative) if not w>>r&1)
    return sum(row<<(j*len(negative)) for j,r in enumerate(positive) if w>>r&1)

@cache
def transitions(cap,old):
    result=[]
    for ai,bi in combinations(range(len(old)),2):
        a,b=old[ai],old[bi]
        rest=[v for k,v in enumerate(old) if k not in (ai,bi)]
        for op in (0,1):
            z=signals[a]&signals[b] if op==0 else signals[a]|signals[b]
            if z not in index or index[z] in old:continue
            zi=index[z]
            for ka,kb in ((0,0),(1,0),(0,1),(1,1)):
                child=tuple(sorted(rest+[zi]+([a] if ka else [])+([b] if kb else [])))
                if child in layers[cap-1]:result.append((ai,bi,a,b,op,zi,ka,kb,child))
    return result

start=monotonic()
layer={(roots,tuple(signals[i] for i in roots),(),0):[]}
for cap in range(11,0,-1):
    nxt={}
    for (old,changed,pins,count),path in layer.items():
        for ai,bi,a,b,op,zi,ka,kb,child in transitions(cap,old):
            nc=count+(op==1 and counted in (a,b))
            if nc>=2:continue
            rest={old[k]:changed[k] for k in range(len(old)) if k not in (ai,bi)}
            for sa,sb in ((0,0),(1,0),(0,1),(1,1)):
                np=tuple(sorted(set(pins)|({a} if sa else set())|({b} if sb else set())))
                if len(np)>2:continue
                av=ONE if sa else changed[ai]
                bv=ONE if sb else changed[bi]
                new=dict(rest)
                new[zi]=av&bv if op==0 else av|bv
                if ka:new[a]=changed[ai]
                if kb:new[b]=changed[bi]
                values=tuple(new[v] for v in child)
                separation=0
                for w in values:separation|=sep(w)
                if separation!=FULL:continue
                key=(child,values,np,nc)
                if key not in nxt:nxt[key]=path+[(a,b,op,sa,sb,ka,kb)]
        if len(nxt)>250000 or monotonic()-start>180:
            print('BOUND',cap,len(layer),len(nxt),'seconds',round(monotonic()-start,2),flush=True)
            raise SystemExit(2)
    print('remaining',cap-1,'coupled states',len(nxt),'seconds',round(monotonic()-start,2),flush=True)
    layer=nxt

for (old,changed,pins,count),path in layer.items():
    if old!=(index[target],) or changed!=(goal,):continue
    locations={index[raw[v]]:i for i,v in enumerate(vertices)}
    gates=[]
    physical_pins=set()
    for a,b,op,sa,sb,ka,kb in path:
        aa,bb=locations[a],locations[b]
        if sa:physical_pins.add(aa)
        if sb:physical_pins.add(bb)
        gates.append({'op':['and','or'][op],'inputs':[aa,bb],'modified_inputs':[0 if sa else aa+1,0 if sb else bb+1]})
        z=signals[a]&signals[b] if op==0 else signals[a]|signals[b]
        locations[index[z]]=7+len(gates)-1
    if len(physical_pins)>2:continue
    result={'gates':gates,'pins':sorted(physical_pins),'or_readers_of_2':count,'output':17}
    (HERE/'viable-counterexample.json').write_text(json.dumps(result,indent=2)+'\n')
    print('COUNTEREXAMPLE',json.dumps(result),flush=True)
    break
else:
    print('No counterexample in this monotone live-state search.',flush=True)
