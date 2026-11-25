#!/usr/bin/env python3
"""Generate exact star-cover baselines and bounded two-deletion seeds."""
import itertools
import json
from pathlib import Path

P=Path(__file__).resolve().parent
EDGES=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
MASK=(1<<1024)-1
RAW=[sum(1<<x for x in range(1024) if x>>i&1) for i in range(10)]
RAW.append(MASK^RAW[0])
TARGET=0
for a,b in EDGES: TARGET|=RAW[a]&RAW[b]

def evaluate(gs,o):
    w=RAW[:]
    for op,a,b in gs:
        assert a<len(w) and b<len(w)
        w.append(w[a]&w[b] if op==0 else w[a]|w[b] if op==1 else MASK^w[a])
    got=w[o]
    return ((got&~TARGET).bit_count(),(TARGET&~got).bit_count())

def erase(gs,o,j,side):
    alias=gs[j][1+side]
    wire=11+j
    def ren(w):
        return alias if w==wire else w-1 if w>wire else w
    return [g if k<j else [g[0],ren(g[1]),ren(g[2])] for k,g in enumerate(gs) if k!=j],ren(o)

def main():
    independent_masks=[m for m in range(1024) if all(not(m>>a&1 and m>>b&1) for a,b in EDGES)]
    assert max(m.bit_count() for m in independent_masks)==4
    inds=[s for s in itertools.combinations(range(10),4) if all(not(a in s and b in s) for a,b in EDGES)]
    assert len(inds)==5
    baselines=[]; seeds=[]; deleted=0
    for independent in inds:
        cover=sorted(set(range(10))-set(independent))
        internal=[e for e in EDGES if e[0] in cover and e[1] in cover]
        assert len(internal)==3
        for direction in itertools.product(range(2),repeat=3):
            assigned={v:[] for v in cover}
            orient={tuple(e):e[side] for e,side in zip(internal,direction)}
            for a,b in EDGES:
                center=orient[(a,b)] if a in cover and b in cover else a if a in cover else b
                assigned[center].append(b if center==a else a)
            gs=[];terms=[]
            for v in cover:
                ns=sorted(assigned[v]); assert ns
                w=ns[0]
                for u in ns[1:]: gs.append([1,w,u]);w=10+len(gs)
                gs.append([0,v,w]);terms.append(10+len(gs))
            out=terms[0]
            for u in terms[1:]:gs.append([1,out,u]);out=10+len(gs)
            assert len(gs)==20 and evaluate(gs,out)==(0,0)
            base_id=len(baselines)
            baselines.append({'id':base_id,'independent':independent,'cover':cover,'orientation':direction,'gates':gs,'output':out,'size':20})
            local=[]
            for a,b in itertools.combinations(range(20),2):
                for sa,sb in itertools.product(range(2),repeat=2):
                    # Delete later first so the earlier index is unchanged.
                    one,oo=erase(gs,out,b,sb)
                    two,oo=erase(one,oo,a,sa)
                    fp,fn=evaluate(two,oo);deleted+=1
                    local.append({'base_id':base_id,'deleted':[a,b],'redirect_sides':[sa,sb],
                                  'gates':two,'output':oo,'size':18,'false_positive':fp,'false_negative':fn})
            local.sort(key=lambda s:(s['false_positive']+s['false_negative'],s['false_positive']))
            seen=set()
            for s in local:
                key=(s['output'],tuple(map(tuple,s['gates'])))
                if key not in seen:
                    seen.add(key);seeds.append(s)
                if len(seen)>=16:break
    (P/'baselines.json').write_text(json.dumps(baselines,indent=2)+'\n')
    (P/'seeds.json').write_text(json.dumps(seeds,indent=2)+'\n')
    with (P/'seeds.txt').open('w') as f:
        f.write(str(len(seeds))+'\n')
        for s in seeds:
            f.write(str(s['output'])+'\n')
            for g in s['gates']:f.write(' '.join(map(str,g))+'\n')
    summary={'baselines':len(baselines),'independent_sets_size4':len(inds),'maximum_independent_set_size':4,
             'minimum_vertex_cover_size':6,'two_gate_deletions_checked':deleted,
             'retained_seeds':len(seeds),'truth_rows':1024,'target_true_rows':TARGET.bit_count(),
             'best_seed_errors':min(s['false_positive']+s['false_negative'] for s in seeds),
             'op_encoding':{'0':'and','1':'or','2':'not_first_operand'},'raw_inputs':'x0..x9,!x0'}
    (P/'seed-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary))

if __name__=='__main__': main()
