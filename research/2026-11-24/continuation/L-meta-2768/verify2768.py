"""Numerical one-NOT search for OR(0,3). Run in or beside the pequalnp-proofs checkout.
The projection bounds come from L_meta_1667. Its raw lower bound also excludes
wasting a gate in a 15-gate circuit. Before the NOT, surviving wires must
separate every opposite-value pair. After it, they must separate each pair in
the correct direction, since the remaining circuit is monotone. The search
uses all opposite-value pairs within Hamming distance two and all minimal
positive versus maximal negative pairs. An empty frontier is a computational
result. Its translation into a kernel-checked certificate remains open.
"""
from pathlib import Path
from functools import reduce
import operator
import re
import time

work = Path(__file__).resolve().parent
certificate = Path("lean/PEqualNP/Outside/L_meta_1667.lean")
locations = [work / "pequalnp-proofs", work, *work.parents]
source = next(root / certificate for root in locations if (root / certificate).is_file())
src = source.read_text(encoding="utf8")
def line_for(name):
    return next(t for t in src.splitlines() if t.startswith('def '+name+' '))

all512 = (1<<512)-1
raw = tuple(int(a,16) for a in re.findall(r'0x([0-9a-f]+)',line_for('inputs')))
seed = raw[0]|raw[3]
goal = int(line_for('graph').split(':= ')[1],16)
positive=[p for p in range(512) if goal>>p&1]
negative=[n for n in range(512) if not goal>>n&1]
maxfalse={n for n in negative if all(goal>>(n | (1<<i))&1 for i in range(9) if not n>>i&1)}
pairs=[(p,n) for p in positive for n in negative if (p^n).bit_count()<=2 or (p.bit_count()==2 and n in maxfalse)]
all768=(1<<len(pairs))-1
sig={w:tuple(sum(1<<j for j,t in enumerate(pairs) if t[k]>>i&1) for k in (0,1)) for i,w in enumerate(raw)}
def op(o,x,y,mask):
    return x & y if o==0 else (x | y if o==1 else x^mask)
def operate(o,a,b):
    z=op(o,a,b,all512)
    if z not in sig:
        pa,qa=sig[a]
        pb,qb=sig[b]
        sig[z]=op(o,pa,pb,all768),op(o,qa,qb,all768)
    return z
operate(1,raw[0],raw[3])
cols=[]
for ci,(z,o,_,_,lb) in enumerate(tuple(map(int,c)) for c in re.findall(r'\((\d+),(\d+),(\d+),(\d+),(\d+)\)',line_for('deadcolumns'))):
    D=sum(1<<r for r in range(512) if r & z==0 and r & o==o)
    cols.append((ci,D,lb, {0,D,*[r&D for r in raw]}))

def next_layer(frontier,cap):
    layer={}
    statistics=[0,0,0,0]
    used_rules={}
    start=time.monotonic()
    for par,((ws,used),(ops,bank)) in enumerate(frontier.items()):
        projected=[]
        for ci,D,lb,base in cols:
            avail=set(base)
            paid=0
            price=0
            for t,(o,i,j) in enumerate(ops):
                z=bank[9+t]&D
                if z not in avail:
                    paid|=1<<t
                    price+=1
                    avail.add(z)
            flags=tuple((w&D in (0,D)) for w in ws)
            margin=lb+sum(flags)-(cap-1)-price
            if margin>=0:
                projected.append((ci,D,paid,avail,margin,flags))
        wsindices=[bank.index(w) for w in ws]
        cov={}
        for i in range(len(ws)):
            for j in range(i,len(ws)):
                for o in ((() if used else (2,)) if i==j else (0,1)):
                    z=operate(o,ws[i],ws[j])
                    if z in (0,all512) or z in ws: continue
                    for di,dj in (((1,0),(0,0)) if i==j else ((1,1),(1,0),(0,1),(0,0))):
                        nn=len(ws)+1-di-dj
                        now_used=used or o==2
                        if nn>cap-(not now_used): continue
                        orient=now_used
                        rm=((i if di else -1),(j if dj else -1))
                        key=(*rm,orient)
                        if key not in cov:
                            cov[key]=reduce(operator.or_,((sig[w][0] & ~sig[w][1]) if orient else (sig[w][0]^sig[w][1]) for t,w in enumerate(ws) if t not in rm),0)
                        wz=(sig[z][0]&~sig[z][1]) if orient else sig[z][0]^sig[z][1]
                        if cov[key]|wz != all768: continue
                        statistics[0]+=1
                        witness=None
                        for ci,D,paid,avail,margin,flags in projected:
                            v=z&D
                            if margin+(v==0 or v==D)-di*flags[i]-dj*flags[j]-(v not in avail)>0:
                                witness=(ci,paid)
                                break
                        if witness:
                            used_rules.setdefault(par,set()).add(witness)
                            statistics[1]+=1
                            continue
                        child=tuple(sorted([z]+[w for t,w in enumerate(ws) if t not in rm]))
                        if goal in child:
                            raise ValueError(('FOUND TARGET',cap,ops,o,i,j))
                        child=(child,now_used)
                        if child not in layer:
                            layer[child]=(ops+((o,wsindices[i],wsindices[j]),),bank+(z,))
                            statistics[2]+=1
                        else:
                            statistics[3]+=1
    return layer,used_rules,statistics

if __name__=='__main__':
    print('raw',len(raw),'columns',len(cols),'sig',len(sig),flush=True)
    frontier={(tuple(sorted(raw+(seed,))),False):(((1,0,3),),raw+(seed,))}
    for cap in range(14,0,-1):
        future, rules, stats = next_layer(frontier,cap)
        print('cap',cap,'states',len(frontier),'next',len(future),'transition statistics',stats,flush=True)
        if not future:
            break
        frontier=future
    else:
        raise AssertionError('search did not exhaust')

