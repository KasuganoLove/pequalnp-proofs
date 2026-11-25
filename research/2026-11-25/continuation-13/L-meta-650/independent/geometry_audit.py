"""Deterministic finite geometry and restriction-obstacle audit, not a proof of650."""
from pathlib import Path
from collections import Counter
from itertools import combinations
import json,re
P=Path(__file__).resolve().parent
E=[tuple(map(int,p)) for p in re.findall(r'\((\d+), (\d+)\)',(P.parent/'statement.txt').read_text())]
adj={v:{b if a==v else a for a,b in E if v in (a,b)} for v in range(26)}
lines=[sum(1<<p for p,l in E if l==13+j) for j in range(13)]
profiles={}
for k in [3,4,5,6,7]:
    counts=Counter();representatives={}
    for s in range(8192):
        if s.bit_count()!=k:continue
        profile=tuple(sum((s&l).bit_count()==i for l in lines) for i in range(5))
        counts[profile]+=1;representatives.setdefault(profile,s)
    profiles[str(k)]=[{'lines_by_intersection_size':prof,'subsets':num,'representative_mask':representatives[prof],'pendant_lines':prof[1],'core_vertices':k+sum(prof[2:]),'core_edges':sum(i*prof[i] for i in range(2,5))} for prof,num in sorted(counts.items())]
max3=max(r['lines_by_intersection_size'][3] for r in profiles['7'])
assert max3==6
cycles=[];vertex_count=Counter();wedge_count=Counter()
for pts in combinations(range(13),3):
    ls=[next(iter(adj[a]&adj[b])) for a,b in combinations(pts,2)]
    if len(set(ls))<3:continue
    free=set(pts)|set(ls)
    assert len(free)==6 and all(len(adj[v]&free)==2 for v in free)
    cycles.append(sorted(free))
    for v in free:
        vertex_count[v]+=1;a,b=sorted(adj[v]&free);wedge_count[(v,a,b)]+=1
assert len(cycles)==234 and set(vertex_count.values())=={54} and set(wedge_count.values())=={9}
# A negative control for an UNCONDITIONAL averaging bound: concatenate the
# point-star and line-star implementations of F, then OR their equal outputs.
def stars(side):
    gs=[]
    def emit(op,a,b):gs.append((op,min(a,b),max(a,b)));return 26+len(gs)-1
    outs=[]
    for c in range(13*side,13*(side+1)):
        a,b,c1,d=sorted(adj[c]);u=emit(1,a,b);v=emit(1,c1,d);w=emit(1,u,v);outs.append(emit(0,c,w))
    o=outs[0]
    for w in outs[1:]:o=emit(1,o,w)
    return gs,o
A,ao=stars(0);B,bo=stars(1)
def shift(w):return w if w<26 else w+len(A)
D=A+[(op,shift(a),shift(b)) for op,a,b in B]+[(1,ao,shift(bo))];do=26+len(D)-1
assert len(D)==129
assert all(0<=a<b<26+j for j,(op,a,b) in enumerate(D))
live_full={do}
for j in reversed(range(len(D))):
    if 26+j in live_full:live_full.update(D[j][1:])
assert all(v in live_full for v in range(26+len(D)))
# Constant propagation, unary/duplicate-operand bypass and dead-gate pruning.
def restrict(gs,out,free):
    m=len(free);ix={v:i for i,v in enumerate(free)}
    stats=[('v',ix[v]) if v in ix else ('c',False) for v in range(26)];new=[]
    for op,a,b in gs:
        x,y=stats[a],stats[b]
        if x[0]=='c' and y[0]=='c':z=('c',(x[1] or y[1]) if op else (x[1] and y[1]))
        elif x[0]=='c':z=x if x[1]==bool(op) else y
        elif y[0]=='c':z=y if y[1]==bool(op) else x
        elif x==y:z=x
        else:new.append((op,x[1],y[1]));z=('v',m+len(new)-1)
        stats.append(z)
    assert stats[out][0]=='v'
    output=stats[out][1];live={output}
    for j in reversed(range(len(new))):
        if m+j in live:live.update(new[j][1:])
    kept=sum(m+j in live for j in range(len(new)))
    return kept
restriction_sizes=[restrict(D,do,f) for f in cycles]
assert set(restriction_sizes)=={17}
control={'circuit_size':129,'raw_inputs':26,'surplus':104,'cofactor_sizes':dict(Counter(restriction_sizes)),'cofactor_surplus_sum':sum(k-6+1 for k in restriction_sizes),'eighteen_times_original_surplus':18*104,'uniform_unconditional_bound_holds':False,'limitation':'This deliberately redundant circuit is not minimum. The reported violation applies to the explicit local constant-propagation, operand-bypass, and dead-pruning procedure in geometry_audit.py. It does not refute a bound for minimum original circuits or one permitting independently minimum cofactors.'}
record={'graph_edges':E,'profiles':profiles,'seven_point_max_exactly_three_lines':max3,'no_induced_heawood_reason':'An induced Heawood needs7 lines meeting7 selected points in exactly3; maximum is6.','six_cycles':cycles,'six_cycle_count':234,'cycles_through_every_vertex':54,'cycles_through_every_wedge':9,'required_surplus_sum_from_cycle8_gate_bound':702,'desired_full_surplus':39,'unproved_sufficient_averaging_inequality':'For a normalized minimum full circuit, total cofactor surplus <=18*original surplus. No proof is supplied.','unconditional_negative_control':control}
(P/'geometry-and-restriction-audit.json').write_text(json.dumps(record,indent=2)+'\n')
(P/'redundant-averaging-control.json').write_text(json.dumps({'gates':D,'output':do,'input_count':26},indent=2)+'\n')
print(json.dumps({'cycles':234,'max_three_lines_on_seven_points':max3,'control':control}))
