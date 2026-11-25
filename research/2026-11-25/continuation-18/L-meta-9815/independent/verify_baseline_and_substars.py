#!/usr/bin/env python3
"""Independent scalar baseline verification and bounded star-subcircuit audit."""
import json,pathlib,re,itertools,collections,hashlib
BASE=pathlib.Path(__file__).resolve().parents[1];gap=json.loads((BASE/'gap.json').read_text());E=[tuple(map(int,p)) for p in re.findall(r'\(x (\d+) && x (\d+)\)',gap['statement'])]
N=14;adj=[{b for a,b in E if a==v}|{a for a,b in E if b==v} for v in range(N)]
# Explicit left-star circuit; fresh wires numbered from14.
gates=[]
def emit(op,a,b):
 gates.append([op,a,b]);return N+len(gates)-1
outs=[]
for u in range(7):
 ns=sorted(adj[u]);w=ns[0]
 for v in ns[1:]:w=emit('or',w,v)
 outs.append(emit('and',u,w))
w=outs[0]
for v in outs[1:]:w=emit('or',w,v)
errors=[]
for mask in range(1<<N):
 vals=[bool(mask>>i&1) for i in range(N)]
 for op,a,b in gates:vals.append((vals[a] and vals[b]) if op=='and' else (vals[a] or vals[b]))
 target=any((mask>>u&1) and (mask>>v&1) for u,v in E)
 if vals[w]!=target:errors.append(mask)
cover=[]
for k in range(N+1):
 cover=[list(c) for c in itertools.combinations(range(N),k) if all(u in c or v in c for u,v in E)]
 if cover:break
baseline={'n':N,'edges':E,'gates':gates,'output':w,'size':len(gates),'and_count':sum(g[0]=='and' for g in gates),'or_count':sum(g[0]=='or' for g in gates),'assignments_tested':1<<N,'errors':errors,'minimum_cover':k,'all_minimum_covers':cover,'formal_status':'ordinary scalar Python verification only'}
(BASE/'independent/baseline-25.json').write_text(json.dumps(baseline,indent=2)+'\n')
# Delete pendant vertices only while a nonempty2-core exists. Each removed leaf
# is a dependent variable; fixing it false preserves a nonconstant target.
# Forest cases use checked forest theorem instead, avoiding the last-edge issue.
rows=[]
for side in [range(7),range(7,14)]:
 for k in range(1,5):
  for centers in itertools.combinations(side,k):
   verts=set(centers)|set().union(*(adj[v] for v in centers));ee={tuple(sorted((v,w))) for v in centers for w in adj[v]};original=len(ee);removed=[]
   while True:
    dd=collections.Counter(v for e in ee for v in e);leaves=[v for v,d in dd.items() if d==1]
    if not leaves:break
    v=min(leaves);removed.append(v);ee={e for e in ee if v not in e}
   dd=collections.Counter(v for e in ee for v in e);nn=len(dd);mm=len(ee);base=None;kind='unclassified';source=None
   if not ee:base=original+k-1;kind='forest';source='PEqualNP.MetaComplexity.L104'
   elif all(d==2 for d in dd.values()):base=nn+(nn+1)//2-1+len(removed);kind='cycle_with_pendant_trees';source='PEqualNP.MetaComplexity.L106 + gate_elim'
   elif nn==8 and mm==9 and sorted(dd.values())==[2]*6+[3]*2:
    hubs=[v for v,d in dd.items() if d==3];bb={v:{w for e in ee if v in e for w in e if w!=v} for v in dd};lengths=[]
    for start in bb[hubs[0]]:
     prev=hubs[0];cur=start;length=1
     while cur not in hubs:
      nxt=next(iter(bb[cur]-{prev}));prev,cur=cur,nxt;length+=1
     if cur==hubs[1]:lengths.append(length)
    if sorted(lengths)==[3,3,3]:base=12+len(removed);kind='theta333_with_pendant_trees';source='L-meta-516 + gate_elim'
   rows.append({'centers':list(centers),'edge_count':original,'standard_star_cost':original+k-1,'removed_pendants':removed,'core_n':nn,'core_e':mm,'core_degrees':sorted(dd.values()),'checked_route_lower':base,'kind':kind,'source':source,'route_meets_star_cost':base==original+k-1})
summary={'scope':'Only replacement of the selected stars as a standalone subfunction; no restriction on arbitrary global circuits is inferred. No new Lean certificate.','counts_by_center_count':{str(k):{'total':sum(len(r['centers'])==k for r in rows),'route_meets_standard_cost':sum(len(r['centers'])==k and r['route_meets_star_cost'] for r in rows)} for k in range(1,5)},'unresolved_four_star_cases':[r for r in rows if len(r['centers'])==4 and not r['route_meets_star_cost']],'all_cases':rows}
(BASE/'independent/substar-audit.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({'baseline_size':len(gates),'assignments':1<<N,'errors':len(errors),'cover_number':len(cover[0]),'cover_count':len(cover),'substar_counts':summary['counts_by_center_count'],'unresolved_four_star_count':len(summary['unresolved_four_star_cases']),'unresolved_core_types':dict(collections.Counter(str((r['core_n'],r['core_e'],r['core_degrees'])) for r in summary['unresolved_four_star_cases']))},indent=2))
