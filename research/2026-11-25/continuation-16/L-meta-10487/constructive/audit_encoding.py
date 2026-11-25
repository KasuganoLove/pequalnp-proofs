#!/usr/bin/env python3
"""Independent gate-CNF checks and all128-row monotone12-gate control.

This is ordinary Python validation, not a Lean completeness/UNSAT certificate.
"""
from pathlib import Path
import json

P=Path(__file__).resolve().parent
M=json.loads((P/'encoding.json').read_text())
E=[(0,2),(1,3),(0,4),(1,4),(2,4),(3,4),(0,5),(1,5),(2,5),
   (3,5),(0,6),(1,6),(2,6),(3,6),(4,6)]
assert E==[tuple(e) for e in json.loads((P/'problem.json').read_text())['edges']]

def apply(op,a,b=False):
    if op=='and':return a and b
    if op=='or':return a or b
    if op=='not':return not a
    return op=='true'

relations=0
for op in M['ops']:
    for a in [False,True]:
        for b in [False,True]:
            for z in [False,True]:
                clauses={'and':[not z or a,not z or b,z or not a or not b],
                    'or':[z or not a,z or not b,not z or a or b],
                    'not':[not z or not a,z or a],
                    'false':[not z],'true':[z]}[op]
                assert all(clauses)==(z==apply(op,a,b));relations+=1

chosen=[];positive=set()
for j,g in enumerate(M['selectors']):
    op=j%5
    if op==2 and j!=2:op=1
    a=(j*3)%(7+j);b=a+j%(7+j-a)
    chosen.append((M['ops'][op],a,b))
    positive.update([g['op'][op],g['a'][a],g['b'][b]])
assert sum(op=='not' for op,_,_ in chosen)<=1
for row in range(128):
    wires=[bool(row&(1<<i)) for i in range(7)]
    for g,(op,a,b) in zip(M['selectors'],chosen):
        av,bv=wires[a],wires[b];z=apply(op,av,bv)
        for k,v in [('av',av),('bv',bv),('v',z)]:
            if v:positive.add(g[k][row])
        wires.append(z)
with (P/'formula.cnf').open() as stream:
    clauses=[list(map(int,line.split()[:-1])) for line in stream
             if not line.startswith(('c','p'))]
for c in clauses[:-128]:
    assert any(v in positive if v>0 else -v not in positive for v in c)
for row,c in enumerate(clauses[-128:]):
    expected=any(row&(1<<a) and row&(1<<b) for a,b in E)
    assert c==[M['selectors'][-1]['v'][row]*(1 if expected else -1)]
not_clauses={tuple(sorted([-M['selectors'][i]['op'][2],-M['selectors'][j]['op'][2]]))
             for i in range(11) for j in range(i+1,11)}
all_clauses={tuple(sorted(c)) for c in clauses}
assert not_clauses<=all_clauses

# F = x0*x2 OR x1*x3 OR x4*x6 OR
#     (x0 OR x1 OR x2 OR x3)*(x4 OR x5 OR x6).
gates=[('or',0,2),('or',1,3),('or',4,6),('or',7,8),('or',9,5),
       ('and',0,2),('and',1,3),('and',4,6),('and',10,11),
       ('or',12,13),('or',14,15),('or',16,17)]
errors=[]
for row in range(128):
    wires=[bool(row&(1<<i)) for i in range(7)]
    for j,(op,a,b) in enumerate(gates):
        assert a<7+j and b<7+j
        wires.append(apply(op,wires[a],wires[b]))
    expected=any(row&(1<<a) and row&(1<<b) for a,b in E)
    if wires[-1]!=expected:errors.append(row)
assert not errors
(P/'baseline12.json').write_text(json.dumps({'size':12,'output':18,
    'gates':[{'op':op,'inputs':[a,b]} for op,a,b in gates],
    'verified_rows':128,'mismatches':errors,'not_count':0},indent=2)+'\n')
result={'operator_truth_cases':relations,'internal_cnf_clauses_replayed':len(clauses)-128,
    'maximum_one_not_pair_clauses_checked':len(not_clauses),
    'target_rows_checked':128,'baseline12_rows_checked':128,'baseline12_mismatches':errors,
    'scope':'Independent Python sanity checks; no full task proof or formal synthesis certificate'}
(P/'encoding-audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
