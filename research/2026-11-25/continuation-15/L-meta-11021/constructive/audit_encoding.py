#!/usr/bin/env python3
"""Independent checks of the CNF gate relations and a concrete 16-gate bound.

This does not prove synthesis completeness or certify an UNSAT result.
"""
from pathlib import Path
import json

P=Path(__file__).resolve().parent
M=json.loads((P/'encoding.json').read_text())
E=[(0,4),(0,5),(1,5),(2,6),(3,6),(0,7),(2,7),(4,7),
   (1,8),(3,8),(4,8),(6,8)]

def f(op,a,b=False):
    if op=='and': return a and b
    if op=='or': return a or b
    if op=='not': return not a
    return op=='true'

# With the operation selector set true, check the corresponding clauses for
# all eight assignments (a,b,z), both accepted and rejected values of z.
relation_cases=0
for op in M['ops']:
    for a in [False,True]:
        for b in [False,True]:
            for z in [False,True]:
                clauses = {
                    'and':[not z or a,not z or b,z or not a or not b],
                    'or':[z or not a,z or not b,not z or a or b],
                    'not':[not z or not a,z or a],
                    'false':[not z], 'true':[z]}[op]
                assert all(clauses)==(z==f(op,a,b))
                relation_cases+=1

# A deterministic arbitrary circuit uses every operator. Construct values from
# direct gate replay, then check every internal clause of the generated file.
chosen=[]; true_vars=set()
for j,g in enumerate(M['selectors']):
    op=j%5; a=(j*3)%(9+j); b=a+(j%(9+j-a))
    chosen.append((M['ops'][op],a,b))
    true_vars.update([g['op'][op],g['a'][a],g['b'][b]])
for row in range(512):
    wires=[bool(row&(1<<i)) for i in range(9)]
    for g,(op,a,b) in zip(M['selectors'],chosen):
        av,bv=wires[a],wires[b]; z=f(op,av,bv)
        for key,val in [('av',av),('bv',bv),('v',z)]:
            if val: true_vars.add(g[key][row])
        wires.append(z)
with (P/'formula.cnf').open() as stream:
    clauses=[list(map(int,line.split()[:-1])) for line in stream
             if not line.startswith(('p','c'))]
for c in clauses[:-512]:
    assert any(v in true_vars if v>0 else -v not in true_vars for v in c)
for row,c in enumerate(clauses[-512:]):
    expected=any(row&(1<<a) and row&(1<<b) for a,b in E)
    assert c==[M['selectors'][-1]['v'][row]*(1 if expected else -1)]

gates=[('or',0,1),('and',5,9),('or',2,3),('or',11,8),('and',6,12),
       ('or',0,2),('or',14,4),('and',7,15),('or',1,3),('or',17,4),
       ('and',8,18),('and',0,4),('or',10,13),('or',16,19),
       ('or',21,22),('or',23,20)]
bad=[]
for row in range(512):
    wires=[bool(row&(1<<i)) for i in range(9)]
    for op,a,b in gates: wires.append(f(op,wires[a],wires[b]))
    expected=any(row&(1<<a) and row&(1<<b) for a,b in E)
    if wires[-1]!=expected: bad.append(row)
assert not bad
(P/'baseline16.json').write_text(json.dumps({'size':16,'output':24,
    'gates':[{'op':op,'inputs':[a,b]} for op,a,b in gates],
    'verified_rows':512,'mismatches':bad},indent=2)+'\n')
report={'gate_relation_cases':relation_cases,
        'internal_cnf_clauses_replayed':len(clauses)-512,
        'output_constraint_rows_checked':512,'baseline16_rows_checked':512,
        'baseline16_mismatches':bad,
        'scope':'Local generator sanity checks only; no formal completeness or UNSAT certificate'}
(P/'encoding-audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report))
