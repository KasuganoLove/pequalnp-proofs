"""Exact four-line block, sixteen-gate control, and symbolic global splice."""
from pathlib import Path
import hashlib
import json
import re

P = Path(__file__).resolve().parent
gap = json.loads((P.parent / "gap.json").read_text())
full_edges = [(int(a), int(b)) for a, b in re.findall(r"\(x (\d+) && x (\d+)\)", gap["statement"])]
lines = [21, 25, 27, 37]
bundles = [[2, 16], [7, 10, 20], [8, 9, 12], [11, 13, 19]]
local_edges = [(1,5),(1,6),(1,7),(1,8), (2,0),(2,5),(2,9),
               (3,0),(3,6),(3,10), (4,0),(4,7),(4,11)]
raw_or_bundles = [[1],[21],[25],[27],[37],[6],[3],[18],*bundles]
expanded = {tuple(sorted((a,b))) for i,j in local_edges
            for a in raw_or_bundles[i] for b in raw_or_bundles[j]}
assert expanded == {e for e in full_edges if e[1] in lines}
assert len(expanded) == 20
gates = []
def local_gate(op,a,b):
    assert a < 12 + len(gates) and b < 12 + len(gates)
    gates.append({'op':op,'inputs':[a,b]})
    return 12 + len(gates)-1
stars = []
for center, neighbors in [(1,[5,6,7,8]),(2,[0,5,9]),(3,[0,6,10]),(4,[0,7,11])]:
    signal=neighbors[0]
    for q in neighbors[1:]:signal=local_gate('or',signal,q)
    stars.append(local_gate('and',center,signal))
output=stars[0]
for star in stars[1:]:output=local_gate('or',output,star)
assert len(gates)==16 and output==27
for x in range(4096):
    w=[bool(x>>i&1) for i in range(12)]
    for g in gates:
        a,b=g['inputs'];w.append(w[a]and w[b] if g['op']=='and' else w[a]or w[b])
    assert w[output]==any((x>>a&1)and(x>>b&1) for a,b in local_edges)

def minimal(terms):
    result=[]
    for t in sorted(set(terms),key=lambda x:(x.bit_count(),x)):
        if not any((s&t)==s for s in result):result.append(t)
    return frozenset(result)
full_gates=[];symbolic=[frozenset([1<<i]) for i in range(40)]
def add(op,inputs):
    assert all(i<len(symbolic) for i in inputs)
    a,b=inputs
    result=minimal(symbolic[a]|symbolic[b]) if op=='or' else minimal(x|y for x in symbolic[a] for y in symbolic[b])
    full_gates.append({'op':op,'inputs':inputs});symbolic.append(result)
    return len(symbolic)-1
bundle_wires=[]
for group in bundles:
    signal=group[0]
    for q in group[1:]:signal=add('or',[signal,q])
    bundle_wires.append(signal)
assert len(full_gates)==7
mapping=[1,21,25,27,37,6,3,18,*bundle_wires]
for g in gates:
    mapping.append(add(g['op'],[mapping[i] for i in g['inputs']]))
group_output=mapping[output]
outputs=[group_output]
for right in range(21,40):
    if right in lines:continue
    neighbors=sorted(a for a,b in full_edges if b==right)
    signal=neighbors[0]
    for left in neighbors[1:]:signal=add('or',[signal,left])
    outputs.append(add('and',[right,signal]))
full_output=outputs[0]
for signal in outputs[1:]:full_output=add('or',[full_output,signal])
assert len(full_gates)==113 and full_output==152
assert symbolic[full_output]==frozenset((1<<a)|(1<<b) for a,b in full_edges)
problem={'task':'L-meta-9834','global_statement_sha256':hashlib.sha256(gap['statement'].encode()).hexdigest(),
         'selected_global_lines':lines,'private_point_bundles':bundles,'local_raw_interpretations':raw_or_bundles,
         'local_edges':local_edges,'local_vertices':12,'local_edge_count':13,'local_baseline_gates':16,
         'local_goal_gates':15,'local_maximum_NOT_gates_for_search':1,'preparation_OR_gates':7,
         'other_line_stars_gates':75,'final_merge_OR_gates':15,
         'global_candidate_size_if_local_goal_found':112,
         'baseline_local_all4096_verified':True,'baseline_full_symbolic95_edges_verified':True,
         'raw_global_wire_mapping_after_preparation':[1,21,25,27,37,6,3,18,*bundle_wires]}
(P/'problem.json').write_text(json.dumps(problem,indent=2)+'\n')
(P/'baseline16.json').write_text(json.dumps({'gates':gates,'output':output,'size':16},indent=2)+'\n')
(P/'baseline-splice113.json').write_text(json.dumps({'gates':full_gates,'output':full_output,'size':113,'symbolic_edge_monomials':95},indent=2)+'\n')
print(json.dumps(problem,indent=2))
