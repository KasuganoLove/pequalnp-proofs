"""Relabel the selected five-point circuit and add the other eight stars."""
from pathlib import Path
import json,sys
P=Path(__file__).resolve().parent
name=sys.argv[1] if len(sys.argv)>1 else 'candidate-23.json'
C=json.loads((P/name).read_text());problem=json.loads((P/'problem.json').read_text())
assert C['input_count']==18
assert 0<=C['output']<18+len(C['gates']), 'A genuine nonconstant witness must have an existing output wire'
mapping=problem['raw_to_full650']
def wire(w):return mapping[w] if w<18 else w+8
gates=[[op,wire(a),wire(b)] for op,a,b in C['gates']]
out=wire(C['output'])
def emit(op,a,b):gates.append([op,a,b]);return 26+len(gates)-1
for p in problem['remaining_full650_points']:
    ns=[b for a,b in problem['full650_edges'] if a==p]
    assert len(ns)==4
    a=emit(1,ns[0],ns[1]);b=emit(1,ns[2],ns[3]);c=emit(1,a,b);star=emit(0,p,c)
    out=emit(1,out,star)
assert len(gates)==len(C['gates'])+40
base='full650-'+Path(name).stem
(P/(base+'.json')).write_text(json.dumps({'input_count':26,'gates':gates,'output':out,'source_five_point_circuit':name},indent=2)+'\n')
with (P/(base+'.txt')).open('w') as f:
    f.write(f"26 {len(gates)} {out} 52\n")
    for a,b in problem['full650_edges']:f.write(f'{a} {b}\n')
    for op,a,b in gates:f.write(f'{op} {a} {b}\n')
# Independently check all full650 minimal positives and maximal negatives.
def ev(mask):
    w=[bool(mask>>i&1) for i in range(26)]
    for op,a,b in gates:
        x=w[a] if a<len(w) else False;y=w[b] if b<len(w) else False
        w.append(True if op==2 else (x or y if op else x and y))
    return w[out] if out<len(w) else False
line_points=[[a for a,b in problem['full650_edges'] if b==13+l] for l in range(13)]
pos_errors=[(a,b) for a,b in problem['full650_edges'] if not ev((1<<a)|(1<<b))]
negatives=[];neg_errors=[]
for S in range(8192):
    points=[p for p in range(13) if S>>p&1]
    avoided=[l for l in range(13) if all(p not in line_points[l] for p in points)]
    if not all(any(p in line_points[l] for l in avoided) for p in range(13) if p not in points):continue
    mask=S+sum(1<<(13+l) for l in avoided);negatives.append(mask)
    if ev(mask):neg_errors.append(mask)
assert len(negatives)==704
record={'source':name,'full_gate_count':len(gates),'point_subsets_examined':8192,'positive_count':52,'maximal_negative_count':704,'positive_errors':pos_errors,'negative_errors':neg_errors,'all_boundary_correct':not pos_errors and not neg_errors,'fits63':len(gates)<=63,'lean_verified':False}
(P/(base+'-boundary-verification.json')).write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record))
if pos_errors or neg_errors:raise SystemExit(1)
