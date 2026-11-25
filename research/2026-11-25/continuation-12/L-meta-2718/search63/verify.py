"""Independent literal finite-set predicate verifier for L-meta-2718.

It loops over all8192 point subsets, computes the posted quantified conditions
directly, and evaluates every required negative input plus all52 positives.
The optimized preparer's maximality/degeneracy bitmask test is not reused.
"""
from pathlib import Path
import json,sys
P=Path(__file__).resolve().parent
name=sys.argv[1] if len(sys.argv)>1 else 'candidate-63.json'
C=json.loads((P/name).read_text());gates=C['gates'];out=C['output']
assert len(gates)==C['size']
for j,(op,a,b) in enumerate(gates):assert op in (0,1) and 0<=a<26+j and 0<=b<26+j
assert 0<=out<26+len(gates)
def ev(mask):
    w=[bool(mask>>i&1) for i in range(26)]
    for op,a,b in gates:w.append((w[a] or w[b]) if op else (w[a] and w[b]))
    return w[out]
def inc(p,l):return (p-l)%13 in (0,1,3,9)
positive_errors=[];negative_errors=[];positives=[];negatives=[]
for p in range(13):
 for l in range(13):
  if inc(p,l):
   mask=(1<<p)|(1<<(13+l));positives.append(mask)
   if not ev(mask):positive_errors.append({'point':p,'line':l,'mask':mask})
for S in range(8192):
    points=[p for p in range(13) if S>>p&1]
    avoids=[l for l in range(13) if all(not inc(p,l) for p in points)]
    maximal=all(any(inc(p,l) for l in avoids) for p in range(13) if p not in points)
    collinear=any(all(inc(p,l) for p in points) for l in range(13))
    concurrent=any(all(inc(p,l) for l in avoids) for p in range(13))
    if not maximal or not(collinear or concurrent):continue
    mask=S+sum(1<<(13+l) for l in avoids);negatives.append(mask)
    if ev(mask):negative_errors.append({'point_mask':S,'line_mask':sum(1<<l for l in avoids),'mask':mask})
assert len(positives)==52 and len(negatives)==236
problem=json.loads((P/'problem.json').read_text())
assert set(positives)==set(problem['positive_masks'])
assert set(negatives)==set(problem['negative_masks'])
def degree(side):
    w=[int((i<13)==(side==0)) for i in range(26)]
    for op,a,b in gates:w.append(max(w[a],w[b]) if op else w[a]+w[b])
    return w[out]
result={'source':name,'size':len(gates),'all_point_subsets_examined':8192,'positive_count':52,'negative_count':236,'positive_errors':len(positive_errors),'negative_errors':len(negative_errors),'first_positive_errors':positive_errors[:20],'first_negative_errors':negative_errors[:20],'point_degree':degree(0),'line_degree':degree(1),'promise_correct':not positive_errors and not negative_errors,'budget63':len(gates)<=63,'lean_verified':False}
(P/(Path(name).stem+'-verification.json')).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
