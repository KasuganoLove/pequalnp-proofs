from pathlib import Path
import json,hashlib
P=Path(__file__).resolve().parent
N=26;D=[0,1,3,9];U=(1<<13)-1
lines=[sum(1<<((l+d)%13) for d in D) for l in range(13)]
pencils=[sum(1<<l for l in range(13) if lines[l]>>p&1) for p in range(13)]
edges=[(p,13+l) for p in range(13) for l in range(13) if lines[l]>>p&1]
positive=[(1<<p)|(1<<l) for p,l in edges]
negative=[];types={}
for s in range(8192):
    t=sum(1<<l for l in range(13) if not(lines[l]&s))
    cover=0
    for l in range(13):
        if t>>l&1:cover|=lines[l]
    if cover!=(U^s):continue
    deg=any(not(s&~line) for line in lines) or any(not(t&~pen) for pen in pencils)
    if not deg:continue
    negative.append(s|(t<<13))
    key=f'{s.bit_count()}+{t.bit_count()}'
    types[key]=types.get(key,0)+1
assert len(positive)==52 and len(negative)==236
rows=positive+negative
(P/'rows.txt').write_text(f'{len(rows)} {len(positive)}\n'+'\n'.join(map(str,rows))+'\n')
problem={'raw_inputs':26,'suffix_gates':63,'difference_set':D,'edges':edges,'positive_masks':positive,'negative_masks':negative,'negative_types':types,'training_rows':288,'scope':'exact52incident positives and236degenerate maximal negatives; not all704maximal negatives'}
(P/'problem.json').write_text(json.dumps(problem,indent=2)+'\n')
def star_circuit(side,rotation,variant):
    gates=[]
    def gate(op,a,b):
        gates.append((op,min(a,b),max(a,b)));return N+len(gates)-1
    def fold_or(w,balanced):
        w=list(w)
        if balanced:
            while len(w)>1:
                w=[gate(1,w[i],w[i+1]) if i+1<len(w) else w[i] for i in range(0,len(w),2)]
            return w[0]
        out=w[0]
        for x in w[1:]:out=gate(1,out,x)
        return out
    stars=[]
    for k in range(13):
        v=(k+rotation)%13
        center=v if side==0 else 13+v
        neighbors=[13+l for l in range(13) if lines[l]>>v&1] if side==0 else [p for p in range(13) if lines[v]>>p&1]
        sh=(variant+k)%4;neighbors=neighbors[sh:]+neighbors[:sh]
        if variant==2:neighbors=[neighbors[i] for i in (0,2,1,3)]
        if variant==3:neighbors.reverse()
        stars.append(gate(0,center,fold_or(neighbors,variant%2==0)))
    out=fold_or(stars,variant%2==0)
    assert len(gates)==64
    return gates,out
def erase(gates,out,j,which):
    old=N+j;replacement=gates[j][1+which]
    def remap(w):return replacement if w==old else w-1 if w>old else w
    gs=[(op,remap(a),remap(b)) for k,(op,a,b) in enumerate(gates) if k!=j]
    return tuple(gs),remap(out)
base,bo=star_circuit(0,0,0)
(P/'known-64.json').write_text(json.dumps({'size':64,'output':bo,'gates':base},indent=2)+'\n')
seeds=[];seen=set()
for side in range(2):
 for rot in range(13):
  for variant in range(4):
   gs,o=star_circuit(side,rot,variant)
   for j in range(64):
    for which in range(2):
     e=erase(gs,o,j,which)
     if e not in seen:seen.add(e);seeds.append(e)
with (P/'seeds.txt').open('w') as f:
    f.write(f'{len(seeds)}\n')
    for gs,o in seeds:
        f.write(str(o)+'\n')
        for op,a,b in gs:f.write(f'{op} {a} {b}\n')
print(json.dumps({'rows':len(rows),'positive':52,'negative':236,'seeds':len(seeds),'baseline_size':64}))
