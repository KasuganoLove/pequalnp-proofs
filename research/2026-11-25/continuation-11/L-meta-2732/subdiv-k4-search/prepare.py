from pathlib import Path
import hashlib
import json
import random

HERE=Path(__file__).resolve().parent
source=HERE.parent/'five-star-free-or/problem.json'
problem=json.loads(source.read_text())
edges=[tuple(e) for e in problem['edges']]
assert len(edges)==12 and problem['free_or']==[4,5]
negative={m for m in range(1024) if not any((m>>u&1) and (m>>v&1) for u,v in edges)}
maxfalse=sorted(m for m in negative if all((m|(1<<v)) not in negative
                                         for v in range(10) if not(m>>v&1)))
assert maxfalse==problem['maximal_false_masks']
positive=[(1<<u)|(1<<v) for u,v in edges]
physical=[m|(((m>>4&1) or (m>>5&1))<<10) for m in positive+maxfalse]
assert physical==problem['physical_rows']
(HERE/'rows.txt').write_text(f'{len(physical)} {len(positive)}\n'+' '.join(map(str,physical))+'\n')
rng=random.Random(273220261125)

def star(centers):
    centers=list(centers);rng.shuffle(centers)
    gates=[];terms=[]
    def add(op,a,b):
        gates.append([op,min(a,b),max(a,b)])
        return 10+len(gates)
    for v in centers:
        neighbors=[a if b==v else b for a,b in edges if a==v or b==v]
        rng.shuffle(neighbors);w=neighbors[0]
        for u in neighbors[1:]:w=add(1,w,u)
        terms.append(add(0,v,w))
    while len(terms)>1:
        a=terms.pop(rng.randrange(len(terms)));b=terms.pop(rng.randrange(len(terms)))
        terms.append(add(1,a,b))
    return {'size':len(gates),'output':terms[0],'gates':gates,'raw_inputs':10,'free_or':[4,5]}

def erase(seed,k,operand):
    old=seed['gates'];deleted=11+k;replacement=old[k][operand]
    def wire(v):
        if v==deleted:v=replacement
        return v-1 if v>deleted else v
    gates=[[op,wire(a),wire(b)] for j,(op,a,b) in enumerate(old) if j!=k]
    assert all(0<=a<11+j and 0<=b<11+j for j,(_,a,b) in enumerate(gates))
    return {'size':len(gates),'output':wire(seed['output']),'gates':gates,'raw_inputs':10,'free_or':[4,5]}

seeds=[]
for trial in range(128):
    base=star(range(4));assert base['size']==15
    if trial==0:(HERE/'known-star-suffix15.json').write_text(json.dumps(base,indent=2)+'\n')
    for k in range(15):
        for operand in [1,2]:seeds.append(erase(base,k,operand))
for trial in range(512):
    seed=star(range(4,10));assert seed['size']==17
    for _ in range(3):seed=erase(seed,rng.randrange(seed['size']),rng.choice([1,2]))
    assert seed['size']==14;seeds.append(seed)
with (HERE/'seeds.txt').open('w') as f:
    f.write(str(len(seeds))+'\n')
    for seed in seeds:
        f.write(str(seed['output'])+'\n')
        for gate in seed['gates']:f.write(' '.join(map(str,gate))+'\n')
problem.update({'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
                'heawood_map':[0,3,2,4,13,7,8,10,12,11],
                'extra_center':1,'pendant_line':9,'remaining_centers':[5,6],
                'seeds':len(seeds),'rng_seed':273220261125})
(HERE/'problem.json').write_text(json.dumps(problem,indent=2)+'\n')
print(json.dumps({'training_rows':len(physical),'positive':len(positive),'maximal_false':len(maxfalse),'seeds':len(seeds)}))
