"""Bijective variable renaming, with a full independent inverse clause check."""
from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent
source=P/'representation-10-sparse.cnf';target=P/'representation-10-dense.cnf'
ids=set();count=0;declared=None
with source.open() as f:
    for line in f:
        if line.startswith('p '):declared=tuple(map(int,line.split()[2:]));continue
        if not line.strip() or line.startswith('c'):continue
        lits=list(map(int,line.split()));assert lits[-1]==0 and all(lits[:-1])
        ids.update(abs(v) for v in lits[:-1]);count+=1
assert declared and count==declared[1]
ordered=sorted(ids);mapping={old:new for new,old in enumerate(ordered,1)}
with source.open() as f,target.open('w') as g:
    g.write(f'p cnf {len(ordered)} {count}\n')
    for line in f:
        if not line.strip() or line[0] in 'pc':continue
        lits=list(map(int,line.split()))[:-1]
        g.write(' '.join(str(mapping[abs(v)] if v>0 else -mapping[abs(v)]) for v in lits)+' 0\n')
inverse=[0]+ordered
with source.open() as f,target.open() as g:
    f.readline();g.readline()
    for original,renamed in zip(f,g,strict=True):
        a=list(map(int,original.split()));b=list(map(int,renamed.split()))
        assert a==[0 if v==0 else (inverse[abs(v)] if v>0 else -inverse[abs(v)]) for v in b]
(P/'dense-to-sparse.json').write_text(json.dumps(inverse)+'\n')
record={'sparse_maximum_variable':declared[0],'dense_variables':len(ordered),'clauses':count,'bijection_inverse_checked':True,'clause_order_preserved':True,'sparse_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'dense_sha256':hashlib.sha256(target.read_bytes()).hexdigest()}
(P/'encoding.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record))
