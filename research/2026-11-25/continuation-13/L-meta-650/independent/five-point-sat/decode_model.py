"""Check all dense clauses and decode any SAT model back to original enc2 IDs."""
from pathlib import Path
import json
P=Path(__file__).resolve().parent
log=(P/'cadical.log').read_text()
if 's SATISFIABLE' not in log:raise SystemExit('No SAT model; no candidate decoded.')
a={abs(int(t)):int(t)>0 for line in log.splitlines() if line.startswith('v ') for t in line.split()[1:] if t!='0'}
count=0
for line in (P/'five-point-23-dense.cnf').read_text().splitlines():
    if not line or line[0] in 'pc':continue
    clause=[int(t) for t in line.split() if t!='0']
    assert any(a.get(abs(v),False)==(v>0) for v in clause),count
    count+=1
inv=json.loads((P/'dense-to-sparse.json').read_text())
original={old:a.get(new,False) for new,old in enumerate(inv) if new}
n=18;s=23;wd=2**n+n+s+1
def ix(kind,j,k):return (kind*(s+1)+j)*wd+k+1
def choose(kind,j,ks):
    found=[k for k in ks if original.get(ix(kind,j,k),False)]
    assert found,(kind,j)
    return found[0]
gates=[[choose(0,j,range(3)),choose(1,j,range(n+j+1)),choose(2,j,range(n+j+1))] for j in range(s)]
out=choose(6,0,range(n+s+1))
(P/'candidate-23.json').write_text(json.dumps({'input_count':18,'gates':gates,'output':out},indent=2)+'\n')
record={'clauses_checked':count,'dense_assignment_satisfies_every_clause':True,'decoded_gates':len(gates),'decoded_output':out,'truth_table_verified':False}
(P/'model-decoding.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record))
