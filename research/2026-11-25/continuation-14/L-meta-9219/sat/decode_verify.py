"""Check the SAT assignment, decode a circuit, and verify every exact oneEach row."""
from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent
log=(P/'cadical.log').read_text()
if 's SATISFIABLE' not in log:raise SystemExit('No SAT model; no witness decoded.')
a={abs(int(t)):int(t)>0 for line in log.splitlines() if line.startswith('v ') for t in line.split()[1:] if t!='0'}
count=0
with (P/'representation-10-dense.cnf').open() as f:
    for line in f:
        if not line.strip() or line[0] in 'pc':continue
        clause=[int(t) for t in line.split() if t!='0']
        assert all(abs(v) in a for v in clause),('missing_variable',count)
        assert any(a[abs(v)]==(v>0) for v in clause),('false_clause',count)
        count+=1
inv=json.loads((P/'dense-to-sparse.json').read_text())
original={old:a.get(new,False) for new,old in enumerate(inv) if new}
n=10;s=10;wd=2**n+n+s+1
def ix(kind,j,k):return (kind*(s+1)+j)*wd+k+1
def choose(kind,j,ks):
    found=[k for k in ks if original.get(ix(kind,j,k),False)]
    assert found,(kind,j)
    return found[0]
gates=[[choose(0,j,range(3)),choose(1,j,range(n+j+1)),choose(2,j,range(n+j+1))] for j in range(s)]
out=choose(6,0,range(n+s+1))
C={'input_count':10,'gates':gates,'output':out,'operation_codes':{'0':'AND','1':'OR','2':'constant TRUE (empty AND)'},'scope':'Representation on exactly one true input in each half of five; not a full graph-function witness'}
checks=[]
for u in range(5):
    for v in range(5):
        w=[i==u for i in range(5)]+[j==v for j in range(5)]
        for j,(op,left,right) in enumerate(gates):
            assert op in (0,1,2) and 0<=left<=n+j and 0<=right<=n+j
            l=w[left] if left<len(w) else False;r=w[right] if right<len(w) else False
            w.append(True if op==2 else (l or r if op else l and r))
        actual=w[out] if out<len(w) else False
        expected=bool((7586366>>(5*u+v))&1)
        checks.append({'left':u,'right':v,'actual':actual,'expected':expected})
        assert actual==expected,(u,v,actual,expected)
(P/'candidate-10.json').write_text(json.dumps(C,indent=2)+'\n')
record={'checked_cnf_clauses':count,'cnf_assignment_satisfies_every_clause':True,'oneEach_inputs_checked':25,'all_correct':True,'gate_count':len(gates),'within_budget10':len(gates)<=10,'circuit_sha256':hashlib.sha256((P/'candidate-10.json').read_bytes()).hexdigest(),'lean_verified':False,'checks':checks}
(P/'verification.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'gate_count':len(gates),'gates':gates,'output':out,'all_25_correct':True,'sha256':record['circuit_sha256']}))
