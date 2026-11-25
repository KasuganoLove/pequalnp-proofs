"""Independently decode and check a CaDiCaL SAT model, then assemble Heawood.

No UNSAT inference is made here. The 14-slot suffix receives physical values
for raw input columns0..9 and OR(raw4,raw5) at column10.
"""
from pathlib import Path
import hashlib,json,sys
p=Path(__file__).resolve().parent
problem=json.loads((p/'problem.json').read_text())
log=(p/'cadical.log').read_text()
if 's SATISFIABLE' not in log:
    print('No SAT model; no witness verification performed.')
    raise SystemExit(2)
assignment={abs(int(t)):int(t)>0 for line in log.splitlines() if line.startswith('v ') for t in line.split()[1:] if t!='0'}
# Check the supplied assignment directly against every exported clause.
clause_count=0
for line in (p/'subdivision-k4-free-or-14.cnf').read_text().splitlines():
    if not line or line[0] in 'cp':continue
    literals=[int(t) for t in line.split() if t!='0']
    assert any(assignment.get(abs(t),False)==(t>0) for t in literals),('unsatisfied clause',clause_count)
    clause_count+=1
n=11;s=14;wd=2**n+n+s+1
def ix(kind,gate,slot):return (kind*(s+1)+gate)*wd+slot+1
def selected(kind,gate,choices):
    values=[k for k in choices if assignment.get(ix(kind,gate,k),False)]
    assert values,(kind,gate)
    return values[0]
gates=[]
for j in range(s):
    op=selected(0,j,range(3))
    a=selected(1,j,range(n+j+1));b=selected(2,j,range(n+j+1))
    gates.append({'op':['and','or','true'][op],'inputs':[] if op==2 else [a,b]})
out=selected(6,0,range(n+s+1))
def evaluate(gates,out,values):
    w=list(values)
    for g in gates:
        bits=[w[i] if i<len(w) else False for i in g['inputs']]
        w.append(all(bits) if g['op'] in ('and','true') else any(bits))
    return w[out] if out<len(w) else False
def graph_value(mask,edges):return any((mask>>a&1) and (mask>>b&1) for a,b in edges)
errors=[]
for mask in range(1024):
    raw=[bool(mask>>i&1) for i in range(10)]
    value=evaluate(gates,out,raw+[raw[4] or raw[5]])
    if value!=bool(graph_value(mask,problem['edges'])):errors.append(mask)
assert not errors,('subdivision-K4 errors',errors[:20])
# One charged prefix gate exposes OR(Heawood13,Heawood7). The remaining
# original labels map a,b,e,f,c,d,p,q,r,s -> 0,3,2,4,13,7,8,10,12,11.
mapping=[0,3,2,4,13,7,8,10,12,11]
def wire(k):
    if k<10:return mapping[k]
    if k==10:return 14
    return k+4
H=[{'op':'or','inputs':[13,7]}]
for g in gates:H.append({'op':g['op'],'inputs':[wire(i) for i in g['inputs']]})
sub_output=wire(out)
def emit(op,*inputs):
    H.append({'op':op,'inputs':list(inputs)})
    return 14+len(H)-1
neighbors=emit('or',14,9)
fifth=emit('and',1,neighbors)
five=emit('or',sub_output,fifth)
left=emit('or',9,10);left=emit('or',left,12);left=emit('and',5,left)
right=emit('or',8,9);right=emit('or',right,11);right=emit('and',6,right)
final=emit('or',five,left);final=emit('or',final,right)
heawood_edges=[(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]
assert len(H)==26
errors=[]
for mask in range(16384):
    val=evaluate(H,final,[bool(mask>>i&1) for i in range(14)])
    if val!=bool(graph_value(mask,heawood_edges)):errors.append(mask)
assert not errors,('Heawood errors',errors[:20])
(p/'subdivision-k4-witness.json').write_text(json.dumps({'gates':gates,'output':out,'input_count':11,'free_or':[4,5]},indent=2)+'\n')
(p/'heawood-26-witness.json').write_text(json.dumps({'gates':H,'output':final,'input_count':14},indent=2)+'\n')
result={'cnf_clauses_checked':clause_count,'cnf_sha256':hashlib.sha256((p/'subdivision-k4-free-or-14.cnf').read_bytes()).hexdigest(),'subdivision_k4_all_inputs':1024,'heawood_all_inputs':16384,'heawood_gate_count':len(H),'all_correct':True,'lean_checked':False,'first_two_gate_orbit_normalization_checked':False}
(p/'sat-witness-verification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
