#!/usr/bin/env python3
"""Independently decode a Monotone2 selector model and replay all64 scalar rows."""
import pathlib,json,hashlib,datetime
b=pathlib.Path(__file__).resolve().parent;meta=json.loads((b/'encoding.json').read_text());n,s,T=meta['n'],meta['gate_slots'],meta['table'];A=(1<<n)+n+s+1
text=(b/'solver.log').read_text();assert 's SATISFIABLE' in text,'No SAT model to decode'
pos=set();neg=set()
for line in text.splitlines():
 if line.startswith('v '):
  for tok in line.split()[1:]:
   q=int(tok)
   if q>0:pos.add(q)
   elif q<0:neg.add(-q)
assert not(pos&neg)
# Verify the model against every original CNF clause before decoding.
clauses=[];cur=[]
for line in (b/'formula.cnf').read_text().splitlines():
 if not line or line[0] in 'cp':continue
 for z in map(int,line.split()):
  if not z:clauses.append(cur);cur=[]
  else:cur.append(z)
assert not cur
badclauses=[i+1 for i,c in enumerate(clauses) if not any((z in pos) if z>0 else (-z not in pos) for z in c)];assert not badclauses
V=lambda kd,j,a:((kd*(s+1)+j)*A+a+1) in pos
gates=[]
for j in range(s):
 ops=[o for o in range(3) if V(0,j,o)];aa=[k for k in range(n+j+1) if V(1,j,k)];bb=[k for k in range(n+j+1) if V(2,j,k)];assert ops and aa and bb
 op=ops[0];gates.append({'op':'and' if op in [0,2] else 'or','inputs':[] if op==2 else [aa[0],bb[0]]})
outs=[k for k in range(n+s+1) if V(6,0,k)];assert outs;output=outs[0]
def evaluate(gs,o,r):
 w=[bool(r>>i&1) for i in range(n)]
 for g in gs:
  vs=[w[k] if k<len(w) else False for k in g['inputs']];w.append(all(vs) if g['op']=='and' else any(vs))
 return w[o] if o<len(w) else False
errors=[r for r in range(1<<n) if evaluate(gates,output,r)!=bool(T>>r&1)];assert not errors
# Delete only syntactically unreachable gates; preserve raw-input indices and all retained semantics.
needed=set()
def visit(w):
 if w<n or w>=n+len(gates) or w-n in needed:return
 j=w-n;needed.add(j)
 for z in gates[j]['inputs']:visit(z)
visit(output);order=sorted(needed);mapping={n+j:n+i for i,j in enumerate(order)}
compact=[{'op':gates[j]['op'],'inputs':[mapping.get(z,z) for z in gates[j]['inputs']]} for j in order];co=mapping.get(output,output)
ce=[r for r in range(1<<n) if evaluate(compact,co,r)!=bool(T>>r&1)];assert not ce
result={'task':'L-meta-12128','timestamp':datetime.datetime.now(datetime.timezone.utc).isoformat(),'table':T,'n':n,'cnf_clauses_verified':len(clauses),'model_sha256':hashlib.sha256((b/'solver.log').read_bytes()).hexdigest(),'raw_gates':gates,'raw_output':output,'gates':compact,'output':co,'size':len(compact),'all_rows_tested':1<<n,'errors':ce,'basis_ok':all(g['op'] in ['and','or'] and len(g['inputs'])<=2 for g in compact),'reads_back':all(z<n+i for i,g in enumerate(compact) for z in g['inputs']),'scope':'Ordinary CNF model verification and independent scalar replay only; no Lean proof.'};assert result['basis_ok'] and result['reads_back'];(b/'witness.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
