#!/usr/bin/env python3
"""Exact64-row structural and thirteen-gate control audit; no search."""
import pathlib,json,itertools,hashlib
b=pathlib.Path(__file__).resolve().parent;T=4276676736*(1<<32)+4269860864
U=[0,1,2,4];weights=[2,2,2,3,2,1]
gates=[('or',[0,1]),('and',[0,1]),('or',[2,4]),('and',[2,4]),('or',[7,9]),('and',[6,8]),('and',[7,9]),('and',[10,11]),('or',[10,11]),('and',[3,14]),('and',[5,13]),('or',[12,15]),('or',[17,16])];out=18
errors=[];structure_errors=[]
for r in range(64):
 x=[bool(r>>i&1) for i in range(6)];want=bool(T>>r&1);count=sum(x[i] for i in U);expanded=(x[3] and count>=2) or (x[5] and count>=3) or count==4;weighted=sum(w*x[i] for i,w in enumerate(weights))>=7
 if want!=expanded or want!=weighted:structure_errors.append(r)
 v=x[:]
 for op,ins in gates:
  assert all(i<len(v) for i in ins)
  z=[v[i] for i in ins];v.append(all(z) if op=='and' else any(z))
 if v[out]!=want:errors.append(r)
sym_errors=[]
for p in itertools.permutations(U):
 for r in range(64):
  rr=r
  for i,j in zip(U,p):rr=(rr&~(1<<i))|(((r>>j)&1)<<i)
  if ((T>>rr)&1)!=((T>>r)&1):sym_errors.append([list(p),r])
assert not errors and not structure_errors and not sym_errors
result={'table':T,'all_rows':64,'monotone':all(not(T>>r&1) or(T>>(r|(1<<i))&1) for r in range(64) for i in range(6)),'four_symmetric_inputs':U,'permutations_tested':24,'weighted_threshold':{'weights':weights,'threshold':7},'formula':'x3*T2(U) OR x5*T3(U) OR T4(U)','baseline':{'gates':gates,'output':out,'size':len(gates),'errors':errors},'structure_errors':structure_errors,'symmetry_errors':sym_errors,'scope':'Ordinary scalar verification only. Thirteen gates exceed the desired eleven and do not complete L-meta-12128.'};(b/'baseline-13.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'size':len(gates),'rows':64,'errors':len(errors),'symmetry_errors':len(sym_errors),'structure_errors':len(structure_errors),'all_pass':True}))
