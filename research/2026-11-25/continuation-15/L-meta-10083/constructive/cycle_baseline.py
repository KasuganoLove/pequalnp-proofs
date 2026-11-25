#!/usr/bin/env python3
"""Build/check the exact cycle-family oneEach representation; no search."""
from pathlib import Path
import json,sys
k=int(sys.argv[1]) if len(sys.argv)>1 else 15
assert k>=3
n=3*k;gs=[]
def gate(op,a,b):
 w=2*n+len(gs);gs.append([op,a,b]);return w
z=[gate('or',j,n+j) for j in range(n)]
terms=[]
for i in range(k):
 p=gate('or',z[i],z[k+i]);q=gate('or',z[(i+1)%k],z[2*k+i]);terms.append(gate('and',p,q))
out=terms[0]
for t in terms[1:]:out=gate('or',out,t)
def target(a,b):
 return any(((a==i or a==k+i) and (b==(i+1)%k or b==2*k+i)) or ((b==i or b==k+i) and (a==(i+1)%k or a==2*k+i)) for i in range(k))
errors=[]
for a in range(n):
 for b in range(n):
  w=[j==a for j in range(n)]+[j==b for j in range(n)]
  for op,u,v in gs:w.append((w[u] or w[v]) if op=='or' else (w[u] and w[v]))
  if w[out]!=target(a,b):errors.append([a,b,w[out],target(a,b)])
assert not errors and len(gs)==7*k-1
p=Path(__file__).resolve().parent
(p/f'baseline-k{k}.json').write_text(json.dumps({'k':k,'n':n,'size':len(gs),'output':out,'gate_wire_base':2*n,'gates':gs,'verified_oneEach_rows':n*n,'mismatches':errors,'scope':'Only required oneEach domain; this is a7k-1 upper bound, not the target7k-2.'},indent=2)+'\n')
print(json.dumps({'k':k,'size':len(gs),'output':out,'verified_pairs':n*n,'mismatches':errors}))
