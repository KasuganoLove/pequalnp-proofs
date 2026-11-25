from pathlib import Path
import sympy as s
from itertools import permutations
import json,time
start=time.time()
x,y,z=s.symbols('x y z')
w=s.symbols('a b c d e f g h i j')
C=s.zeros(4)
for var,(i,j) in zip(w,[(i,j) for i in range(4) for j in range(i,4)]):
 C[i,j]=C[j,i]=var
r=s.sqrt(2)
U=s.zeros(4);V=s.zeros(4)
U[0,0]=V[2,2]=r-1;U[1,1]=V[3,3]=-r-1
U[0,1]=U[1,0]=V[2,3]=V[3,2]=1
M=s.ones(4)+x*U+y*V+z*C
p=s.Poly(s.expand(sum(s.prod(M[i,k[i]] for i in range(4)) for k in permutations(range(4)))-24),x,y,z)
linear=[s.expand(c) for powers,c in p.terms() if powers[2]==1]
print('linear constraints',len(linear),flush=True)
sol=next(iter(s.linsolve(linear,w)))
sol=[s.simplify(e) for e in sol]
print('linear solution',list(zip(w,sol)),flush=True)
q=s.Poly(s.expand(p.as_expr().subs(dict(zip(w,sol)),simultaneous=True)),x,y,z)
constraints=list(dict.fromkeys(s.factor(c,extension=r) for powers,c in q.terms() if powers[2]>=2 and c!=0))
print('remaining constraints',constraints,flush=True)
params=sorted(set().union(*(c.free_symbols for c in sol)),key=str)
print('params',params,flush=True)
if constraints:
 gb=s.groebner(constraints,*params,extension=r)
 print('groebner',list(gb),flush=True)
else:gb=[]
result={'linear_solution':{str(a):str(b) for a,b in zip(w,sol)},'constraints':[str(c) for c in constraints],'parameters':[str(v) for v in params],'groebner':[str(v) for v in gb],'seconds':time.time()-start,'scope':'extension of one fixed nonstar two-dimensional block plane only; not arbitrary L'}
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
print('seconds',time.time()-start,flush=True)
