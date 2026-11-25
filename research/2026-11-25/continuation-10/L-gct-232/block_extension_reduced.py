from pathlib import Path
import sympy as s
from itertools import permutations
import json,time,signal

def expired(*_):
 raise TimeoutError('Bounded exact calculation reached 120 seconds')
signal.signal(signal.SIGALRM,expired);signal.alarm(120)
start=time.time();r=s.sqrt(2);K=s.QQ.algebraic_field(r)
x,y,z,d,g,h,i=s.symbols('x y z d g h i')
params=(d,g,h,i);gens=(x,y,z,*params)
a=-2*r*d-2*g*(4-3*r)-h*(1-r)/2-i
b=-d*(2-r)+g*(2-3*r)+h/4-i*(1+r)/2
c=d-h*(r+2)/8+r*i/4
f=g-h*(r+2)/8+r*i/4
C=s.Matrix([[a,b,c,d],[b,0,f,g],[c,f,h,i],[d,g,i,0]])
U=s.zeros(4);V=s.zeros(4)
U[0,0]=V[2,2]=r-1;U[1,1]=V[3,3]=-r-1
U[0,1]=U[1,0]=V[2,3]=V[3,2]=1
M=s.ones(4)+x*U+y*V+z*C
P=s.Poly(-24,*gens,domain=K)
for perm in permutations(range(4)):
 prod=s.Poly(1,*gens,domain=K)
 for k in range(4):prod*=s.Poly(M[k,perm[k]],*gens,domain=K)
 P+=prod
by_xyz={}
for powers,coef in P.rep.to_dict().items():
 by_xyz.setdefault(powers[:3],{})[powers[3:]]=coef
constraints=[s.Poly.from_dict(coefs,params,domain=K) for coefs in by_xyz.values()]
print('constraints',len(constraints),'terms',sum(len(q.terms()) for q in constraints),'elapsed',time.time()-start,flush=True)
assert all(p[2]>=2 for p in by_xyz)
result={'parameters':[str(v) for v in params], 'linear_gauge':'Subtract multiples of U,V to set C11=C33=0; remaining linear equations solved exactly.', 'matrix':[[str(e) for e in C.row(k)] for k in range(4)],'constraints':{str(p):str(s.Poly.from_dict(coefs,params,domain=K).as_expr()) for p,coefs in by_xyz.items()},'charts':[],'scope':'one fixed nonstar two-dimensional block plane only; no arbitrary-space classification'}
for v in params:
 expr=[q.as_expr().subs(v,1) for q in constraints]
 others=[w for w in params if w!=v]
 gb=s.groebner(expr,*others,order='grevlex',domain=K)
 row={'set_parameter_to_one':str(v),'groebner':[str(q) for q in gb], 'inconsistent':list(gb)==[s.Integer(1)]}
 result['charts'].append(row);print(row,'elapsed',time.time()-start,flush=True)
result['seconds']=time.time()-start
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
print('COMPLETE',flush=True)
