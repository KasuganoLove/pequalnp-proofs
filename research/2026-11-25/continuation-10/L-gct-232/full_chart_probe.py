from pathlib import Path
import itertools,json,signal,sys,time
import sympy as s

def alarm(*_): raise TimeoutError('30-second exact diagnostic limit')
signal.signal(signal.SIGALRM,alarm)
start=time.time();pivots=tuple(map(int,sys.argv[1:4]));signal.alarm(30)
out=Path(__file__).with_name('full-chart-'+'-'.join(map(str,pivots))+'.json')
result={'pivots':pivots,'scope':'one RREF stratum for a possible three-plane; diagnostic only, no Lean certificate'}
try:
 x,y,z=s.symbols('x y z');R=s.zeros(3,9);params=[]
 for i,p in enumerate(pivots):
  R[i,p]=1
  for j in range(p+1,9):
   if j not in pivots:
    q=s.Symbol(f'a{i}_{j}');R[i,j]=q;params.append(q)
 vec=list((s.Matrix([[x,y,z]])*R).row(0))
 # Coordinates are T01,T02,T03,T11,T12,T13,T22,T23,T33.
 b,c,d,e,f,g,h,i,j=vec
 a=-2*(b+c+d+f+g+i)-e-h-j
 T=s.Matrix([[a,b,c,d],[b,e,f,g],[c,f,h,i],[d,g,i,j]])
 gens=(x,y,z,*params);M=s.ones(4)+T
 P=s.Poly(-24,*gens,domain=s.QQ)
 for perm in itertools.permutations(range(4)):
  prod=s.Poly(1,*gens,domain=s.QQ)
  for k in range(4):prod*=s.Poly(M[k,perm[k]],*gens,domain=s.QQ)
  P+=prod
 by_xyz={}
 for powers,coef in P.rep.to_dict().items():by_xyz.setdefault(powers[:3],{})[powers[3:]]=coef
 polys=[s.Poly.from_dict(coefs,params,domain=s.QQ) for coefs in by_xyz.values()] if params else []
 result.update(parameters=len(params),constraints=len(polys),total_terms=sum(len(q.terms()) for q in polys),coefficient_seconds=time.time()-start)
 print(result,flush=True)
 if any(q.total_degree()==0 and q!=0 for q in polys):result['status']='inconsistent constant coefficient'
 else:
  gb=s.groebner(polys,*params,order='grevlex',method='f5b',domain=s.QQ)
  result['groebner']=[str(q.as_expr() if isinstance(q,s.Poly) else q) for q in gb]
  result['status']='inconsistent' if len(gb)==1 and gb[0].as_expr()==1 else 'unresolved nontrivial basis'
except TimeoutError as exc:
 result['status']='timeout';result['message']=str(exc)
except Exception as exc:
 result['status']='error';result['message']=repr(exc)
result['seconds']=time.time()-start
out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result),flush=True)
