"""Exact symbolic extension test for the known non-star disjoint-block plane.
Uses coefficient expansion and linear equations only, no Groebner job.
"""
import sympy as s,itertools,json
x,y,z=s.symbols('x y z'); r=s.sqrt(2)
a,b,c,d,e,f,g,h,i,j=s.symbols('a b c d e f g h i j')
U=s.zeros(4);V=s.zeros(4)
for M,k in [(U,0),(V,2)]:
    M[k,k]=r-1;M[k,k+1]=M[k+1,k]=1;M[k+1,k+1]=-r-1
C=s.Matrix([[a,b,c,d],[b,e,f,g],[c,f,h,i],[d,g,i,j]])
T=s.ones(4)+x*U+y*V+z*C
per=s.expand(sum(s.prod(T[k,p[k]] for k in range(4)) for p in itertools.permutations(range(4)))-24)
P=s.Poly(per,x,y,z)
linear=[(m,s.expand(v)) for m,v in P.terms() if m[2]==1]
print('Linear z coefficients:')
for m,v in linear: print(m,s.factor(v,extension=r))
sol=s.linsolve([v for m,v in linear],(a,b,c,d,e,f,g,h,i,j))
print('linear solution',sol)
ss=dict(zip((a,b,c,d,e,f,g,h,i,j),list(sol)[0]))
print('Remaining coefficients:')
rem=[]
for m,v in P.terms():
    vv=s.factor(s.expand(v.subs(ss)),extension=r)
    if vv!=0:
        rem.append({'monomial':m,'coefficient':str(vv)})
        print(m,vv)
json.dump({'field':'Q(sqrt(2))','linear_solution':{str(k):str(v) for k,v in ss.items()},'remaining':rem,'scope':'Symbolic equations for extensions of this fixed two-dimensional plane only.'},open('ownership-block-extension.json','w'),indent=2)
