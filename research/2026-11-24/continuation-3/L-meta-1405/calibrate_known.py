import itertools
import json
from pathlib import Path

root=Path(__file__).parent
source=(root/'path4_synthesize_sym.py').read_text().replace('depth = 5','depth = 6')
namespace={'__file__':str(root/'path4_synthesize_sym.py')}
exec(source[:source.index("print(json.dumps({'variables'")],namespace)
pool,cnf,samples=namespace['pool'],namespace['cnf'],namespace['samples']

def AND(a,b): return ('and',a,b)
def OR(a,b): return ('or',a,b)
def MAJ(i): return OR(AND(i,i+4),AND(i+8,OR(i,i+4)))
formula=OR(AND(MAJ(1),OR(MAJ(0),MAJ(2))),AND(MAJ(2),MAJ(3)))
def height(t): return 0 if isinstance(t,int) else 1+max(height(t[1]),height(t[2]))
assert height(formula)==6
def pad(t,h):
    if h==0:
        assert isinstance(t,int)
        return t
    if isinstance(t,int): return AND(pad(t,h-1),pad(t,h-1))
    return (t[0],pad(t[1],h-1),pad(t[2],h-1))
formula=pad(formula,6)
def canonical(t,permutations):
    if isinstance(t,int):
        v=t%4+4*permutations[t%4][t//4]
        return v,(v,)
    a,ka=canonical(t[1],permutations)
    b,kb=canonical(t[2],permutations)
    if ka>kb:a,b,ka,kb=b,a,kb,ka
    return (t[0],a,b),ka+kb
perms=list(itertools.permutations(range(3)))
formula,key=min((canonical(formula,p) for p in itertools.product(perms,repeat=4)),key=lambda v:v[1])
nodes={}
def collect(t,n=1):
    nodes[n]=t
    if not isinstance(t,int):collect(t[1],2*n);collect(t[2],2*n+1)
collect(formula)
def evaluate(t,mask):
    if isinstance(t,int):return bool((mask>>t)&1)
    a,b=evaluate(t[1],mask),evaluate(t[2],mask)
    return a and b if t[0]=='and' else a or b
truth={}
for variable in range(1,pool.top+1):
    item=pool.obj(variable)
    if item[0]=='pick':truth[variable]=nodes[item[1]]==item[2]
    elif item[0]=='or':truth[variable]=nodes[item[1]][0]=='or'
    else:truth[variable]=evaluate(nodes[item[1]],samples[item[2]][0])
violated=[i for i,c in enumerate(cnf.clauses) if not any(truth[abs(lit)]==(lit>0) for lit in c)]
assert not violated, violated[:10]
assert all(evaluate(formula,m)==namespace['target'](m) for m in range(4096))
report={'known_path4_depth':6,'all_4096_inputs_verified':True,'all_encoding_clauses_satisfied':True,
        'clause_count':len(cnf.clauses),'variables':pool.top,
        'limitation':'This checks an existing depth6 upper bound; it does not certify the depth5 UNSAT result.'}
(root/'known-path4-calibration.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
