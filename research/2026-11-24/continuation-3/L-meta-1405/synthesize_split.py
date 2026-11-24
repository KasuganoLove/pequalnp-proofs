import sys
import json
import time
from pathlib import Path

root=Path(__file__).parent
source=(root/'synthesize.py').read_text().replace('depth = 6','depth = 5')
source=source[:source.index("print(json.dumps({'variables'")]
source=source.replace('    cnf.append([value(1,sid) if truth else -value(1,sid)])','    pass')
source=source.replace('cnf.append([pick(count,0)])','')
ns={'__file__':str(root/'synthesize.py')}
exec(source,ns)
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType
pool,base,samples=ns['pool'],ns['cnf'],ns['samples']
value,pick,op=ns['value'],ns['pick'],ns['op']
count=ns['count']
start=time.monotonic()
deadline=start+420
def solve_until(solver,until):
    while time.monotonic()<until:
        solver.conf_budget(3000)
        answer=solver.solve_limited()
        if answer is not None:return answer
    return None
def tree(model,n=1):
    if n>=count:return next(v for v in range(15) if pick(n,v) in model)
    return ('or' if op(n) in model else 'and',tree(model,2*n),tree(model,2*n+1))
def evaluate(t,mask):
    if isinstance(t,int):return bool((mask>>t)&1)
    a,b=evaluate(t[1],mask),evaluate(t[2],mask)
    return a or b if t[0]=='or' else a and b
def save(t):
    assert all(evaluate(t,m)==ns['target'](m) for m in range(32768))
    operators,leaves={},{}
    def walk(t,n=1):
        if isinstance(t,int):leaves[str(n)]=t
        else:operators[str(n)]=t[0];walk(t[1],2*n);walk(t[2],2*n+1)
    walk(t)
    (root/'witness.json').write_text(json.dumps({'depth':6,'operators':operators,'leaves':leaves,'all_32768_inputs_verified':True},indent=2)+'\n')
    print('WITNESS VERIFIED ON ALL32768 INPUTS',flush=True)

for mode in ('or','and'):
    mode_deadline=min(deadline,time.monotonic()+210)
    fixed=[sid for sid,(_,truth) in enumerate(samples) if truth==(mode=='and')]
    covered=[sid for sid,(_,truth) in enumerate(samples) if truth==(mode=='or')]
    sign=1 if mode=='or' else -1
    clauses=list(base.clauses)+[[(-sign)*value(1,sid)] for sid in fixed]
    symmetry=[[pick(count,0)]]
    for leaf in range(count,2*count):
        for group in range(5):
            for copy in (1,2):
                symmetry.append([-pick(leaf,group+5*copy)]+
                                [pick(previous,group+5*(copy-1)) for previous in range(count,leaf)])
    cardinality=CardEnc.atleast([sign*value(1,sid) for sid in covered],bound=(len(covered)+1)//2,vpool=pool,encoding=EncType.totalizer)
    print(json.dumps({'mode':mode,'coverage_count':len(covered),'required_first':(len(covered)+1)//2,'variables':pool.top,'clauses':len(clauses)+len(symmetry)+len(cardinality.clauses)}),flush=True)
    with Solver(name='cadical195',bootstrap_with=clauses+symmetry+cardinality.clauses) as first:
        rounds=0
        while time.monotonic()<mode_deadline:
            answer=solve_until(first,mode_deadline)
            if answer is not True:
                print(json.dumps({'mode':mode,'first_result':answer,'seconds':time.monotonic()-start,'stats':first.accum_stats()}),flush=True)
                break
            model=set(x for x in first.get_model() if x>0)
            missing=[sid for sid in covered if ((value(1,sid) in model)!=(sign==1))]
            print(json.dumps({'mode':mode,'candidate':rounds,'covered':len(covered)-len(missing),'missing':len(missing),'seconds':time.monotonic()-start}),flush=True)
            with Solver(name='cadical195',bootstrap_with=clauses+[[sign*value(1,sid)] for sid in missing]) as second:
                answer2=solve_until(second,min(mode_deadline,time.monotonic()+40))
                if answer2:
                    model2=set(x for x in second.get_model() if x>0)
                    save((mode,tree(model),tree(model2)))
                    raise SystemExit(0)
                if answer2 is None:
                    # A timeout excludes only this exact coverage pattern from
                    # this heuristic search; it proves no mathematical claim.
                    first.add_clause([(-sign if sid not in missing else sign)*value(1,sid) for sid in covered])
                else:
                    first.add_clause([sign*value(1,sid) for sid in missing])
            rounds+=1
print(json.dumps({'status':'no_witness_in_bounded_split_search','seconds':time.monotonic()-start}),flush=True)
