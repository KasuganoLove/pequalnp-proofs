import itertools
import json
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent / 'deps'))
from pysat.formula import CNF, IDPool
from pysat.solvers import Solver

root = Path(__file__).parent
depth = 6
count = 1 << depth
pool = IDPool()
cnf = CNF()
pick = lambda leaf, variable: pool.id(('pick', leaf, variable))
value = lambda node, sample: pool.id(('value', node, sample))
op = lambda node: pool.id(('or', node))

def target(mask):
    majority = [sum((mask >> (i+5*k)) & 1 for k in range(3)) >= 2 for i in range(5)]
    return any(majority[i] and majority[(i+1)%5] for i in range(5))

positive = set()
for i in range(5):
    for first in itertools.combinations(range(3),2):
        for second in itertools.combinations(range(3),2):
            positive.add(sum(1 << (i+5*k) for k in first) |
                         sum(1 << ((i+1)%5+5*k) for k in second))
negative = set()
for independent in itertools.combinations(range(5),2):
    if (independent[0]-independent[1])%5 in (1,4):
        continue
    outside = [i for i in range(5) if i not in independent]
    full = sum(1 << (i+5*k) for i in independent for k in range(3))
    for singles in itertools.product(range(3),repeat=3):
        negative.add(full | sum(1 << (i+5*k) for i,k in zip(outside,singles)))
assert len(positive) == 45 and len(negative) == 135
assert all(target(x) for x in positive) and not any(target(x) for x in negative)
samples = [(mask,True) for mask in sorted(positive)] + [(mask,False) for mask in sorted(negative)]

for leaf in range(count,2*count):
    choices = [pick(leaf,v) for v in range(15)]
    cnf.append(choices)
    for a,b in itertools.combinations(choices,2):
        cnf.append([-a,-b])
    for sid,(mask,_) in enumerate(samples):
        for v in range(15):
            cnf.append([-pick(leaf,v), value(leaf,sid) if (mask>>v)&1 else -value(leaf,sid)])

for node in range(1,count):
    for sid,(_,truth) in enumerate(samples):
        a,b,z = value(2*node,sid),value(2*node+1,sid),value(node,sid)
        selector = op(node)
        cnf.extend([[selector,-a,-b,z],[selector,a,-z],[selector,b,-z],
                    [-selector,a,b,-z],[-selector,-a,z],[-selector,-b,z]])

for sid,(_,truth) in enumerate(samples):
    cnf.append([value(1,sid) if truth else -value(1,sid)])

# Order child subtrees by their minimum variable. Recursively this minimum
# occurs at the leftmost leaf. This only fixes commutative gate symmetry.
for node in range(1,count):
    height = depth - node.bit_length() + 1
    left = (2*node) << (height-1)
    right = (2*node+1) << (height-1)
    for a in range(15):
        for b in range(a):
            cnf.append([-pick(left,a),-pick(right,b)])
# Every input is essential, so variable0 occurs and can be the first leaf.
cnf.append([pick(count,0)])

# Canonical first occurrence order within each symmetric majority gadget.
for leaf in range(count,2*count):
    for group in range(5):
        for copy in (1,2):
            cnf.append([-pick(leaf,group+5*copy)] +
                       [pick(previous,group+5*(copy-1)) for previous in range(count,leaf)])
cnf.append([pick(count+1,v) for v in (0,1,2,5)])

print(json.dumps({'variables':pool.top,'clauses':len(cnf.clauses),'positive':45,'negative':135}),flush=True)
start = time.monotonic()
with Solver(name='cadical195', bootstrap_with=cnf.clauses) as solver:
    deadline = start + 600
    rounds = 0
    while True:
        solver.conf_budget(5000)
        result = solver.solve_limited()
        rounds += 1
        if rounds % 5 == 0:
            print(json.dumps({'rounds':rounds,'seconds':time.monotonic()-start,'stats':solver.accum_stats()}),flush=True)
        if result is not None or time.monotonic() >= deadline:
            break
    print(json.dumps({'sat':result,'seconds':time.monotonic()-start,'stats':solver.accum_stats()}),flush=True)
    if result:
        model = set(x for x in solver.get_model() if x>0)
        labels = {str(k):next(v for v in range(15) if pick(k,v) in model) for k in range(count,2*count)}
        operators = {str(k):('or' if op(k) in model else 'and') for k in range(1,count)}
        def evaluate(mask):
            values = {k:bool((mask>>labels[str(k)])&1) for k in range(count,2*count)}
            for k in range(count-1,0,-1):
                values[k] = (values[2*k] or values[2*k+1]) if operators[str(k)]=='or' else (values[2*k] and values[2*k+1])
            return values[1]
        assert all(evaluate(mask)==target(mask) for mask in range(1<<15))
        witness = {'depth':depth,'operators':operators,'leaves':labels,'all_32768_inputs_verified':True}
        (root/'witness.json').write_text(json.dumps(witness,indent=2)+'\n')
        print('WITNESS VERIFIED ON ALL32768 INPUTS',flush=True)
