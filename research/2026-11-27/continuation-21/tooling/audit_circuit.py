#!/usr/bin/env python3
"""Independent scalar and packed evaluation for a promised bipartite circuit."""
import argparse, hashlib, json, pathlib

def audit(d):
    n, m = d['n'], d['m']
    gates, output = d['gates'], d['output']
    rows = [int(x,0) if isinstance(x,str) else x for x in d['rows']]
    assert n > 0 and m > 0 and len(rows) == n
    assert isinstance(output,int) and not isinstance(output,bool) and output >= 0
    assert all(0 <= r < 2**m for r in rows)
    assert len(gates) <= d['bound']
    counts = {'and':0,'or':0,'not':0}
    for j,g in enumerate(gates):
        op, ins = g['op'], g['inputs']
        assert op in counts and len(ins) <= 2
        assert all(isinstance(a,int) and 0 <= a < n+m+j for a in ins)
        counts[op] += 1
    def scalar(u,v):
        wires = [i == u for i in range(n)]+[j == v for j in range(m)]
        for g in gates:
            vals = [wires[a] for a in g['inputs']]
            if g['op']=='and': z = all(vals)
            elif g['op']=='or': z = any(vals)
            else: z = not (vals[0] if vals else False)
            wires.append(z)
        return wires[output] if output < len(wires) else False
    scalar_rows = [sum((1 << v) for v in range(m) if scalar(u,v)) for u in range(n)]
    mask = (1 << (n*m))-1
    wires = [((1 << m)-1) << (u*m) for u in range(n)]
    wires += [sum(1 << (u*m+v) for u in range(n)) for v in range(m)]
    for g in gates:
        vals = [wires[a] for a in g['inputs']]
        if g['op']=='and':
            z = mask
            for a in vals: z &= a
        elif g['op']=='or':
            z = 0
            for a in vals: z |= a
        else: z = mask ^ (vals[0] if vals else 0)
        wires.append(z)
    packed = wires[output] if output < len(wires) else 0
    packed_rows = [(packed >> (u*m)) & ((1<<m)-1) for u in range(n)]
    assert scalar_rows == packed_rows, 'Independent evaluators disagree'
    assert scalar_rows == rows, 'Circuit does not represent the posted graph'
    target_bytes = b''.join(r.to_bytes((m+7)//8,'little') for r in rows)
    reachable = set()
    def visit(w):
        if w < n+m or w in reachable or w >= n+m+len(gates): return
        reachable.add(w)
        for a in gates[w-n-m]['inputs']: visit(a)
    visit(output)
    return {'passed':True,'n':n,'m':m,'promise_inputs':n*m,'gates':len(gates),'bound':d['bound'],
            'operations':counts,'all_reads_earlier':True,'reachable_gates':len(reachable),
            'independent_evaluators':['scalar Boolean gate evaluator','packed integer column evaluator'],
            'row_bytes_sha256':hashlib.sha256(target_bytes).hexdigest()}

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('circuit',type=pathlib.Path)
    p.add_argument('--output',type=pathlib.Path)
    a=p.parse_args()
    result=audit(json.loads(a.circuit.read_text()))
    result['circuit_file_sha256']=hashlib.sha256(a.circuit.read_bytes()).hexdigest()
    text=json.dumps(result,indent=2)+'\n'
    if a.output:
        a.output.parent.mkdir(parents=True,exist_ok=True)
        a.output.write_text(text)
    print(text)
