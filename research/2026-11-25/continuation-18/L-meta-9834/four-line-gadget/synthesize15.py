#!/usr/bin/env python3
"""One bounded exact read-back AND/OR/NOT synthesis attempt.

The CNF supports exactly fifteen gates, raw inputs 0..11, constants as gates,
and copies via repeated operands. It constrains every one of the 4096 input
assignments. An operation selector guards its truth-table clauses; two one-hot
pin selectors guard equalities to earlier wires. The last gate is the output.
This script is a witness search, not a formal completeness/UNSAT certificate.
"""
from pathlib import Path
import argparse, datetime, hashlib, json, resource, subprocess, time

N, K, ROWS = 12, 15, 4096
EDGES = [(1, 5), (1, 6), (1, 7), (1, 8), (2, 0), (2, 5), (2, 9), (3, 0), (3, 6), (3, 10), (4, 0), (4, 7), (4, 11)]
OPS = ['and', 'or', 'not', 'false', 'true']

def expected(row):
    return any((row >> a) & 1 and (row >> b) & 1 for a,b in EDGES)

def prepare(directory):
    counter = 0
    def new(count):
        nonlocal counter
        result = list(range(counter + 1, counter + count + 1))
        counter += count
        return result
    gates = []
    for j in range(K):
        gates.append({'a':new(N+j), 'b':new(N+j), 'op':new(len(OPS)),
                      'av':new(ROWS), 'bv':new(ROWS), 'v':new(ROWS)})
    clauses = 0
    body = directory / 'formula-body.tmp'
    with body.open('w') as f:
        def add(*c):
            nonlocal clauses
            f.write(' '.join(map(str,c)) + ' 0\n')
            clauses += 1
        def onehot(vs):
            add(*vs)
            for a in range(len(vs)):
                for b in range(a):
                    add(-vs[a], -vs[b])
        for j,g in enumerate(gates):
            onehot(g['a']); onehot(g['b']); onehot(g['op'])
            # AND/OR are commutative; NOT ignores b, so b may be set to a.
            for a,sa in enumerate(g['a']):
                for sb in g['b'][:a]:
                    add(-sa,-sb)
            for r in range(ROWS):
                for pins,vs in [('a','av'),('b','bv')]:
                    z = g[vs][r]
                    for w,s in enumerate(g[pins]):
                        if w < N:
                            add(-s, z if (r >> w) & 1 else -z)
                        else:
                            u = gates[w-N]['v'][r]
                            add(-s,-z,u); add(-s,z,-u)
                a,b,z = g['av'][r],g['bv'][r],g['v'][r]
                s = g['op'][0]  # z <-> a AND b
                add(-s,-z,a); add(-s,-z,b); add(-s,z,-a,-b)
                s = g['op'][1]  # z <-> a OR b
                add(-s,z,-a); add(-s,z,-b); add(-s,-z,a,b)
                s = g['op'][2]  # z <-> NOT a
                add(-s,-z,-a); add(-s,z,a)
                add(-g['op'][3],-z); add(-g['op'][4],z)
        # Every raw variable is essential in the13-edge function.
        for w in range(N):
            add(*(g[p][w] for g in gates for p in ('a','b')))
        # Any witness can discard dead gates then pad with output copies.
        # Syntactic read constraints are a weaker necessary form of liveness.
        for j in range(K-1):
            add(*(gates[k][p][N+j] for k in range(j+1,K) for p in ('a','b')))
        # This bounded search permits at most one NOT position. The public
        # L-meta-9834 task itself permits arbitrarily many counted NOT gates.
        for j in range(K):
            for i in range(j):
                add(-gates[i]['op'][2], -gates[j]['op'][2])
        for r in range(ROWS):
            add(gates[-1]['v'][r] if expected(r) else -gates[-1]['v'][r])
    formula = directory/'formula.cnf'
    with formula.open('wb') as out, body.open('rb') as src:
        out.write(f'p cnf {counter} {clauses}\n'.encode())
        for chunk in iter(lambda:src.read(1048576),b''):
            out.write(chunk)
    body.unlink()
    meta = {'inputs':N,'gates':K,'rows':ROWS,'ops':OPS,'variables':counter,
            'clauses':clauses,'cnf_bytes':formula.stat().st_size,
            'cnf_sha256':hashlib.sha256(formula.read_bytes()).hexdigest(),
            'wire_order':'raw 0..11; gates 12..26; output26', 'maximum_not_gates':1,
            'selectors':gates}
    (directory/'encoding.json').write_text(json.dumps(meta)+'\n')
    return meta

def verify_sat(directory, meta, model):
    circuit = []
    for g in meta['selectors']:
        def pick(vs):
            found = [i for i,v in enumerate(vs) if v in model]
            assert len(found)==1, found
            return found[0]
        selected,a,b = OPS[pick(g['op'])],pick(g['a']),pick(g['b'])
        op = 'or' if selected == 'false' else 'and' if selected == 'true' else selected
        circuit.append({'op':op,'inputs':[] if selected in ('false','true') else
                        ([a] if selected=='not' else [a,b])})
    assert sum(g['op']=='not' for g in circuit) <= 1
    errors=[]
    for r in range(ROWS):
        wires=[bool((r>>i)&1) for i in range(N)]
        for j,g in enumerate(circuit):
            assert all(0<=i<N+j for i in g['inputs'])
            xs=[wires[i] for i in g['inputs']]
            val = (all(xs) if g['op']=='and' else any(xs) if g['op']=='or'
                   else not xs[0] if g['op']=='not' else g['op']=='true')
            wires.append(val)
        if wires[-1] != expected(r):
            errors.append(r)
    result={'size':K,'output':N+K-1,'gates':circuit,'verified_rows':ROWS,
            'mismatches':errors,'not_count':sum(g['op']=='not' for g in circuit)}
    (directory/'candidate.json').write_text(json.dumps(result,indent=2)+'\n')
    assert not errors, errors
    # Independent literal check of all generated CNF clauses against model.
    checked=0
    with (directory/'formula.cnf').open() as f:
        for line in f:
            if line.startswith(('c','p')): continue
            c=[int(x) for x in line.split()[:-1]]
            assert any((v in model) if v>0 else (-v not in model) for v in c)
            checked+=1
    result['cnf_clauses_checked']=checked
    return result

def main():
    p=argparse.ArgumentParser(); p.add_argument('--solver',required=True)
    p.add_argument('--seconds',type=int,default=300)
    args=p.parse_args(); directory=Path(__file__).resolve().parent
    meta=prepare(directory)
    print(json.dumps({k:v for k,v in meta.items() if k!='selectors'}),flush=True)
    def limits():
        resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3))
        resource.setrlimit(resource.RLIMIT_CPU,(args.seconds,args.seconds+2))
    start_utc=datetime.datetime.now(datetime.timezone.utc).isoformat()
    start=time.monotonic(); before=resource.getrusage(resource.RUSAGE_CHILDREN)
    status='UNKNOWN'; timed_out=False
    with (directory/'solver.log').open('w') as log:
        child=subprocess.Popen([args.solver,str(directory/'formula.cnf')],
                               stdout=log,stderr=subprocess.STDOUT,preexec_fn=limits)
        try: rc=child.wait(timeout=args.seconds)
        except subprocess.TimeoutExpired:
            timed_out=True; child.terminate()
            try: rc=child.wait(timeout=3)
            except subprocess.TimeoutExpired:
                child.kill(); rc=child.wait()
    after=resource.getrusage(resource.RUSAGE_CHILDREN)
    result={'start_utc':start_utc,'end_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
            'status':status,'exit_code':rc,'wall_seconds':time.monotonic()-start,
            'cpu_seconds':after.ru_utime+after.ru_stime-before.ru_utime-before.ru_stime,
            'max_rss_kib':after.ru_maxrss,'wall_limit_seconds':args.seconds,
            'virtual_memory_limit_bytes':2*1024**3,'timed_out':timed_out,
            'public_unsat_claim':False,'attempts':1}
    content=(directory/'solver.log').read_text()
    if 's SATISFIABLE' in content:
        model={int(v) for line in content.splitlines() if line.startswith('v ')
               for v in line[2:].split() if int(v)>0}
        checked=verify_sat(directory,meta,model)
        result.update(status='SAT',verified_rows=ROWS,not_count=checked['not_count'],cnf_clauses_checked=checked['cnf_clauses_checked'])
    elif 's UNSATISFIABLE' in content:
        result['status']='UNSAT in encoded read-back model; no formal certificate checked'
    (directory/'result.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result),flush=True)

if __name__=='__main__': main()
