#!/usr/bin/env python3
"""Fixed-OR-count exact finite encoding, with no bound on AND gates.

Each OR operand and the final output is an arbitrary conjunction of original
inputs, earlier OR outputs, and a false signal. Empty conjunction is true.
All64 C6 input rows are constrained. Port commutation is broken by lex order.
"""
import argparse
import json
from pathlib import Path

P=Path(__file__).resolve().parent
N=6
EDGES=[(0,1),(1,2),(2,3),(3,4),(4,5),(5,0)]

class CNF:
    def __init__(self):self.n=0;self.clauses=[]
    def var(self):self.n+=1;return self.n
    def add(self,*lits):self.clauses.append(list(lits))
    def lex(self,a,b):
        eq=self.var();self.add(eq)
        for x,y in zip(a,b):
            self.add(-eq,-x,y)
            nxt=self.var()
            self.add(-nxt,eq);self.add(-nxt,-x,y);self.add(-nxt,x,-y)
            self.add(-eq,-x,-y,nxt);self.add(-eq,x,y,nxt)
            eq=nxt

def generate(k,calibrate=False):
    c=CNF();rows=[[c.var() for m in range(64)] for i in range(k)]
    ports=[]
    def port(stage):
        sources=[f'x{v}' for v in range(N)]+[f'o{i}' for i in range(stage)]+['false']
        sel=[c.var() for s in sources]
        vals=[]
        for mask in range(64):
            p=c.var();vals.append(p);bad=[]
            for name,q in zip(sources,sel):
                if name=='false':v=False
                elif name[0]=='x':v=bool(mask>>int(name[1:])&1)
                else:v=rows[int(name[1:])][mask]
                if v is True:continue
                if v is False:b=q
                else:
                    b=c.var();c.add(-b,q);c.add(-b,-v);c.add(-q,v,b)
                bad.append(b);c.add(-p,-b)
            c.add(p,*bad)
        meta={'stage':stage,'sources':sources,'selectors':sel,'row_variables':vals}
        ports.append(meta)
        return vals,sel
    for i in range(k):
        a,sa=port(i);b,sb=port(i);c.lex(sa,sb)
        for m in range(64):
            o=rows[i][m];c.add(-a[m],o);c.add(-b[m],o);c.add(-o,a[m],b[m])
    out,_=port(k)
    for m in range(64):
        f=any((m>>a&1) and (m>>b&1) for a,b in EDGES)
        c.add(out[m] if f else -out[m])
    if calibrate:
        assert k==5
        selected=[['x1'],['x5'],['x1'],['x3'],['x3'],['x5'],
                  ['x0','o0'],['x2','o1'],['o3'],['x4','o2'],['o4']]
        for i in range(k):
            aa=selected[2*i];bb=selected[2*i+1];src=ports[2*i]['sources']
            if [s in aa for s in src]>[s in bb for s in src]:selected[2*i],selected[2*i+1]=bb,aa
        for p,names in zip(ports,selected):
            for src,q in zip(p['sources'],p['selectors']):c.add(q if src in names else -q)
    stem=f'c6-k{k}'+('-calibration' if calibrate else '')
    with (P/(stem+'.cnf')).open('w') as f:
        f.write(f'p cnf {c.n} {len(c.clauses)}\n')
        for clause in c.clauses:f.write(' '.join(map(str,clause))+' 0\n')
    meta={'n':N,'or_count':k,'input_rows':64,'variables':c.n,'clauses':len(c.clauses),
          'ports':ports,'or_row_variables':rows,'calibration':calibrate,
          'edges':EDGES,'no_and_gate_bound':True}
    (P/(stem+'.json')).write_text(json.dumps(meta,indent=2)+'\n')
    print(json.dumps({key:meta[key] for key in ['n','or_count','variables','clauses','calibration','no_and_gate_bound']}))

def decode(stem):
    meta=json.loads((P/(stem+'.json')).read_text())
    lines=(P/(stem+'.solution')).read_text().splitlines()
    status=next((s for s in lines if s.startswith('s ')),None)
    if status!='s SATISFIABLE':print(json.dumps({'status':status}));return
    assignment={abs(v):v>0 for s in lines if s.startswith('v ') for v in map(int,s.split()[1:]) if v}
    selected=[[src for src,v in zip(p['sources'],p['selectors']) if assignment[v]] for p in meta['ports']]
    # Independent scalar evaluation, not the CNF's row-variable assignment.
    for mask in range(64):
        values={f'x{v}':bool(mask>>v&1) for v in range(N)};values['false']=False
        for i in range(meta['or_count']):
            values[f'o{i}']=all(values[s] for s in selected[2*i]) or all(values[s] for s in selected[2*i+1])
        got=all(values[s] for s in selected[-1])
        want=any((mask>>a&1) and (mask>>b&1) for a,b in EDGES)
        assert got==want,(mask,got,want)
    # Translate arbitrary conjunctions into fan-in≤2 AND gates, reusing inputs.
    gates=[];wires={f'x{v}':v for v in range(N)}
    def add(op,ins):gates.append({'op':op,'inputs':ins});return N+len(gates)-1
    def conjunction(names):
        if 'false' in names:
            if 'false' not in wires:wires['false']=add('and',[1000000])
            return wires['false']
        if not names:return add('and',[])
        out=wires[names[0]]
        for name in names[1:]:out=add('and',[out,wires[name]])
        return out
    for i in range(meta['or_count']):
        left=conjunction(selected[2*i]);right=conjunction(selected[2*i+1])
        wires[f'o{i}']=add('or',[left,right])
    output=conjunction(selected[-1])
    for mask in range(64):
        w=[bool(mask>>v&1) for v in range(N)]
        for g in gates:
            vals=[w[i] if i<len(w) else False for i in g['inputs']]
            w.append(all(vals) if g['op']=='and' else any(vals))
        assert w[output]==any((mask>>a&1) and (mask>>b&1) for a,b in EDGES)
    result={'status':'SATISFIABLE','or_count':meta['or_count'],'total_gates':len(gates),
            'selected_ports':selected,'rows_independently_verified':64,'gates':gates,'output':output}
    (P/(stem+'-circuit.json')).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({key:result[key] for key in ['status','or_count','total_gates','rows_independently_verified','selected_ports']}))

if __name__=='__main__':
    a=argparse.ArgumentParser();a.add_argument('--k',type=int,default=4);a.add_argument('--calibrate',action='store_true');a.add_argument('--decode')
    args=a.parse_args()
    if args.decode:decode(args.decode)
    else:generate(args.k,args.calibrate)
