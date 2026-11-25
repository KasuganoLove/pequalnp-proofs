#!/usr/bin/env python3
"""Finite necessary-condition table for a unique nonzero input reader.

Enumerates arbitrary Boolean functions on at most two ORIGINAL variables.
Free NOT(x0) is derived from x0, never treated as an independent input.
This is finite Python validation, not a Lean proof or a circuit lower bound.
"""
import itertools
import json
from pathlib import Path

P=Path(__file__).resolve().parent
EDGES=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
EDGESET={tuple(sorted(e)) for e in EDGES}

def target(m):
    return any((m>>a&1) and (m>>b&1) for a,b in EDGES)

def scalar_check(c):
    errors=[]
    for m in range(1024):
        w=[bool(m>>i&1) for i in range(10)]+[not bool(m&1)]
        for op,ins in c['gates']:
            assert op in ['and','or','not'] and all(i<len(w) for i in ins)
            assert len(ins)<=2
            value=all(w[i] for i in ins) if op=='and' else any(w[i] for i in ins) if op=='or' else not w[ins[0]]
            w.append(value)
        if w[c['output']]!=target(m):errors.append(m)
    active=lambda op,ins:ins[:1] if op=='not' else ins
    readers0=[j for j,(op,ins) in enumerate(c['gates']) if any(i in [0,10] for i in active(op,ins))]
    readers1=[j for j,(op,ins) in enumerate(c['gates']) if 1 in active(op,ins)]
    assert not errors and len(readers0)==3 and len(readers1)==1 and len(c['gates'])==29
    return {'rows':1024,'errors':errors,'size':len(c['gates']),
            'active_readers_0_or_10':readers0,'active_readers_variable1':readers1,
            'satisfies_18_gate_cap':False}

def residual_example(kind):
    gs=[]
    def add(op,*ins):gs.append([op,list(ins)]);return 10+len(gs)
    edge_wires={}
    for a,b in EDGES:
        if 1 not in [a,b]:edge_wires[tuple(sorted((a,b)))]=add('and',a,b)
    terms=list(edge_wires.values());f0=terms[0]
    for w in terms[1:]:f0=add('or',f0,w)
    e=edge_wires[(2,3)]
    n=add('or',0,2);n=add('or',n,6)
    if kind=='and_with_nand_edge':
        h=add('not',e);g=add('and',1,h);term=add('and',g,n)
    else:
        g=add('or',1,e);h=add('or',n,e);term=add('and',g,h)
    out=add('or',f0,term)
    return {'kind':kind,'gates':gs,'output':out,'unique_variable':1,'partner_edge':[2,3]}

def main():
    singles=[];pairs=[];pivotal_counts={}
    for v in range(1,10):
        pivots=[m for m in range(1024) if not(m>>v&1) and not target(m) and target(m|(1<<v))]
        assert len(pivots)==40;pivotal_counts[str(v)]=len(pivots)
        for w in range(10):
            if w==v:continue
            projected=sorted({m>>w&1 for m in pivots});assert projected==[0,1]
            allowed_and=[h for h in range(4) if all(h>>b&1 for b in projected)]
            allowed_or=[h for h in range(4) if all(not(h>>b&1) for b in projected)]
            assert allowed_and==[3] and allowed_or==[0]
            singles.append({'v':v,'w':w,'projection':projected,'allowed_and_partner_tables':allowed_and,'allowed_or_partner_tables':allowed_or})
        for j,k in itertools.combinations([w for w in range(10) if w!=v],2):
            witness={}
            for m in pivots:witness.setdefault((m>>j&1)+2*(m>>k&1),m)
            projection=sorted(witness)
            is_edge=(j,k) in EDGESET
            assert projection==([0,1,2] if is_edge else [0,1,2,3])
            allowed_and=[h for h in range(16) if all(h>>b&1 for b in projection)]
            allowed_or=[h for h in range(16) if all(not(h>>b&1) for b in projection)]
            assert allowed_and==([7,15] if is_edge else [15])
            assert allowed_or==([0,8] if is_edge else [0])
            pairs.append({'v':v,'j':j,'k':k,'edge':is_edge,'projection':projection,
                          'witness_masks':{str(b):m for b,m in sorted(witness.items())},
                          'allowed_and_partner_tables':allowed_and,'allowed_or_partner_tables':allowed_or})
    examples=[residual_example('and_with_nand_edge'),residual_example('or_with_and_edge')]
    example_checks=[dict(kind=c['kind'],**scalar_check(c)) for c in examples]
    summary={'checked_by':'Independent exhaustive Python; not Lean',
             'nonzero_variables':9,'pivotal_assignments_per_variable':40,
             'single_variable_projections':len(singles),'two_variable_projections':len(pairs),
             'edge_pair_projections':sum(r['edge'] for r in pairs),
             'nonedge_pair_projections':sum(not r['edge'] for r in pairs),
             'arbitrary_two_variable_truth_tables_per_pair':16,
             'and_or_truth_table_conditions_tested':len(pairs)*16*2,
             'truth_table_encoding':'bit b0+2*b1 stores h(b0,b1); 0=false,7=NAND,8=AND,15=true',
             'free_not0':'derived from original x0, not an independent input',
             'nonconstant_allowed_models':sum(len(r['allowed_and_partner_tables'])+len(r['allowed_or_partner_tables'])-2 for r in pairs),
             'two_29_gate_example_checks':example_checks,
             'limitation':'Necessary local condition only. No18-gate impossibility and no counterexample to it.'}
    (P/'projection-table.json').write_text(json.dumps({'summary':summary,'singles':singles,'pairs':pairs},indent=2)+'\n')
    (P/'residual-examples.json').write_text(json.dumps(examples,indent=2)+'\n')
    (P/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary))

if __name__=='__main__':main()
