"""Replay any SAT model against clauses and literal Rank semantics."""
from pathlib import Path
import hashlib,json
from encode import encode,direct
P=Path(__file__).resolve().parent
text=(P/'cadical.log').read_text()
assert 's SATISFIABLE' in text, 'No SAT verdict; no model is being claimed.'
lits=[int(v) for l in text.splitlines() if l.startswith('v ') for v in l[2:].split() if int(v)]
assigned={abs(v):v>0 for v in lits}
A,C,nv,counts,d,p=encode(15,14)
assert all(any(assigned.get(abs(v),False)==(v>0) for v in c) for c in C)
schedule=[]
for v in range(90):
    choices=[t for t in range(15) if assigned.get(d(v,t),False)]
    assert len(choices)==1
    schedule.append(choices[0])
assert direct(A,schedule,14)
R=set(range(45)); Cset=set(range(45)); replay=[]
for t in range(1,15):
    X=sorted(a for a in R if schedule[a]==t)
    Y=sorted(b for b in Cset if schedule[45+b]==t)
    assert all(A[a][c]==A[b][c] for a in X for b in X for c in Cset)
    assert all(A[a][c]==A[a][e] for c in Y for e in Y for a in R)
    replay.append({'round':t,'rows':X,'columns':Y})
    R-=set(X); Cset-=set(Y)
out={'family_k':15,'rank_budget':14,'all_cnf_clauses_satisfied':True,
     'literal_public_adjacency_checked':True,'every_round_twins_checked':True,'terminal_bic_checked':True,
     'rounds':replay,'remaining_rows':sorted(R),'remaining_columns':sorted(Cset),
     'scope':'An explicit Rank14 schedule. This is NOT a circuit witness and does NOT settle10083.',
     'log_sha256':hashlib.sha256((P/'cadical.log').read_bytes()).hexdigest()}
(P/'verified-schedule.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'verified':True,'remaining_rows':len(R),'remaining_columns':len(Cset)}))
