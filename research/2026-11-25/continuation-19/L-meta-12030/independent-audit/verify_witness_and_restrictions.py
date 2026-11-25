#!/usr/bin/env python3
"""Independent scalar verification of12030's exact edge list and submitted control.
No solver or Lean invocation; the core lower bound itself is not proved here.
"""
import pathlib,re,json,hashlib,datetime,itertools
base=pathlib.Path(__file__).resolve().parents[1];gap=json.loads((base/'gap.json').read_text());s=gap['statement']
rawlists=[list(map(int,re.findall(r'\d+',m))) for m in re.findall(r'\(\[([\d,\s]+)\] : List ℕ\)',s)]
assert len(rawlists)==6 and all(r==rawlists[0] for r in rawlists),'The posted repeated lists differ or changed format'
flat=rawlists[0];assert len(flat)==28;edges=list(zip(flat[::2],flat[1::2]));assert len(set(edges))==14
expected=[(0,3),(1,3),(0,4),(1,4),(0,5),(1,5),(3,5),(4,5),(0,6),(1,6),(2,6),(3,6),(4,6),(5,6)]
assert edges==expected,'Exact target edges differ from the audited task'
gates=[('or',[0,1]),('or',[3,4]),('and',[7,8]),('or',[7,8]),('and',[10,5]),('or',[9,11]),('or',[10,5]),('or',[13,2]),('and',[14,6]),('or',[12,15])];output=16
legal=all(op in ['and','or'] and len(ins)==2 and all(0<=j<7+i for j in ins) for i,(op,ins) in enumerate(gates));assert legal
# This deliberately uses scalar lists/default-false reads, not bit-parallel code.
def ev(mask):
 w=[bool(mask&(1<<i)) for i in range(7)]
 for op,ins in gates:
  vals=[w[j] if 0<=j<len(w) else False for j in ins]
  w.append(all(vals) if op=='and' else any(vals))
 return w[output] if output<len(w) else False

def target(mask,deleted=()):
 for v in deleted:mask&=~(1<<v)
 return any(bool(mask&(1<<u)) and bool(mask&(1<<v)) for u,v in edges)
errors=[r for r in range(128) if ev(r)!=target(r)];assert not errors
steps=[];deleted=[]
for v,witness in [(1,10),(2,68),(4,17)]:
 before=target(witness,deleted);after=target(witness,deleted+[v]);nz=target(9,deleted+[v]);zero=target(0,deleted+[v]);assert before and not after and nz and not zero
 steps.append({'deleted_before':deleted[:],'vertex':v,'essential_assignment':witness,'essential_bits':[i for i in range(7) if witness>>i&1],'before':before,'after_fix_false':after,'nonzero_assignment':9,'nonzero_bits':[0,3],'nonzero_value_after':nz,'zero_assignment_value_after':zero})
 deleted.append(v)
core=[0,3,5,6];remaining=[list(e) for e in edges if not set(e)&set(deleted)];want=[list(e) for e in itertools.combinations(core,2)];assert sorted(remaining)==sorted(want)
core_errors=[]
for r in range(16):
 mask=sum((1<<v) for i,v in enumerate(core) if r>>i&1)
 if target(mask,deleted)!=(r.bit_count()>=2):core_errors.append(r)
assert not core_errors
report={'task':gap['id'],'timestamp':datetime.datetime.now(datetime.timezone.utc).isoformat(),'statement_sha256':hashlib.sha256(s.encode()).hexdigest(),'exact_edges':edges,'all_six_posted_edge_lists_identical':True,'witness':{'n_inputs':7,'gates':gates,'output':output,'size':len(gates),'and_count':sum(op=='and' for op,_ in gates),'or_count':sum(op=='or' for op,_ in gates),'not_count':0,'fanin_at_most_two':legal,'reads_back':legal,'all_assignments_tested':128,'errors':errors},'restriction_steps':steps,'core':{'vertices':core,'remaining_edges':remaining,'complete_graph_K4':True,'assignments_tested':16,'errors':core_errors},'scope':'Ordinary independent scalar audit only. The complete lower bound and exact public theorem remain the responsibility of the separately checked Lean proof.'}
(base/'independent-audit/verification.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'task':gap['id'],'gate_count':len(gates),'and':report['witness']['and_count'],'or':report['witness']['or_count'],'assignments':128,'errors':len(errors),'essential_witnesses':[x['essential_assignment'] for x in steps],'nonzero_witness':9,'core_vertices':core,'core_edges':len(remaining),'all_pass':True},indent=2))
