from pathlib import Path
import json,re,hashlib

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
LEAN=ROOT/'pequalnp-proofs/lean'
REF=HERE.parent/'L-meta-10696/status-audit/L_meta_9539.reference.lean'
source=REF.read_text()
negative=json.loads((HERE/'gap.json').read_text())['statement']
assert negative.startswith('¬ (') and negative.endswith(')')
statement=negative[len('¬ ('):-1]
edges=[(0,2),(1,3),(0,4),(1,4),(2,4),(3,4),(0,5),(1,5),(2,5),(3,5),(0,6),(1,6),(2,6),(3,6),(4,6)]
edge_list='['+', '.join(str(v) for e in edges for v in e)+']'
old_list='[0, 1, 0, 2, 0, 3, 0, 5, 1, 2, 1, 3, 1, 4, 2, 3, 2, 4]'
target=lambda x:any((x>>a)&1 and (x>>b)&1 for a,b in edges)
positive=[x for x in range(128) if target(x)]
zero=[x for x in range(128) if not target(x)]
samples=[(p,z) for p in positive for z in zero]
P=len(samples);assert P==1596
rows=[]
for i in range(7):
    value=sum(((p>>i)&1)<<k for k,(p,z) in enumerate(samples))
    value+=sum(((z>>i)&1)<<(k+P) for k,(p,z) in enumerate(samples))
    rows.append(value)
expr=' || '.join(f'(x {a} && x {b})' for a,b in edges)
s=source.replace('L_meta_9539','L_meta_10486').replace(old_list,edge_list)
s=re.sub(r'\b1400\b',str(P*2),s)
s=re.sub(r'\b700\b',str(P),s)
s=s.replace('Fin 6','Fin 7').replace('inputs.length = 6','inputs.length = 7')
s=re.sub(r'^def F \(x : Fin 7 → Bool\) : Bool := .*$', 'def F (x : Fin 7 → Bool) : Bool := '+expr,s,flags=re.M)
s=s.replace('search 7','search 10').replace('7 < binaryCost','10 < binaryCost').replace('search_complete ht 7','search_complete ht 10')
start=s.index('def rows : List W :=')
end=s.index('\nset_option maxRecDepth 16000 in',start)
s=s[:start]+'def rows : List W :=\n  ['+', '.join(hex(x) for x in rows)+']\n'+s[end:]
# The task-level circuit and exact public theorem are copied from the current assignment data.
base=json.loads((HERE/'constructive/baseline12.json').read_text())
gate_text='['+', '.join('⟨PEqualNP.CircuitLowerBounds.GateOp.'+g['op']+', ['+', '.join(map(str,g['inputs']))+']⟩' for g in base['gates'])+']'
s=re.sub(r'^def wg : List PEqualNP.CircuitLowerBounds.Gate := .*$', 'def wg : List PEqualNP.CircuitLowerBounds.Gate := '+gate_text,s,flags=re.M)
s=s.replace('rcases hg with '+' | '.join(['rfl']*9), 'rcases hg with '+' | '.join(['rfl']*12))
s=s.replace('⟨wg, 14⟩','⟨wg, 18⟩').replace('wg.length = 9','wg.length = 12').replace('L_meta_10486.wg, 14','L_meta_10486.wg, 18')
bridge_start=s.index('theorem bridge :')
bridge_end=s.index(' := by',bridge_start)
bridge=s[bridge_start:bridge_end]
cut=bridge.rfind(' = ((')
assert cut>=0
s=s[:bridge_start]+bridge[:cut]+' = ('+expr+')'+s[bridge_end:]
final_start=s.index('theorem PEqualNP.Outside.L_meta_10486 :')
final_end=s.index(' := by',final_start)
s=s[:final_start]+'theorem PEqualNP.Outside.L_meta_10486 : '+statement+s[final_end:]
comment='-- Specializes the checked L_meta_9539 signed live-wire proof to this seven-vertex graph.\n-- The reference attribution below is preserved; the sample table and twelve-gate witness are regenerated.\n'
s=s.replace('\nnamespace PEqualNP.Outside.L_meta_10486.Signed','\n'+comment+'\nnamespace PEqualNP.Outside.L_meta_10486.Signed',1)
out=HERE/'formalization';out.mkdir(exist_ok=True)
(out/'positive-statement.txt').write_text(statement)
(out/'L_meta_10486.literal.lean').write_text(s)
# A computation-only exploratory module, not an official proof and never a submission file.
marker='set_option maxRecDepth 16000 in\nset_option maxHeartbeats 0 in\ntheorem reject'
compute=s[:s.index(marker)]+'\nend PEqualNP.Outside.L_meta_10486.Signed\n\n#eval PEqualNP.Outside.L_meta_10486.Signed.search 10 PEqualNP.Outside.L_meta_10486.Signed.rows\n'
(LEAN/'Pnp10486LiteralCompute.lean').write_text(compute)
(out/'adaptation.json').write_text(json.dumps({'reference':str(REF.relative_to(ROOT)),'reference_sha256':hashlib.sha256(REF.read_bytes()).hexdigest(),'literal_source_sha256':hashlib.sha256(s.encode()).hexdigest(),'positive_rows':len(positive),'negative_rows':len(zero),'separation_pairs':P,'bit_width':P*2,'binary_search_budget':10,'baseline_gates':12,'scope':'Candidate exact literal checker specialization; not yet Lean checked.'},indent=2)+'\n')
print(json.dumps({'source_bytes':len(s.encode()),'compute_bytes':len(compute.encode()),'pairs':P,'path':str(out/'L_meta_10486.literal.lean')}))
