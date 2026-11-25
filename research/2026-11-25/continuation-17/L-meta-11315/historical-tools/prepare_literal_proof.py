from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
LEAN = ROOT / 'pequalnp-proofs/lean'
REF = HERE.parent / 'L-meta-10696/status-audit/L_meta_9539.reference.lean'
source = REF.read_text()
gap = json.loads((HERE / 'gap.json').read_text())
statement = gap['statement']
baseline = json.loads((HERE / 'ownership-signed/baseline.json').read_text())
edges = [tuple(e) for e in baseline['edges']]
assert edges == [(0,3),(0,4),(1,4),(2,4),(0,5),(1,5),(3,5),(0,6),(1,6),(3,6),(5,6)]
edge_list = '[' + ', '.join(str(v) for e in edges for v in e) + ']'
old_list = '[0, 1, 0, 2, 0, 3, 0, 5, 1, 2, 1, 3, 1, 4, 2, 3, 2, 4]'
target = lambda x: any((x >> a) & 1 and (x >> b) & 1 for a,b in edges)
positive = [x for x in range(128) if target(x)]
negative = [x for x in range(128) if not target(x)]
pairs = [(p,z) for p in positive for z in negative]
P = len(pairs)
assert P == 2160
rows = []
for i in range(7):
    rows.append(sum(((p >> i) & 1) << k for k,(p,z) in enumerate(pairs)) +
                sum(((z >> i) & 1) << (k+P) for k,(p,z) in enumerate(pairs)))
expr = ' || '.join(f'(x {a} && x {b})' for a,b in edges)
s = source.replace('import Mathlib\n', 'import Mathlib.Tactic\n', 1)
s = s.replace('L_meta_9539', 'L_meta_11315').replace(old_list, edge_list)
s = re.sub(r'\b1400\b', str(2*P), s)
s = re.sub(r'\b700\b', str(P), s)
s = s.replace('Fin 6', 'Fin 7').replace('inputs.length = 6', 'inputs.length = 7')
s = re.sub(r'^def F \(x : Fin 7 → Bool\) : Bool := .*$',
           'def F (x : Fin 7 → Bool) : Bool := ' + expr, s, flags=re.M)
s = s.replace('search 7', 'search 9').replace('7 < binaryCost', '9 < binaryCost')
s = s.replace('search_complete ht 7', 'search_complete ht 9')
start = s.index('def rows : List W :=')
end = s.index('\nset_option maxRecDepth 16000 in', start)
s = s[:start] + 'def rows : List W :=\n  [' + ', '.join(hex(x) for x in rows) + ']\n' + s[end:]
gates = baseline['gates']
assert len(gates) == 11 and baseline['output'] == 17
gate_text = '[' + ', '.join('⟨PEqualNP.CircuitLowerBounds.GateOp.' + op +
                          ', [' + str(a) + ', ' + str(b) + ']⟩' for op,a,b in gates) + ']'
s = re.sub(r'^def wg : List PEqualNP.CircuitLowerBounds.Gate := .*$',
           'def wg : List PEqualNP.CircuitLowerBounds.Gate := ' + gate_text, s, flags=re.M)
s = s.replace('rcases hg with ' + ' | '.join(['rfl']*9),
              'rcases hg with ' + ' | '.join(['rfl']*11))
s = s.replace('⟨wg, 14⟩', '⟨wg, 17⟩').replace('wg.length = 9', 'wg.length = 11')
s = s.replace('L_meta_11315.wg, 14', 'L_meta_11315.wg, 17')
start = s.index('theorem bridge :')
end = s.index(' := by', start)
bridge = s[start:end]
cut = bridge.rfind(' = ((')
assert cut >= 0
s = s[:start] + bridge[:cut] + ' = (' + expr + ')' + s[end:]
start = s.index('theorem PEqualNP.Outside.L_meta_11315 :')
end = s.index(' := by', start)
s = s[:start] + 'theorem PEqualNP.Outside.L_meta_11315 : ' + statement + s[end:]
comment = ('-- Specializes the checked L_meta_9539 signed live-wire proof to this seven-vertex graph.\n'
           '-- The original attribution is retained; the sample table and eleven-gate witness are regenerated.\n')
s = s.replace('\nnamespace PEqualNP.Outside.L_meta_11315.Signed',
              '\n' + comment + '\nnamespace PEqualNP.Outside.L_meta_11315.Signed', 1)
out = HERE / 'formalization'
out.mkdir(exist_ok=True)
(out / 'L_meta_11315.literal.lean').write_text(s)
(LEAN / 'PEqualNP/Outside/L_meta_11315.lean').write_text(s)
meta = {'task': gap['id'], 'reference_sha256': hashlib.sha256(REF.read_bytes()).hexdigest(),
        'source_sha256': hashlib.sha256(s.encode()).hexdigest(), 'source_bytes': len(s.encode()),
        'positive_rows':len(positive), 'negative_rows':len(negative), 'pairs':P, 'bit_width':2*P,
        'binary_budget':9, 'witness_gates':11, 'witness_output':17,
        'scope':'Exact candidate specialization, awaiting Lean verification.'}
(out / 'adaptation.json').write_text(json.dumps(meta, indent=2) + '\n')
print(json.dumps(meta))
