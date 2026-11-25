from pathlib import Path
import hashlib, json

ROOT = Path(__file__).resolve().parents[4]
REPO = ROOT / 'pequalnp-proofs'
src = REPO / 'lean/PEqualNP/Outside/L_meta_12030.lean'
raw = src.read_bytes()
assert hashlib.sha256(raw).hexdigest() == '052c0e4396cdacee1909ddbf8b6e39d859bb960676599515c5ad60b9a202d11b'
s = raw.decode().replace('L_meta_12030', 'L_meta_12030_split')
old = '''set_option maxRecDepth 100000 in
theorem searchS_false : (List.range 7).all (fun s => !searchS s) = true := by
  decide +kernel
'''
assert s.count(old) == 1
parts = ['''def searchBlock (s m0 : ℕ) : Bool :=
  (List.range (m0 + 1)).any fun m1 =>
    (List.range (m1 + 1)).any fun m2 => (List.range (m2 + 1)).any fun m3 =>
      search s (mk m0 m1 m2 m3)
''']
for gate_budget in range(7):
    for count in range(gate_budget + 2):
        parts.append(f'''set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem searchBlock_false_{gate_budget}_{count} : searchBlock {gate_budget} {count} = false := by
  decide +kernel
''')
    values = ', '.join(map(str, range(gate_budget + 2)))
    cases = ', '.join(f'searchBlock_false_{gate_budget}_{j}' for j in range(gate_budget + 2))
    parts.append(f'''theorem searchS_false_{gate_budget} : searchS {gate_budget} = false := by
  change ([{values}] : List ℕ).any (searchBlock {gate_budget}) = false
  simp only [List.any_cons, List.any_nil, {cases}, Bool.false_or]
''')
parts.append('''theorem searchS_false : (List.range 7).all (fun s => !searchS s) = true := by
  change ([0, 1, 2, 3, 4, 5, 6] : List ℕ).all (fun s => !searchS s) = true
  simp only [List.all_cons, List.all_nil, searchS_false_0, searchS_false_1,
    searchS_false_2, searchS_false_3, searchS_false_4, searchS_false_5,
    searchS_false_6, Bool.not_false, Bool.true_and]
''')
s = s.replace(old, '\n'.join(parts))
dest = REPO / 'lean/PEqualNP/Outside/L_meta_12030_split.lean'
assert not dest.exists()
dest.write_text(s)
print(json.dumps({'file':str(dest),'bytes':len(s.encode()),'sha256':hashlib.sha256(s.encode()).hexdigest(),'blocks':35}))
