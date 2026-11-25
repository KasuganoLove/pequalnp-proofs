from pathlib import Path
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
LEAN = ROOT / 'pequalnp-proofs/lean'
base = json.loads((HERE.parent/'ownership-signed/baseline.json').read_text())
branches = json.loads((HERE/'independent-first-level.json').read_text())
pairs = [(p,n) for p in base['positive_assignments'] for n in base['negative_assignments']]
P = len(pairs)
def pack(signature):
    return sum(((signature >> p)&1)<<k for k,(p,n) in enumerate(pairs)) + sum(((signature >> n)&1)<<(k+P) for k,(p,n) in enumerate(pairs))
raw = [sum(((x>>i)&1)<<x for x in range(128)) for i in range(7)]
s = 'import Pnp11315SplitCore\n\nnamespace PEqualNP.Outside.L_meta_11315.Signed\n\n'
for i,r in enumerate(raw):
    s += f'def initial_{i} : W := {hex(pack(r))}\n'
for b in branches:
    i = b['index']
    sig = int(b['frontier_raw_signatures'][0],16)
    s += f'\ndef firstWord_{i} : W := {hex(pack(sig))}\n'
    names = [f'firstWord_{i}'] + [f'initial_{v}' for v in b['retained_raw_order']]
    s += f'def state_{i} : Nat × List W := ({b["extra"]}, [' + ', '.join(names) + '])\n'
    s += f'set_option maxRecDepth 16000 in\ntheorem state_eq_{i} : (children 3 rows).getD {i} (0, []) = state_{i} := by\n  decide +kernel\n'
s += '\nend PEqualNP.Outside.L_meta_11315.Signed\n'
(LEAN/'Pnp11315States.lean').write_text(s)
for b in branches:
    i=b['index']
    p='import Pnp11315States\n\nnamespace PEqualNP.Outside.L_meta_11315.Signed\n\n'
    p+=f'set_option maxRecDepth 16000 in\nset_option maxHeartbeats 0 in\ntheorem explicit_{i} : optimized 8 state_{i}.1 state_{i}.2 = false := by\n  decide +kernel\n\n'
    p+=f'theorem branch_{i} :\n  let q := (children 3 rows).getD {i} (0, [])\n  optimized 8 q.1 q.2 = false := by\n  dsimp only\n  rw [state_eq_{i}]\n  exact explicit_{i}\n\nend PEqualNP.Outside.L_meta_11315.Signed\n'
    (LEAN/f'Pnp11315Explicit{i}.lean').write_text(p)
print(json.dumps({'states':len(branches),'states_source_bytes':len(s.encode()),'paired_width':2*P}))
