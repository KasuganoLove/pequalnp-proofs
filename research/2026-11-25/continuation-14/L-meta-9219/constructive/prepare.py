#!/usr/bin/env python3
"""Recreate exact samples and deterministic erasure seeds; does not search."""
from pathlib import Path
import json
out=Path(__file__).resolve().parent
mask=7586366
pairs=[(u,v) for u in range(5) for v in range(5)]
pos=[p for p in pairs if (mask>>(5*p[0]+p[1]))&1]
neg=[p for p in pairs if not ((mask>>(5*p[0]+p[1]))&1)]
rows=pos+neg
(out/'rows.txt').write_text(f'25 {len(pos)}\n'+'\n'.join(str((1<<u)|(1<<(5+v))) for u,v in rows)+'\n')
# Correct11-gate construction independently verified by root on all25 inputs.
base11=[(1,3,4),(1,6,7),(1,0,5),(1,1,11),(1,13,8),(0,12,14),
        (1,12,13),(1,16,2),(1,10,9),(0,17,18),(1,15,19)]
# Independent13-gate row/column factoring.
base13=[(1,3,4),(1,6,7),(1,0,10),(0,12,11),(0,0,8),(1,0,1),
        (1,15,2),(0,16,9),(1,1,10),(0,18,5),(1,13,14),(1,17,19),(1,20,21)]
def evaluate(gs,out,u,v):
 w=[i==u for i in range(5)]+[j==v for j in range(5)]
 for op,a,b in gs:w.append((w[a] or w[b]) if op else (w[a] and w[b]))
 return w[out]
for gs,o in [(base11,20),(base13,22)]:
 assert all(evaluate(gs,o,u,v)==bool((mask>>(5*u+v))&1) for u,v in pairs)
def erase(gs,out,j,side):
 victim=10+j;replacement=gs[j][side+1]
 def remap(w):
  if w==victim:w=replacement
  return w-1 if w>victim else w
 return [(op,remap(a),remap(b)) for k,(op,a,b) in enumerate(gs) if k!=j],remap(out)
seeds=[erase(base11,20,j,s) for j in range(11) for s in range(2)]
front=[(base13,22)]
for depth in range(3):
 front=[erase(gs,o,j,s) for gs,o in front for j in range(len(gs)) for s in range(2)]
seeds+=front
with (out/'seeds.txt').open('w') as f:
 f.write(str(len(seeds))+'\n')
 for gs,o in seeds:
  f.write(str(o)+'\n')
  for g in gs:f.write(' '.join(map(str,g))+'\n')
(out/'problem.json').write_text(json.dumps({'task':'L-meta-9219','mask':mask,
 'rows':[''.join(str((mask>>(5*u+v))&1) for v in range(5)) for u in range(5)],
 'wire_order':'rows0..4,columns5..9','sample_order':rows,'gate_count':10,
 'seed_count':len(seeds),'scope':'Exactly25 oneEach inputs only; heuristic failure cannot prove nonexistence.'},indent=2)+'\n')
print(f'Prepared {len(seeds)} seeds; both exact baselines pass all25 rows.')
