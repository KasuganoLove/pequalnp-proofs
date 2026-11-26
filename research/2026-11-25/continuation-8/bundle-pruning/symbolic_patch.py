#!/usr/bin/env python3
"""Replace finite adjacency certificates by checked arithmetic proofs."""
from pathlib import Path
import argparse, hashlib, json, re

BASE=Path(__file__).resolve().parent
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--input',type=Path,default=BASE/'optimized-L_meta_8323.lean')
p.add_argument('--proofs',type=Path,default=BASE/'Pnp4201SymbolicAdj.lean')
p.add_argument('--output',type=Path,default=BASE/'symbolic-L_meta_8323.lean')
a=p.parse_args()
s=a.input.read_text(); b=a.proofs.read_text()
assert hashlib.sha256(s.encode()).hexdigest()=='236f13567b96d4566a10ba6178b0d2080018f4dfd3f6b664c83d8ddbb02ff199'
assert hashlib.sha256(b.encode()).hexdigest()=='9d0a683e9a057b2f299480dd1e01e817a9aca1f824f2e5aedd9fca6c18ca235a'
helper='''lemma point_ne_line (p l : Fin 21) : point p ≠ line l := by
  intro h
  have hv := congrArg Fin.val h
  have hp := p.isLt
  change p.val = 21 + l.val at hv
  omega

'''
assert 'lemma point_ne_line ' not in s
for name in ['adj_point_line','not_adj_point_point','not_adj_line_line']:
    m=re.search(r'^theorem '+name+r'\b[\s\S]*?(?=\n(?:theorem|end)\b)',b,re.M)
    assert m,name
    replacement=m.group().strip().replace('theorem '+name,'lemma '+name,1)+'\n'
    pattern=r'set_option maxHeartbeats 4000000 in\nset_option maxRecDepth 16000 in\nlemma '+name+r'\b[^\n]*\n  decide \+kernel\n'
    matches=list(re.finditer(pattern,s))
    assert len(matches)==1,(name,len(matches))
    if name=='adj_point_line': replacement=helper+replacement
    start,end=matches[0].span();s=s[:start]+replacement+s[end:]
a.output.write_text(s)
report={'input_sha256':hashlib.sha256(a.input.read_bytes()).hexdigest(),
        'output_sha256':hashlib.sha256(s.encode()).hexdigest(),'output_bytes':len(s.encode()),
        'symbolic_proofs_sha256':hashlib.sha256(b.encode()).hexdigest(),
        'finite_adjacency_tables_replaced':3,'point_line_separation_helper_added':True,
        'public_theorem_statement_changed':False}
(BASE/'symbolic-patch.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report))
