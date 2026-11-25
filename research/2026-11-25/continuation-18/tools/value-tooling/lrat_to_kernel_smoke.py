#!/usr/bin/env python3
"""Small, auditable LRAT/RUP -> Lean Checker smoke-test emitter.
For real circuit certificates use upstream genrow.py's trimming and segmentation.
This follows the public Checker.lean literal/token format; no solver result is trusted
by the generated theorem. The kernel must accept the supplied trace for the exact F.
"""
import argparse,pathlib,json,hashlib
ap=argparse.ArgumentParser();ap.add_argument('cnf');ap.add_argument('lrat');ap.add_argument('lean');ap.add_argument('--namespace',default='PnpValueLratSanity');args=ap.parse_args()
cnf=pathlib.Path(args.cnf);proof=pathlib.Path(args.lrat);out=pathlib.Path(args.lean)
# DIMACS allows clauses to span lines. Preserve their exact order.
raw=[];nv=None;nc=None
for line in cnf.read_text().splitlines():
 t=line.split()
 if not t or t[0]=='c':continue
 if t[0]=='p':assert t[1]=='cnf';nv,nc=map(int,t[2:]);continue
 raw.extend(map(int,t))
clauses=[];cur=[]
for lit in raw:
 if lit==0:clauses.append(cur);cur=[]
 else:assert nv is not None and abs(lit)<=nv;cur.append(lit)
assert not cur and len(clauses)==nc
enc=lambda l:2*abs(l)+(l<0)
F=[[enc(l) for l in c] for c in clauses]
db={i+1:c for i,c in enumerate(F)};tokens=[];steps=0;hintcount=0;empty=False
for lineno,line in enumerate(proof.read_text().splitlines(),1):
 t=line.split()
 if not t or t[0]=='c':continue
 assert len(t)>1,(lineno,'short LRAT line')
 if t[1]=='d':continue # Retaining already proved clauses preserves soundness.
 ident=int(t[0]);assert ident not in db and ident>nc
 sep=t.index('0',1);lits=[enc(int(x)) for x in t[1:sep]]
 assert t[-1]=='0';hints=list(map(int,t[sep+1:-1]));assert all(h>0 for h in hints),'RAT hints unsupported'
 false=set(lits);ht=[];conflict=False
 for h in hints:
  assert h in db,(lineno,'missing hint',h)
  remaining=set(db[h])-false
  if not remaining:ht.append(h-1);conflict=True;hintcount+=1;break
  assert len(remaining)==1,(lineno,'nonunit RUP hint',h,remaining)
  u=next(iter(remaining));ht.extend([h-1,u]);false.add(u^1);hintcount+=1
 assert conflict,(lineno,'no contradiction')
 tokens.extend([ident-1]+lits+[0]+ht);db[ident]=lits;steps+=1
 if not lits:empty=True;break
assert empty,'no final empty clause'
fk=list(range(1,len(F)+1));width=max([1]+tokens+fk+[l for c in F for l in c]).bit_length();perword=1024//width
assert perword>0
words=[]
for j in range(0,len(tokens),perword):
 w=1
 for t in reversed(tokens[j:j+perword]):w=(w<<width)|t
 words.append(w)
L=lambda x:'['+','.join(map(str,x))+']'
formula='['+','.join(L(c) for c in F)+']'
source=f'''import PEqualNP.Library.LRAT.Checker

-- Self-chosen contradictory CNF sanity sample; not a project task submission.
-- Token layout follows upstream Checker.lean (Apache-2.0).
namespace {args.namespace}
open PEqualNP.Library.LRAT

def F : List (List Nat) := {formula}
def keys : List Nat := {L(fk)}
def tokens : List Nat := {L(tokens)}
def words : List Nat := {L(words)}

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem token_unsat : ¬ FormulaSat F :=
  check_sound F keys tokens (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem packed_unsat : ¬ FormulaSat F :=
  checkW_sound F keys {width} words (by decide +kernel)

end {args.namespace}
#print axioms {args.namespace}.token_unsat
#print axioms {args.namespace}.packed_unsat
'''
out.write_text(source)
meta={'cnf_sha256':hashlib.sha256(cnf.read_bytes()).hexdigest(),'lrat_sha256':hashlib.sha256(proof.read_bytes()).hexdigest(),'lean_sha256':hashlib.sha256(out.read_bytes()).hexdigest(),'clauses':len(F),'steps':steps,'hints':hintcount,'field_width':width,'tokens':tokens,'words':words,'scope':'Emitted only; Lean acceptance must be checked separately.'}
out.with_suffix('.packing.json').write_text(json.dumps(meta,indent=2)+'\n');print(json.dumps(meta))
