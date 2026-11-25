#!/usr/bin/env python3
"""Read-only source/data checks; this is not a replacement for Lean checking."""
from pathlib import Path
import re,json,hashlib
base=Path(__file__).resolve().parent
candidate=base.parent/'L_meta_9269.lean'
original=base.parent.parent/'L-meta-9219/status-audit/upstream-L_meta_9195.lean'
a=original.read_text();b=candidate.read_text()
def val(s,n):
 return re.search(r'^def '+n+r'\s*:[^\n]*:=\s*([^\n]+)',s,re.M).group(1).strip()
def canon(s):
 s=s.replace('L_meta_9195','L_meta_REVIEW').replace('L_meta_9269','L_meta_REVIEW')
 s=s.replace('7387710','MASK_REVIEW').replace('16223860','MASK_REVIEW')
 for n in ['OO','ZZ']:s=re.sub(r'(^def '+n+r'\s*:[^\n]*:=)[^\n]+',r'\1 LIST_REVIEW',s,flags=re.M)
 s='\n'.join(l for l in s.splitlines() if not l.startswith('-- Adapted from the checked L-meta-9195 proof') and not l.startswith('-- The argument is unchanged;'))
 return '\n'.join(l for l in s.splitlines() if l.strip())
mm=int(val(b,'MM'));oo=json.loads(val(b,'OO'));zz=json.loads(val(b,'ZZ'))
assert mm==16223860
expected_oo=[p for p in range(25) if (mm>>p)&1]
expected_zz=[p for p in range(25) if not ((mm>>p)&1)]
assert oo==expected_oo and zz==expected_zz
assert len(set(oo+zz))==25 and len(oo)<=16 and len(zz)<=16
assert canon(a)==canon(b), 'Unexpected change outside namespace, mask, lists and attribution'
lf=[31,992,31744,1015808,32505856,1082401,2164802,4329604,8659208,17318416]
lf_actual=[sum((1<<(5*u+v)) for u in range(5) for v in range(5) if (i==u if i<5 else i==5+v)) for i in range(10)]
assert lf==lf_actual
A=[[(mm>>(5*u+v))&1 for v in range(5)] for u in range(5)]
row=[{'input':u,'positive':next([u,v] for v in range(5) for t in range(5) if A[u][v] and not A[t][v]),'negative':next([t,v] for v in range(5) for t in range(5) if A[u][v] and not A[t][v])} for u in range(5)]
col=[{'input':5+v,'positive':next([u,v] for u in range(5) for t in range(5) if A[u][v] and not A[u][t]),'negative':next([u,t] for u in range(5) for t in range(5) if A[u][v] and not A[u][t])} for v in range(5)]
for x in row+col:
 u,v=x['positive'];r,s=x['negative'];assert A[u][v] and not A[r][s]
report={'source_sha256':hashlib.sha256(b.encode()).hexdigest(),'upstream_source_sha256':hashlib.sha256(a.encode()).hexdigest(),'normalized_proof_body_identical':True,'changes':'namespace, MM/mask literal, OO, ZZ, attribution only','MM':mm,'OO':oo,'ZZ':zz,'all25_partition':True,'lf_matches_exact_oneEach_bit_order':True,'all10_necessary_input_witnesses':row+col,'rows':[''.join(map(str,r)) for r in A],'positive_count':len(oo),'negative_count':len(zz),'new_lean_runs':0,'official_acceptance_claim':False}
(base/'source-data-review.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:report[k] for k in ['source_sha256','normalized_proof_body_identical','all25_partition','lf_matches_exact_oneEach_bit_order','positive_count','negative_count']}))
