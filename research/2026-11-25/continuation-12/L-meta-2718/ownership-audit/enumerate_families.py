"""Exact finite audit of the posted PG(2,3) negative-input predicate.

This is ordinary Python evidence, not a Lean theorem or nonexistence proof.
"""
from pathlib import Path
from collections import Counter
import json
P=Path(__file__).resolve().parent
D=[0,1,3,9];U=(1<<13)-1
L=[sum(1<<((l+d)%13) for d in D) for l in range(13)]
point_pencils=[sum(1<<l for l in range(13) if L[l]>>p&1) for p in range(13)]
records=[]
for s in range(8192):
    ls=sum(1<<l for l in range(13) if not(s&L[l]))
    covered=0
    for l in range(13):
        if ls>>l&1:covered|=L[l]
    if covered!=(U^s):continue
    deg=any(s&~lm==0 for lm in L) or any(ls&~pm==0 for pm in point_pencils)
    records.append({'point_mask':s,'line_mask':ls,'point_count':s.bit_count(),'line_count':ls.bit_count(),'degenerate':deg})
counts=Counter((r['point_count'],r['line_count'],r['degenerate']) for r in records)
record={'plane_difference_set':D,'maximal_false_count':len(records),'degenerate_count':sum(r['degenerate'] for r in records),'types':[{'point_count':a,'line_count':b,'degenerate':c,'count':v} for (a,b,c),v in sorted(counts.items())],'all_records':records}
(P/'negative-family-enumeration.json').write_text(json.dumps(record,indent=2)+'\n')
small=[U,U<<13]+[(1<<p)|((U^point_pencils[p])<<13) for p in range(13)]
degenerate={r['point_mask']|(r['line_mask']<<13) for r in records if r['degenerate']}
assert len(set(small))==15 and set(small)<=degenerate
def edge(u,v):
    if u>=13 and v<13:u,v=v,u
    return u<13<=v and bool(L[v-13]>>u&1)
assert all(any(((1<<u)|(1<<v))&~mask==0 for mask in small) for u in range(26) for v in range(26) if not edge(u,v))
small_record={'negative_masks':small,'count':15,'all_satisfy_posted_degenerate_maximal_negative_condition':True,'covers_every_nonedge_pair_including_diagonals':True,'nonedge_ordered_pairs_checked':sum(not edge(u,v) for u in range(26) for v in range(26)),'scope':'ordinary finite check; combined with the already compiled generic Pnp2343CleanCost bound this identifies a necessary dirty-AND witness, not a full2718 proof'}
(P/'fifteen-negative-cover.json').write_text(json.dumps(small_record,indent=2)+'\n')
print(json.dumps({k:v for k,v in record.items() if k!='all_records'}))
print(json.dumps(small_record))
