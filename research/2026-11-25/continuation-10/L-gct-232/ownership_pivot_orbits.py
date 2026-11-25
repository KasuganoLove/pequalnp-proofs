"""Exact combinatorial S4 orbit cover for 3-pivot charts in Sym_4.
This is chart bookkeeping only, not a permanent nonexistence certificate.
"""
import itertools,json,math
from pathlib import Path
coords=list(itertools.combinations_with_replacement(range(4),2))
index={c:i for i,c in enumerate(coords)}
perms=list(itertools.permutations(range(4)))
triples=set(itertools.combinations(range(10),3))
covered=set();orbits=[]
for seed in sorted(triples):
    if seed in covered:continue
    transports={}
    for p in perms:
        image=tuple(sorted(index[tuple(sorted((p[coords[k][0]],p[coords[k][1]])))] for k in seed))
        transports.setdefault(image,list(p))
    members=set(transports)
    assert not covered & members
    covered|=members
    free=next(i for i in range(10) if i not in seed and coords[i][0]==coords[i][1])
    orbits.append({'representative':list(seed),'coordinates':[coords[i] for i in seed],
      'size':len(members),'linear_sum_elimination_coordinate':free,
      'members':[{'pivots':list(k),'permutation_from_representative':v} for k,v in sorted(transports.items())]})
assert covered==triples and len(orbits)==11
report={'coordinates':coords,'pivot_sets_total':len(triples),'permutations_total':len(perms),
 'orbit_count':len(orbits),'all_pivot_sets_covered':covered==triples,
 'orbits':orbits,'scope':'Combinatorial coverage of all 3-coordinate pivot charts under simultaneous row/column permutation. No Groebner/nonexistence result.'}
Path('ownership-pivot-orbits.json').write_text(json.dumps(report,indent=2)+'\n')
for o in orbits:print(o['representative'],o['coordinates'],'orbit size',o['size'],'eliminate',coords[o['linear_sum_elimination_coordinate']])
print('all120covered',covered==triples)
