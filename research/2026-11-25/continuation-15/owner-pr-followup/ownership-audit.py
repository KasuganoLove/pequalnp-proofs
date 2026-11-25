"""Read-only finite-data and generic-source audit of immutable PR14022."""
from pathlib import Path
import ast,difflib,hashlib,json,re

P=Path(__file__).resolve().parent
source=P/'L_meta_10221.lean'
reference=P.parent/'L-meta-9219/status-audit/upstream-L_meta_9195.lean'
b=source.read_bytes(); s=b.decode(); r=reference.read_text()
blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
assert blob=='1f0d7cf983743bb6e5f588a28908f2d0682d4389'
mask=int(re.search(r'^def MM : ℕ := (\d+)$',s,re.M).group(1))
assert mask==15768118
def int_list(name,text):
    return ast.literal_eval(re.search(r'^def '+name+r' : List ℕ := (\[[^\n]+\])$',text,re.M).group(1))
OO=int_list('OO',s); ZZ=int_list('ZZ',s)
positive=[i for i in range(25) if (mask>>i)&1]
negative=[i for i in range(25) if not((mask>>i)&1)]
assert OO==positive and ZZ==negative
assert len(set(OO))==len(OO) and len(set(ZZ))==len(ZZ)
assert not(set(OO)&set(ZZ)) and set(OO+ZZ)==set(range(25))
leafs=ast.literal_eval(re.search(r'^def lf \(i : ℕ\) : ℕ := (\[[^\n]+\])\.getD i 0$',s,re.M).group(1))
expected_leafs=[sum(1<<p for p in range(25)
                    if (p//5==i if i<5 else p%5==i-5)) for i in range(10)]
assert leafs==expected_leafs
row_witnesses=[]; column_witnesses=[]
bit=lambda u,v: bool((mask>>(5*u+v))&1)
for u in range(5):
    witness=next((up,v) for up in range(5) for v in range(5) if bit(u,v) and not bit(up,v))
    row_witnesses.append({'row':u,'other_row':witness[0],'column':witness[1]})
for v in range(5):
    witness=next((vp,u) for vp in range(5) for u in range(5) if bit(u,v) and not bit(u,vp))
    column_witnesses.append({'column':v,'other_column':witness[0],'row':witness[1]})

def canonical(text,oldname):
    text=text.replace(oldname,'L_meta_TASK')
    text=re.sub(r'^import PEqualNP\.Defs\.Represents\n','',text,flags=re.M)
    text=re.sub(r'^-- Based on the previously checked L-meta-9195 proof by tb-16\.\n','',text,flags=re.M)
    text=re.sub(r'^-- The mask and both lists of sampled points are specialized to this table\.\n','',text,flags=re.M)
    text=text.replace('15768118','MASK').replace('7387710','MASK')
    text=re.sub(r'^def OO : List ℕ := .*$', 'def OO : List ℕ := POSITIVE_LIST',text,flags=re.M)
    text=re.sub(r'^def ZZ : List ℕ := .*$', 'def ZZ : List ℕ := NEGATIVE_LIST',text,flags=re.M)
    return text.strip()

generic_equal=canonical(s,'L_meta_10221')==canonical(r,'L_meta_9195')
assert generic_equal
diff='\n'.join(difflib.unified_diff(r.replace('L_meta_9195','L_meta_TASK').splitlines(),
                                s.replace('L_meta_10221','L_meta_TASK').splitlines(),
                                fromfile='checked-L9195',tofile='PR14022-L10221',n=3))+'\n'
(P/'generic-source.diff').write_text(diff)
result={'pr':14022,'head':'bc59c2be036e28415543dcb42dd8da78d4439163',
        'source_bytes':len(b),'source_git_blob':blob,'source_sha256':hashlib.sha256(b).hexdigest(),
        'reference_source_sha256':hashlib.sha256(reference.read_bytes()).hexdigest(),
        'mask':mask,'matrix_rows':[''.join('1' if bit(u,v) else '0' for v in range(5)) for u in range(5)],
        'positive_list':OO,'negative_list':ZZ,'positive_count':len(OO),'negative_count':len(ZZ),
        'all_25_bits_partitioned_correctly':True,'all_10_leaf_signatures_correct':True,
        'row_essentiality_witnesses':row_witnesses,'column_essentiality_witnesses':column_witnesses,
        'generic_source_identical_after_explicit_specializations':generic_equal,
        'meaningful_differences':['target mask7387710 ->15768118','OO and ZZ exactly retargeted',
           'module namespace and final theorem renamed','extra allowed Defs.Represents import',
           'explicit tb-16 / L9195 attribution comments'],
        'scope':'Python data/source comparison; Lean compilation and exact-type audit recorded separately'}
(P/'independent-audit.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ('source_sha256','source_git_blob','matrix_rows','positive_count','negative_count','generic_source_identical_after_explicit_specializations')},ensure_ascii=False))
