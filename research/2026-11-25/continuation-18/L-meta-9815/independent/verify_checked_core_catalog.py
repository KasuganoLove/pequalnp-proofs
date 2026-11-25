#!/usr/bin/env python3
"""Check the retained exact graph clauses against immutable, officially checked sources."""
import argparse,pathlib,json,hashlib,re,collections
p=argparse.ArgumentParser();p.add_argument('repository');args=p.parse_args();repo=pathlib.Path(args.repository);base=pathlib.Path(__file__).resolve().parent
catalog=json.loads((base/'checked-core-catalog.json').read_text());status={x['id']:x for x in json.loads((base/'checked-source-status.json').read_text())['checked']}
pat=re.compile(r'(?:\(|:)\s*∀\s+([st])\s*:\s*ℕ,\s*PEqualNP\.MetaComplexity\.HasCircuitSize\s+(\d+)\s+\(fun x : Fin \d+ → Bool =>\s*((?:\(x \d+ && x \d+\)(?:\s*\|\|\s*)?)+)\)\s+\1\s*(?:→|↔)\s*(\d+)\s*≤\s*\1')
neg=re.compile(r':\s*¬\s*\(?PEqualNP\.MetaComplexity\.HasCircuitSize\s+(\d+)\s+\(fun x : Fin \d+ → Bool =>\s*((?:\(x \d+ && x \d+\)(?:\s*\|\|\s*)?)+)\)\s+(\d+)')
cache={}
for row in catalog:
 t=row['task'];rec=status[t]
 if t not in cache:
  raw=(repo/rec['file']).read_bytes();sha=hashlib.sha256(raw).hexdigest();assert sha==rec['file_sha256']==row['sha256'],t
  s=raw.decode();s=s[s.rfind('theorem PEqualNP.Outside.'):].split(':=')[0]
  clauses=[(int(m[1]),m[2],int(m[3])) for m in pat.findall(s)]+[(int(m[0]),m[1],int(m[2])+1) for m in neg.findall(s)]
  cache[t]=[(n,[list(map(int,p)) for p in re.findall(r'\(x (\d+) && x (\d+)\)',ss)],k) for n,ss,k in clauses]
 assert (row['n'],row['edges'],row['bound']) in cache[t],t
result={'sources_verified':len(cache),'exact_clauses_verified':len(catalog),'all_pass':True,'scope':'Source byte/hash/type extraction verification only; not re-running the Lean kernel.'}
(base/'checked-core-catalog-verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
