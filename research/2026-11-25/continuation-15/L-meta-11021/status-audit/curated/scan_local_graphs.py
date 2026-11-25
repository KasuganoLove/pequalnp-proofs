#!/usr/bin/env python3
"""Read-only literal-graph isomorphism scan; no external Python dependencies."""
from pathlib import Path
import re, json, hashlib, subprocess, itertools, argparse
base = Path(__file__).resolve().parent
ap = argparse.ArgumentParser()
ap.add_argument("--repo", type=Path, default=base.parents[3] / "pequalnp-proofs")
ap.add_argument("--desk", type=Path, default=base / "temporary-desk.json")
args = ap.parse_args()
repo = args.repo.resolve()
target = [(0,4),(0,5),(1,5),(2,6),(3,6),(0,7),(2,7),(4,7),(1,8),(3,8),(4,8),(6,8)]
def adj(edges):
    a = [set() for _ in range(9)]
    for u,v in edges:
        a[u].add(v); a[v].add(u)
    return a
def triangles(a):
    return [(i,j,k) for i,j,k in itertools.combinations(range(9),3) if j in a[i] and k in a[i] and k in a[j]]
def iso(edges):
    a,b = adj(target),adj(edges)
    ta,tb = triangles(a),triangles(b)
    sig = lambda x,t,v:(len(x[v]),sum(v in c for c in t))
    domains={u:[v for v in range(9) if sig(a,ta,u)==sig(b,tb,v)] for u in range(9)}
    if any(not v for v in domains.values()): return None
    order=sorted(range(9),key=lambda u:(len(domains[u]),-len(a[u])))
    m={}
    def walk(k):
        if k==9:return dict(m)
        u=order[k]
        for v in domains[u]:
            if v in m.values():continue
            if any(((w in a[u]) != (z in b[v])) for w,z in m.items()):continue
            m[u]=v
            r=walk(k+1)
            if r is not None:return r
            del m[u]
        return None
    return walk(0)
files=subprocess.run(["rg","--files",str(repo/"lean/PEqualNP/Outside"),"-g","L_meta_*.lean"],capture_output=True,text=True,check=True).stdout.splitlines()
hits=[];count=0;candidates=0
for name in files:
    p=Path(name);txt=p.read_text();pos=txt.rfind("theorem PEqualNP.Outside."+p.stem)
    if pos<0:continue
    ty=txt[pos:].split(":= by",1)[0]
    if not ("Fin 9" in ty or "Fin (9" in ty or "HasCircuitSize 9" in ty):continue
    count+=1
    norm=re.sub(r"\((\d+)\s*:\s*Fin\s*(?:\(\d+\s*:\s*ℕ\)|\d+)\)",r"\1",ty)
    es={}
    for m in re.finditer(r"\b([A-Za-z_]\w*)\s+\(?(\d+)\)?\s*&&\s*\1\s+\(?(\d+)\)?",norm):
        es.setdefault(m[1],set()).add(tuple(sorted((int(m[2]),int(m[3])))))
    for var,edges in es.items():
        if len(edges)!=12 or any(max(e)>=9 for e in edges):continue
        if sorted(map(len,adj(edges)))!=sorted(map(len,adj(target))):continue
        candidates+=1;mapping=iso(edges)
        if mapping is not None:
            hits.append({"file":str(p.relative_to(repo)),"sha256":hashlib.sha256(txt.encode()).hexdigest(),"input_variable":var,"isomorphism_target_to_source":mapping,"statement_prefix":ty[:1500]})
desk=json.loads(args.desk.read_text())
table_hits=[]
for row in desk["gaps"]:
    title=row.get("title","")
    if "9 vertices, edges " not in title:continue
    section=title.split("9 vertices, edges ",1)[1].split(":",1)[0]
    edges=[tuple(map(int,m)) for m in re.findall(r"(\d+)-(\d+)",section)]
    if len(edges)==12 and max(max(e) for e in edges)<9:
        mapping=iso(edges)
        if mapping is not None:table_hits.append({"id":row["id"],"title":title,"pr_numbers":row.get("pr_numbers"),"map":mapping})
report={"scope":"Heuristic literal-edge extraction from final public declarations in pinned checkout; does not cover helper-defined graphs or newer files. Public-table comparison covers only titles with explicit9-vertex edges.","target_edges":target,"degree_multiset":sorted(map(len,adj(target))),"triangles":triangles(adj(target)),"local_public_statements_with9_inputs_scanned":count,"matching_degree_literal_targets":candidates,"isomorphic_local_hits":hits,"isomorphic_public_table_hits":table_hits}
(base/"local-isomorphism-audit.json").write_text(json.dumps(report,indent=2)+"\n")
print(json.dumps(report,indent=2))
