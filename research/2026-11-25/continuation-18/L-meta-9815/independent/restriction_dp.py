#!/usr/bin/env python3
"""Ordinary finite exploration of checked total-gate restriction rules; not a Lean certificate."""
import json,re,pathlib,itertools,functools,collections,time,sys
BASE=pathlib.Path(__file__).resolve().parents[1]
gap=json.loads((BASE/'gap.json').read_text())
E=tuple(tuple(map(int,p)) for p in re.findall(r'\(x (\d+) && x (\d+)\)',gap['statement']))
N=14; A=[sum(1<<v for u,v in E if u==i)+sum(1<<u for u,v in E if v==i) for i in range(N)]
def bits(S): return [i for i in range(N) if S>>i&1]
def normalize(S): return sum(1<<i for i in bits(S) if A[i]&S)
def polys(S,p,q):
 out=[]
 for a,b in itertools.product([0,1],repeat=2):
  T=set(); edges=[]; const=False
  for u,v in E:
   if not(S>>u&1 and S>>v&1):continue
   term=[]
   for w in [u,v]:
    if w==p:
     if not a:break
    elif w==q:
     if not b:break
    else:term.append(w)
   else:
    if not term:const=True
    elif len(term)==1:T.add(term[0])
    else:edges.append(tuple(term))
  out.append(('true',) if const else (tuple(sorted(T)),tuple(e for e in edges if not(T&set(e)))))
 return out
USE_CORES='--checked-cores' in sys.argv
CORES=json.loads((BASE/'independent/checked-core-catalog.json').read_text()) if USE_CORES else []
CORE_GROUPS=collections.defaultdict(list)
for row in CORES:
 k=row['key'];CORE_GROUPS[(k[0],k[1],tuple(k[2]))].append(row)
def iso_core(V,row):
 W=sorted({v for e in row['edges'] for v in e})
 B={v:{w for e in row['edges'] if v in e for w in e if w!=v} for v in W}
 S=sum(1<<v for v in V); order=sorted(V,key=lambda v:-(A[v]&S).bit_count());chosen={};used=set()
 def go(i):
  if i==len(order):return dict(chosen)
  v=order[i]
  for w in W:
   if w in used or len(B[w])!=(A[v]&S).bit_count():continue
   if any(bool(A[v]>>u&1)!=(z in B[w]) for u,z in chosen.items()):continue
   chosen[v]=w;used.add(w);r=go(i+1)
   if r is not None:return r
   del chosen[v];used.remove(w)
  return None
 return go(0)
def cover_number(S):
 match={}
 def aug(v,seen):
  for w in bits(A[v]&S):
   if w in seen:continue
   seen.add(w)
   if w not in match or aug(match[w],seen):match[w]=v;return True
  return False
 return sum(aug(v,set()) for v in range(7) if S>>v&1)
def components_and_girth(S):
 V=bits(S);components=0;seen=set();girth=99
 for root in V:
  if root not in seen:
   components+=1;stack=[root];seen.add(root)
   while stack:
    u=stack.pop()
    for v in bits(A[u]&S):
     if v not in seen:seen.add(v);stack.append(v)
  dist={root:0};parent={root:-1};queue=[root]
  for u in queue:
   for v in bits(A[u]&S):
    if v not in dist:dist[v]=dist[u]+1;parent[v]=u;queue.append(v)
    elif parent[u]!=v:girth=min(girth,dist[u]+dist[v]+1)
 return components,girth
def hubs_apart(S):
 H=[v for v in bits(S) if (A[v]&S).bit_count()>=3]
 for root in H:
  dist={root:0};q=[root]
  for u in q:
   for v in bits(A[u]&S):
    if v in dist:continue
    dist[v]=dist[u]+1;q.append(v)
  if any(w!=root and dist.get(w,99)<7 for w in H):return False
 return True
CERT={};MATCHES={}
@functools.lru_cache(None)
def lower(S):
 S0=normalize(S)
 if S0!=S:return lower(S0)
 V=bits(S)
 if not V:return 0
 edges=[(u,v) for u,v in E if S>>u&1 and S>>v&1]
 best=len(V)-1; reason=['essential_inputs',len(V)]
 comp,girth=components_and_girth(S)
 if len(edges)==len(V)-comp or (girth>=7 and hubs_apart(S)):
  exact=len(edges)+cover_number(S)-1
  if exact>best:best,reason=exact,['forest_exact' if len(edges)==len(V)-comp else 'long_thread_exact']

 key=(len(V),len(edges),tuple(sorted((A[v]&S).bit_count() for v in V)))
 for row in CORE_GROUPS.get(key,[]):
  if row['bound']<=best:continue
  mapping=iso_core(V,row)
  if mapping is not None:
   best=row['bound'];reason=['checked_core',row['task']];MATCHES[S]={'task':row['task'],'mapping':mapping,'bound':best}

 cof=[]
 for v in V:
  SF=S&~(1<<v); ST=SF&~A[v]; deg=(S&A[v]).bit_count()
  f=lower(SF); t=(deg+lower(ST)) if normalize(ST) else deg-1
  both=bool(normalize(SF))
  cof.append({'v':v,'false':f,'true':t,'false_nonconstant':both})
  for bound,why in [(f+1 if both else 0,['fixed_false',v]),(t+1,['fixed_true',v]),(min(f,t)+2 if both else 0,['two_polarity',v])]:
   if bound>best:best,reason=bound,why
 nf=all(max(collections.Counter(polys(S,p,q)).values())<3 for p,q in itertools.combinations(V,2))
 if nf and all(c['false_nonconstant'] for c in cof):
  pays=[]
  for c in cof:
   f,t=c['false'],c['true']
   pays.append(min(max(f+3,t+3),max(f+4,t+2),max(f+2,t+4)))
  r=min(pays)
  if r>best:best,reason=r,['reader_pays',pays]
 # Exact cycle theorem in checked L314. All components must be one cycle here.
 if all((A[v]&S).bit_count()==2 for v in V):
  reach=1<<V[0]
  while True:
   new=reach
   for v in bits(reach):new|=A[v]&S
   if new==reach:break
   reach=new
  if reach==S:
   cyc=len(V)+(len(V)+1)//2-1
   if cyc>best:best,reason=cyc,['cycle_exact',len(V)]
 CERT[S]={'vertices':V,'edges':edges,'bound':best,'reason':reason,'cofactors':cof,'no_funnel':nf}
 return best
start=time.monotonic();B=lower((1<<N)-1)
summary={'scope':'Ordinary computation only; no Lean or full lower-bound claim. Uses only total-gate restriction rules, not binary gate costs.','checked_cores_used':USE_CORES,'checked_core_matches':len(MATCHES),'root_bound':B,'target':25,'states':len(CERT),'seconds':time.monotonic()-start,'root':CERT[(1<<N)-1]}
(BASE/('independent/restriction-dp-checked-cores-result.json' if USE_CORES else 'independent/restriction-dp-result.json')).write_text(json.dumps(summary,indent=2)+'\n')
if USE_CORES:
 (BASE/'independent/checked-core-matches.json').write_text(json.dumps(MATCHES,indent=2)+'\n')
print(json.dumps(summary,indent=2))
