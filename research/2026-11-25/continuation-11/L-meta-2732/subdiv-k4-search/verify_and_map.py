"""Independent raw-10 truth table and, only if exact, Heawood extension."""
from pathlib import Path
import json
import re
import sys

HERE=Path(__file__).resolve().parent
problem=json.loads((HERE/'problem.json').read_text())
source=Path(sys.argv[1]);C=json.loads(source.read_text())
edges=problem['edges'];gates=C['gates']
assert C['size']==len(gates)
assert all(op in (0,1) and 0<=a<11+k and 0<=b<11+k for k,(op,a,b) in enumerate(gates))
assert 0<=C['output']<11+len(gates)
fp=fn=0;first=[]
for mask in range(1024):
    w=[bool(mask&(1<<i)) for i in range(10)]
    expected=any(w[a] and w[b] for a,b in edges)
    w.append(w[4] or w[5])
    for op,a,b in gates:w.append(w[a] and w[b] if op==0 else w[a] or w[b])
    actual=w[C['output']]
    fp+=actual and not expected;fn+=expected and not actual
    if actual!=expected and len(first)<8:first.append(mask)
result={'source':source.name,'raw_inputs_checked':1024,'suffix_size':len(gates),
        'core_size_with_free_or':len(gates)+1,'false_positive':fp,'false_negative':fn,
        'first_mismatches':first,'correct':fp==fn==0,'within_14_suffix':len(gates)<=14}
if result['correct']:
    mapping=problem['heawood_map']
    full=[[1,mapping[4],mapping[5]]]
    def wire(v):return mapping[v] if v<10 else v+4
    for op,a,b in gates:full.append([op,wire(a),wire(b)])
    out=wire(C['output'])
    def add(op,a,b):
        full.append([op,min(a,b),max(a,b)])
        return 13+len(full)
    t=add(1,14,9);t=add(0,1,t);out=add(1,out,t)
    for center,neighbors in [(5,[9,10,12]),(6,[8,9,11])]:
        term=add(1,neighbors[0],neighbors[1]);term=add(1,term,neighbors[2])
        term=add(0,center,term);out=add(1,out,term)
    assert len(full)==len(gates)+12 and all(a<14+k and b<14+k for k,(_,a,b) in enumerate(full))
    target=[tuple(map(int,e)) for e in re.findall(r'\(\((\d+) : ℕ\), \((\d+) : ℕ\)\)',
                                               (HERE.parent/'statement.txt').read_text())]
    assert len(target)==21
    mismatches=[]
    for mask in range(16384):
        w=[bool(mask&(1<<i)) for i in range(14)]
        expected=any(w[a] and w[b] for a,b in target)
        for op,a,b in full:w.append(w[a] and w[b] if op==0 else w[a] or w[b])
        if w[out]!=expected:mismatches.append(mask)
    result['heawood']={'size':len(full),'inputs_checked':16384,'mismatches':len(mismatches),'correct':not mismatches}
    if not mismatches:
        name=f'heawood-{len(full)}.json'
        (HERE/name).write_text(json.dumps({'size':len(full),'output':out,'gates':full},indent=2)+'\n')
print(json.dumps(result,indent=2))
