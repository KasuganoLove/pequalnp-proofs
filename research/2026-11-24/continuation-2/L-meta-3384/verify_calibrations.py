"""Independently check the three explicit circuits in the Lean calibration."""
import json
import re
import sys
from pathlib import Path

source=Path(sys.argv[1] if len(sys.argv)>1 else Path(__file__).with_name('Pnp3384Calibration.lean'))
text=source.read_text()
circuits={}
for name,body,output in re.findall(r'def (source|modified|zeroReaders) : Circuit :=\s*⟨\[(.*?)\],(\d+)⟩',text,re.S):
    gates=[(op,[int(a),int(b)]) for op,a,b in re.findall(r'⟨\.(or|and),\[(\d+),(\d+)\]⟩',body)]
    assert len(gates)==11
    circuits[name]=(gates,int(output))
assert set(circuits)=={'source','modified','zeroReaders'}

def evaluate(circuit,inputs):
    gs,o=circuit
    w=list(inputs)
    for op,ins in gs:
        vals=[w[i] if i<len(w) else False for i in ins]
        w.append(all(vals) if op=='and' else any(vals))
    return w[o] if o<len(w) else False

edges=[(0,1),(1,2),(0,4),(1,5),(2,6),(3,5),(4,6),(3,6)]
for r in range(128):
    x=[bool(r>>i&1) for i in range(7)]
    target=any(x[a] and x[b] for a,b in edges)
    assert evaluate(circuits['source'],x)==target
    assert evaluate(circuits['zeroReaders'],x)==target
    assert evaluate(circuits['modified'],[True]+x)==(target or x[0] or x[3])
counts={name:sum(op=='or' and 2 in ins for op,ins in circuits[name][0]) for name in ('source','zeroReaders')}
assert counts=={'source':2,'zeroReaders':0}
for (op,ins),(dop,dins) in zip(circuits['source'][0],circuits['modified'][0]):
    assert op==dop
    for i,j in zip(ins,dins):
        assert j==i+1 or j==0 and i in (7,11)
print(json.dumps({'checked_inputs':128,'gate_count':11,'or_readers_of_2':counts,'replaced_wires':[7,11],'all_checks_passed':True},indent=2))
