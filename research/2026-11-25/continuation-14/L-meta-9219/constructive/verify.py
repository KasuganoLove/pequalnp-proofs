#!/usr/bin/env python3
"""Independent literal evaluation on exactly the25 required oneEach inputs."""
from pathlib import Path
import json,sys
file=Path(sys.argv[1] if len(sys.argv)>1 else 'candidate-10.json')
c=json.loads(file.read_text())
gates=c['gates'];out=c['output'];target=7586366
assert len(gates)<=10, 'gate budget exceeded'
assert isinstance(out,int) and 0<=out<10+len(gates)
for i,(op,a,b) in enumerate(gates):
 assert op in (0,1) and 0<=a<10+i and 0<=b<10+i
rows=[];errors=[];actual=0
for u in range(5):
 for v in range(5):
  w=[i==u for i in range(5)]+[j==v for j in range(5)]
  for op,a,b in gates:w.append((w[a] or w[b]) if op else (w[a] and w[b]))
  got=w[out];expected=bool((target>>(5*u+v))&1)
  actual|=int(got)<<(5*u+v)
  r={'u':u,'v':v,'expected':expected,'actual':got}
  rows.append(r)
  if got!=expected:errors.append(r)
report={'source':file.name,'scope':'Exactly25 oneEach inputs; no condition on other assignments.','target_mask':target,'actual_mask':actual,'gate_count':len(gates),'all_25_pass':not errors,'mismatches':errors,'rows':rows}
report_path=file.with_name(file.stem+'-independent-verification.json')
report_path.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:report[k] for k in ['gate_count','all_25_pass','actual_mask','mismatches']}))
raise SystemExit(0 if not errors else 1)
