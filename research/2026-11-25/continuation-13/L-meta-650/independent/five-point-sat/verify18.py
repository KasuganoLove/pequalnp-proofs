"""Exhaust the complete2^18 truth table using Python big-integer bit columns."""
from pathlib import Path
import json,sys
P=Path(__file__).resolve().parent
name=sys.argv[1] if len(sys.argv)>1 else 'candidate-23.json'
problem=json.loads((P/'problem.json').read_text());C=json.loads((P/name).read_text());n=C['input_count']
assert n==18
R=1<<n;ALL=(1<<R)-1
raw=[]
for i in range(n):
    step=1<<i;col=((1<<step)-1)<<step;length=2*step
    while length<R:col|=col<<length;length*=2
    raw.append(col)
w=raw[:]
for j,g in enumerate(C['gates']):
    op,a,b=g
    assert op in (0,1,2) and 0<=a<=n+j and 0<=b<=n+j
    x=w[a] if a<len(w) else 0;y=w[b] if b<len(w) else 0
    w.append(ALL if op==2 else (x|y if op else x&y))
value=w[C['output']] if C['output']<len(w) else 0
expected=0
for a,b in problem['edges']:expected|=raw[a]&raw[b]
fp=value&~expected;fn=expected&~value
first=[];err=fp|fn
while err and len(first)<12:
    low=err&-err;first.append(low.bit_length()-1);err-=low
result={'source':name,'raw_inputs':18,'gate_count':len(C['gates']),'assignments_checked':R,'false_positive_count':fp.bit_count(),'false_negative_count':fn.bit_count(),'first_error_masks':first,'all_correct':value==expected,'fits_budget23':len(C['gates'])<=23,'lean_verified':False}
(P/(Path(name).stem+'-verification.json')).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
if value!=expected:raise SystemExit(1)
