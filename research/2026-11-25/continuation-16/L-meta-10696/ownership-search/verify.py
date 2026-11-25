from pathlib import Path
import json
P=Path(__file__).resolve().parent
E=[(0,2),(1,3),(0,4),(2,4),(0,5),(2,5),(4,5),(0,6),(1,6),(2,6),(3,6),(4,6)]
def test(gates,output):
    fp=[];fn=[]
    for x in range(128):
        w=[bool((x>>i)&1) for i in range(7)]
        for op,a,b in gates:
            assert op in ('and','or') and 0<=a<len(w) and 0<=b<len(w)
            w.append(w[a] and w[b] if op=='and' else w[a] or w[b])
        actual=w[output]; desired=any(w[a] and w[b] for a,b in E)
        if actual and not desired:fp.append(x)
        if desired and not actual:fn.append(x)
    return {'checked_inputs':128,'false_positives':fp,'false_negatives':fn,'is_correct':not fp and not fn}
best=json.loads((P/'search-result.json').read_text())
validation=test(best['gates'],best['output'])
assert 8*len(validation['false_positives'])+len(validation['false_negatives'])==best['best_weighted_score']
base=[['or',0,2],['and',0,2],['and',4,7],['or',8,9],['or',7,4],['or',5,6],['and',11,12],['or',10,13],['or',1,3],['and',1,3],['and',6,15],['or',16,17],['or',14,18]]
control=test(base,19);assert control['is_correct']
result={'candidate_gate_count':12,'candidate':validation,'control_gate_count':13,'control':control,
        'scope':'Ordinary exhaustive evaluation of the returned12-gate heuristic candidate and13-gate control; no lower-bound certificate'}
(P/'validation.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
