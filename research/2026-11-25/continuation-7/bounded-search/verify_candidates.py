#!/usr/bin/env python3
"""Independent scalar verification of all 1024 assignments.

Does not import the seed generator and does not use packed truth-table words.
Packed NOT gates [2,a,b] become actual unary NOT gates; b is ignored.
"""
import json
from pathlib import Path

P=Path(__file__).resolve().parent

def target(x):
    return ((x[0] and x[1]) or (x[1] and x[2]) or (x[2] and x[3])
            or (x[3] and x[4]) or (x[4] and x[0]) or (x[0] and x[5])
            or (x[1] and x[6]) or (x[2] and x[7]) or (x[3] and x[8])
            or (x[4] and x[9]) or (x[5] and x[7]) or (x[7] and x[9])
            or (x[9] and x[6]) or (x[6] and x[8]) or (x[8] and x[5]))

def check(c):
    fp=[];fn=[]
    for mask in range(1024):
        x=[bool(mask>>i&1) for i in range(10)]
        wires=x+[not x[0]]
        for op,a,b in c['gates']:
            assert op in [0,1,2] and 0<=a<len(wires)
            if op==2:wires.append(not wires[a])
            else:
                assert 0<=b<len(wires)
                wires.append((wires[a] and wires[b]) if op==0 else (wires[a] or wires[b]))
        assert 0<=c['output']<len(wires)
        got=wires[c['output']];want=target(x)
        if got and not want:fp.append(mask)
        if want and not got:fn.append(mask)
    return {'size':len(c['gates']),'rows_checked':1024,'false_positive':len(fp),'false_negative':len(fn),
            'false_positive_masks':fp,'false_negative_masks':fn,'exact':not fp and not fn,
            'suffix_not_count':sum(g[0]==2 for g in c['gates']),
            'free_not_reads':sum((a==10)+(b==10 if op!=2 else 0) for op,a,b in c['gates'])+(c['output']==10)}

def main():
    bases=json.loads((P/'baselines.json').read_text())
    baseline_results=[dict(id=b['id'],**check(b)) for b in bases]
    assert len(bases)==40 and all(b['size']==20 and b['exact'] for b in baseline_results)
    best=check(json.loads((P/'best-18.json').read_text()))
    assert best['size']==18
    result={'validation':'Independent scalar Python; no Lean checker claim',
            'all_40_baselines_exact':True,'baseline_assignment_rows':40*1024,
            'baselines':baseline_results,'best18':best}
    witness=P/'witness-18.json'
    if witness.exists():
        result['witness18']=check(json.loads(witness.read_text()))
        assert result['witness18']['exact'] and result['witness18']['size']<=18
    (P/'independent-verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'all_baselines_exact':True,'baseline_rows':40960,'best18':best,
                      'has_exact_witness':bool(result.get('witness18',{}).get('exact',False))}))

if __name__=='__main__':main()
