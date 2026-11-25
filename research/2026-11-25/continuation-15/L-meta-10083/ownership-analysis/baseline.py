"""Reproduce the 7k-1 gate control; it exceeds the k15 task cap by one."""
from pathlib import Path
import json


def build(k):
    n=3*k; gates=[]
    def add(op,a,b):
        out=2*n+len(gates)
        assert a<out and b<out
        gates.append([op,a,b])
        return out
    z=[add('or',v,n+v) for v in range(n)]
    terms=[]
    for i in range(k):
        L=add('or',z[i],z[k+i])
        R=add('or',z[(i+1)%k],z[2*k+i])
        terms.append(add('and',L,R))
    out=terms[0]
    for t in terms[1:]: out=add('or',out,t)
    assert len(gates)==7*k-1
    return gates,out


if __name__=='__main__':
    k=15; n=3*k
    gates,out=build(k)
    positive=0
    for a in range(n):
        for b in range(n):
            target=any(((a==i or a==k+i) and
                        (b==(i+1)%k or b==2*k+i)) or
                       ((b==i or b==k+i) and
                        (a==(i+1)%k or a==2*k+i)) for i in range(k))
            w=[v==a for v in range(n)]+[v==b for v in range(n)]
            for op,u,v in gates: w.append((w[u] and w[v]) if op=='and' else (w[u] or w[v]))
            assert w[out]==target
            positive+=target
    result={'k':k,'raw_inputs':2*n,'gate_count':len(gates),'output':out,
            'checked_oneEach_inputs':n*n,'positive_entries':positive,'mismatches':0,
            'task_gate_cap':103,'within_task_cap':False,
            'scope':'Ordinary-computation control circuit, not a103-gate witness or Lean proof',
            'gates':gates}
    path=Path(__file__).resolve().parent/'baseline104.json'
    path.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({p:v for p,v in result.items() if p!='gates'}))
