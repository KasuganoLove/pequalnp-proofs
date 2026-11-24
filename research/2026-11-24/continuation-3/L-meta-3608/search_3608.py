#!/usr/bin/env python3
"""Exact bounded-index model for L-meta-3608; solver output is not a Lean proof.
Requires z3-solver. Run with --timeout-ms N --output result.json.
Indices 0..23; future references evaluate false, as in Circuit.wires.
"""
import argparse, json, time
from pathlib import Path
import z3

EDGES = [3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320]

def independent_check(gates):
    reads = [v for op, ins in gates for v in ins]
    multi = {v for v in range(23) if reads.count(v) >= 2}
    ns = [i for i, (op, _) in enumerate(gates) if op == "not"]
    assert len(gates) == 14 and len(ns) == 2 and 3 <= ns[0] <= 6 and ns[1] < 13
    assert all(len(ins) <= (1 if op == "not" else 2) for op, ins in gates)
    assert all(v in reads for v in range(23)) and len(multi) <= 3
    for op, ins in gates:
        if op != "not" and len(ins) == 2 and ins[0] < 9 and ins[1] < 9 and ins[0] != ins[1]:
            assert ins[0] in multi or ins[1] in multi
    for r in range(512):
        w = [bool(r & (1 << i)) for i in range(9)]
        w.append(w[0] or w[2])
        for op, ins in gates:
            vals = [w[v] if v < len(w) else False for v in ins]
            w.append(all(vals) if op == "and" else any(vals) if op == "or" else not (vals[0] if vals else False))
        assert w[23] == any(r & e == e for e in EDGES)
    return {"all_512_assignments": True, "multi_read_wires": sorted(multi), "not_positions": ns}

def main():
    ap=argparse.ArgumentParser(); ap.add_argument("--timeout-ms", type=int, default=90000)
    ap.add_argument("--output", default="search-result.json"); ap.add_argument("--sample-mode", choices=["all", "frontier"], default="all"); args=ap.parse_args()
    samples=list(range(512)) if args.sample_mode=="all" else sorted(set([0,511]+[1<<i for i in range(9)]+EDGES+[r for r in range(512) if not any(r&e==e for e in EDGES) and all(any(((r|(1<<i))&e)==e for e in EDGES) for i in range(9) if not r&(1<<i))]))
    width=len(samples)
    t=time.time(); s=z3.Solver(); s.set(timeout=args.timeout_ms)
    ops=[z3.BitVec(f"op_{i}",2) for i in range(14)]
    ar=[z3.BitVec(f"arity_{i}",2) for i in range(14)]
    aa=[z3.BitVec(f"a_{i}",5) for i in range(14)]
    bb=[z3.BitVec(f"b_{i}",5) for i in range(14)]
    active=[]
    for i in range(14):
        s.add(z3.ULE(ops[i],2), z3.ULE(ar[i],2), z3.ULE(aa[i],23), z3.ULE(bb[i],23))
        s.add(z3.Implies(ops[i]==2,z3.ULE(ar[i],1)))
        s.add(z3.Implies(ar[i]==0,aa[i]==0),z3.Implies(z3.ULT(ar[i],2),bb[i]==0))
        s.add(z3.Implies(z3.And(ar[i]==2,ops[i]!=2),z3.ULE(aa[i],bb[i])))
        active.append([(z3.UGE(ar[i],1),aa[i]),(ar[i]==2,bb[i])])
    nots=[op==2 for op in ops]
    s.add(z3.PbEq([(p,1) for p in nots],2))
    s.add(z3.Or(*nots[3:7]),*[z3.Not(nots[i]) for i in [0,1,2,13]])
    multi=[]
    for v in range(23):
        reads=[z3.And(on,ix==v) for gate in active for on,ix in gate]
        s.add(z3.Or(*reads)); multi.append(z3.AtLeast(*reads,2))
    s.add(z3.AtMost(*multi,3))
    for i in range(14):
        ma=z3.Or(*[z3.And(aa[i]==v,multi[v]) for v in range(9)])
        mb=z3.Or(*[z3.And(bb[i]==v,multi[v]) for v in range(9)])
        s.add(z3.Implies(z3.And(ops[i]!=2,ar[i]==2,z3.ULT(aa[i],9),z3.ULT(bb[i],9),aa[i]!=bb[i]),z3.Or(ma,mb)))
    mask=(1<<width)-1
    w=[z3.BitVecVal(sum((bool(r&(1<<i)))<<j for j,r in enumerate(samples)),width) for i in range(9)]
    w.append(w[0]|w[2])
    def select(ix):
        result=z3.BitVecVal(0,width)
        for j,val in enumerate(w): result=z3.If(ix==j,val,result)
        return result
    for i in range(14):
        a,b=select(aa[i]),select(bb[i]); v=z3.BitVec(f"wire_{10+i}",width)
        av=z3.If(ar[i]==0,z3.BitVecVal(mask,width),z3.If(ar[i]==1,a,a&b))
        ov=z3.If(ar[i]==0,z3.BitVecVal(0,width),z3.If(ar[i]==1,a,a|b))
        nv=z3.If(ar[i]==0,z3.BitVecVal(mask,width),~a)
        s.add(v==z3.If(ops[i]==0,av,z3.If(ops[i]==1,ov,nv)));w.append(v)
    target=sum(any(r&e==e for e in EDGES)<<j for j,r in enumerate(samples))
    s.add(w[23]==target)
    build=time.time()-t; verdict=s.check(); elapsed=time.time()-t
    result={"task":"L-meta-3608","z3_version":z3.get_version_string(),"scope":"all 14-gate circuits over operand indices 0..23 satisfying the posted structural hypotheses; binary operand order canonicalized","sample_mode": args.sample_mode, "sample_count":width, "samples": samples if args.sample_mode!="all" else "all 0..511", "status":str(verdict),"timeout_ms":args.timeout_ms,"build_seconds":build,"elapsed_seconds":elapsed,"formal_status":"not a Lean certificate"}
    if verdict==z3.unknown: result["reason_unknown"]=s.reason_unknown()
    elif verdict==z3.sat:
        m=s.model(); gates=[]
        for i in range(14):
            op=["and","or","not"][m.eval(ops[i]).as_long()]; n=m.eval(ar[i]).as_long()
            gates.append((op,[m.eval(aa[i]).as_long(),m.eval(bb[i]).as_long()][:n]))
        result["gates"]=gates
        try: result["independent_validation"]=independent_check(gates)
        except AssertionError: result["independent_validation"]={"all_512_assignments": False, "note": "sample-consistent circuit only; not a counterexample"}
    Path(args.output).write_text(json.dumps(result,indent=2)+"\n");print(json.dumps(result,indent=2))
if __name__=="__main__":main()
