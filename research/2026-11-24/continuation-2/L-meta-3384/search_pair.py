"""Search for a concrete counterexample to L-meta-3384.

This is a bounded, topologically ordered circuit model, not a proof.
Each gate has two distinct earlier inputs, or one input for NOT.
The final output is the last gate. SAT witnesses are checked independently.
"""
import argparse
import json
from pathlib import Path
import z3

N = 7
ROWS = 1 << N
MASK = (1 << ROWS) - 1
EDGES = [(0,1),(1,2),(0,4),(1,5),(2,6),(3,5),(4,6),(3,6)]
RAW = [sum(1 << r for r in range(ROWS) if r >> i & 1) for i in range(N)]
TARGET = 0
for u,v in EDGES:
    TARGET |= RAW[u] & RAW[v]
MODIFIED = TARGET | RAW[0] | RAW[3]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--timeout", type=int, default=60000)
    ap.add_argument("--not-gates", action="store_true")
    ap.add_argument("--out", type=Path, default=Path(__file__).with_name("counterexample.json"))
    args = ap.parse_args()
    solver = z3.Solver()
    solver.set(timeout=args.timeout)
    orig = [z3.BitVecVal(v, ROWS) for v in RAW]
    altered = list(orig)
    ops, left, right, sl, sr = [],[],[],[],[]
    pin1, pin2 = z3.BitVecs("pin1 pin2", 5)
    solver.add(z3.ULT(pin1, 17), z3.ULT(pin2, 17), z3.ULE(pin1, pin2))

    def select(index, values):
        out = values[0]
        for k,val in enumerate(values[1:], 1):
            out = z3.If(index == k, val, out)
        return out

    for j in range(11):
        op = z3.BitVec(f"op{j}", 2)
        a,b = z3.BitVecs(f"a{j} b{j}", 5)
        sa,sb = z3.Bools(f"sa{j} sb{j}")
        solver.add(z3.ULE(op, 2 if args.not_gates else 1))
        solver.add(z3.ULT(a, N+j), z3.ULT(b, N+j))
        solver.add(z3.If(op == 2, b == a, z3.ULT(a,b)))
        solver.add(z3.Implies(sa,z3.Or(a == pin1,a == pin2)))
        solver.add(z3.Implies(sb,z3.Or(b == pin1,b == pin2)))
        av,bv = select(a,orig),select(b,orig)
        aw,bw = z3.If(sa,z3.BitVecVal(MASK,ROWS),select(a,altered)),z3.If(sb,z3.BitVecVal(MASK,ROWS),select(b,altered))
        v,w = z3.BitVecs(f"v{j} w{j}", ROWS)
        solver.add(v == z3.If(op==0,av&bv,z3.If(op==1,av|bv,~av)))
        solver.add(w == z3.If(op==0,aw&bw,z3.If(op==1,aw|bw,~aw)))
        solver.add(v != 0, v != MASK)
        solver.add(*[v != earlier for earlier in orig])
        orig.append(v);altered.append(w)
        ops.append(op);left.append(a);right.append(b);sl.append(sa);sr.append(sb)
    solver.add(orig[-1] == TARGET, altered[-1] == MODIFIED)
    solver.add(z3.PbLe([(z3.And(ops[j]==1,z3.Or(left[j]==2,right[j]==2)),1) for j in range(11)],1))
    result = solver.check()
    print("solver",z3.get_version_string(),"result",result,"NOT enabled",args.not_gates,flush=True)
    if result != z3.sat:
        if result == z3.unknown:
            print("reason",solver.reason_unknown())
        return
    model=solver.model()
    gates=[];values=list(RAW);changed=list(RAW)
    for j in range(11):
        op,a,b = [model.eval(x).as_long() for x in [ops[j],left[j],right[j]]]
        sa,sb = [z3.is_true(model.eval(x)) for x in [sl[j],sr[j]]]
        ins=[a] if op==2 else [a,b]
        changed_ins=[0 if k else i+1 for i,k in zip(ins,[sa,sb])]
        vv=[values[i] for i in ins]
        ww=[MASK if k==0 else changed[k-1] for k in changed_ins]
        values.append((vv[0]&vv[1]) if op==0 else (vv[0]|vv[1]) if op==1 else MASK^vv[0])
        changed.append((ww[0]&ww[1]) if op==0 else (ww[0]|ww[1]) if op==1 else MASK^ww[0])
        gates.append({"op":["and","or","not"][op],"inputs":ins,"modified_inputs":changed_ins})
    assert values[-1]==TARGET and changed[-1]==MODIFIED
    count=sum(g["op"]=="or" and 2 in g["inputs"] for g in gates)
    assert count < 2
    record={"pin1":model.eval(pin1).as_long(),"pin2":model.eval(pin2).as_long(),"gates":gates,"output":17,"or_readers_of_2":count,"all_128_inputs_checked":True}
    args.out.write_text(json.dumps(record,indent=2)+"\n")
    print(json.dumps(record,indent=2))


if __name__ == "__main__":
    main()
