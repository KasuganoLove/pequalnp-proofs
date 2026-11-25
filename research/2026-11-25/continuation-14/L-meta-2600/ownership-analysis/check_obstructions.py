"""Small exact controls for scope mistakes; not a lower-bound proof for L2600."""
from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent
# Four raw inputs a,b,c,d; graph edges ab and cd.
# H=c(a OR d), J=d(b OR c), F=(a OR H)(b OR J).
gates=[(1,0,3),(0,2,4),(1,1,2),(0,3,6),(1,0,5),(1,1,7),(0,8,9)]
edges={(0,1),(2,3)}
table=[]
for mask in range(16):
    w=[bool(mask>>i&1) for i in range(4)]
    for op,a,b in gates:w.append((w[a] or w[b]) if op else (w[a] and w[b]))
    expected=any(w[a] and w[b] for a,b in edges)
    assert w[-1]==expected
    table.append((w,expected))
below=[all(not w[4+j] or f for w,f in table) for j in range(7)]
tops={j for j,g in enumerate(gates) if g[0]==0 and below[j]}
junk={j for j,g in enumerate(gates) if g[0]==0 and not below[j]}
raw=[{i} for i in range(4)];cone=[set() for i in range(4)]
for j,(op,a,b) in enumerate(gates):
    raw.append(raw[a]|raw[b] if op else set())
    cone.append(cone[a]|cone[b]|{j})
centreless={j for j in tops if not raw[gates[j][1]] or not raw[gates[j][2]]}
topform=all(i not in cone[a]|cone[b] for i in tops for j,(op,a,b) in enumerate(gates) if op==0)
star=set()
for j in tops:
    _,a,b=gates[j]
    for x in raw[a]:
        for y in raw[b]:star.add(tuple(sorted((x,y))))
trace=all(any(table[(1<<a)|(1<<b)][0][4+j] for j in tops) for a,b in edges)
assert tops=={6} and junk=={1,3} and not centreless and topform and trace
assert star=={(0,1)}
model={'scope':'Ordinary exhaustive check of a nonminimum counterexample to raw-guard inference, not a counterexample to L-meta-2600','inputs':4,'gates':gates,'output':10,'graph_edges':sorted(edges),'all_assignments_checked':16,'computes_exact_graph_function':True,'tops':sorted(tops),'junk':sorted(junk),'centreless':sorted(centreless),'topform':topform,'positive_edge_to_top_trace':trace,'top_raw_sides':[sorted(raw[8]),sorted(raw[9])],'star_edges':sorted(star),'uncovered_edges':sorted(edges-star),'raw_guards_fail_on_edge':[2,3],'circuit_gates':7,'known_standard_matching_gates':3,'leastness':False,'lean_verified':False}
(P/'raw-guard-control.json').write_text(json.dumps(model,indent=2)+'\n')
# Exact L2600 labels: point p is incident to line l iff p-l belongs to D.
D={0,1,3,9};E={(p,13+l) for p in range(13) for l in range(13) if (p-l)%13 in D}
U={e for e in E if e[0]==0}|{(1,13)}
covered=E-U
assert len(E)==52 and len(U)==5 and len(covered)==47
sizes=[sum(a==p for a,b in covered) for p in range(1,13)]
assert sorted(sizes)==[3]+[4]*11
prep=sum(k-1 for k in sizes);partial=prep+12+11
t,c,j,o,u,s=12,0,2,2,5,62;e=2*c+j+o
assert 52+t+e<=s+u+1 and 52<=4*t+u and 4*e+8<=5*u
assert prep==35 and partial==58
pending={'scope':'Geometric and numerical residual only; no completion circuit is asserted','t':t,'c':c,'j':j,'o':o,'u':u,'hypothetical_size':s,'e':e,'ledger_left':52+t+e,'ledger_right':s+u+1,'cover_bound_left':52,'cover_bound_right':4*t+u,'strengthened_left':4*e+8,'strengthened_right':5*u,'star_centres':list(range(1,13)),'uncovered_edges':sorted(U),'covered_edge_count':47,'partial_star_gate_count':partial,'partial_preparation_ORs':prep,'remaining_hypothetical_gate_slots':s-partial,'semantic_completion_established':False,'lean_verified':False}
(P/'pending-case.json').write_text(json.dumps(pending,indent=2)+'\n')
print(json.dumps({'matching_control_correct_on':16,'centreless':0,'raw_guard_inference_fails':True,'pending_counts':[t,c,j,o,u],'semantic_completion_established':False}))
