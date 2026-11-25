"""Exact CNF for the finite twin-class deletion Rank in PR13556.

No circuit variables and no symmetry-breaking constraints are used.
Round 0 means surviving all rounds. Positive rounds delete that label.
"""
from pathlib import Path
import hashlib, itertools, json, random


def adjacency(k):
    n = 3*k
    A = [[False]*n for _ in range(n)]
    for i in range(k):
        for a in (i,k+i):
            for b in ((i+1)%k,2*k+i):
                A[a][b]=A[b][a]=True
    # Independently compare the literal public predicate.
    for a in range(n):
        for b in range(n):
            literal=any(((a==i or a==k+i) and
                         (b==(i+1)%k or b==2*k+i)) or
                        ((b==i or b==k+i) and
                         (a==(i+1)%k or a==2*k+i)) for i in range(k))
            assert A[a][b] == literal
    return A


def encode(k, rounds):
    A=adjacency(k); n=len(A); nv=2*n
    # d(v,t) states an exact round, including t=0 (surviving).
    # p(v,t) states deletion in a positive round <= t.
    def d(v,t): return 1+v*(rounds+1)+t
    off=nv*(rounds+1)
    def p(v,t):
        assert 1<=t<=rounds
        return off+v*rounds+t
    clauses=[]; counts={}
    def block(name, f):
        before=len(clauses); f(); counts[name]=len(clauses)-before
    def exact():
        for v in range(nv):
            clauses.append([d(v,t) for t in range(rounds+1)])
            for t,u in itertools.combinations(range(rounds+1),2):
                clauses.append([-d(v,t),-d(v,u)])
    block('one_exact_round',exact)
    def prefix():
        for v in range(nv):
            for t in range(1,rounds+1):
                clauses.append([-p(v,t)]+[d(v,u) for u in range(1,t+1)])
                for u in range(1,t+1): clauses.append([-d(v,u),p(v,t)])
    block('deleted_by_definition',prefix)
    def twins(side):
        for a,b in itertools.combinations(range(n),2):
            delta=[c for c in range(n) if
                   (A[a][c]!=A[b][c] if side==0 else A[c][a]!=A[c][b])]
            if not delta: continue
            av,bv=side*n+a,side*n+b
            # No label can be deleted strictly before the first round.
            clauses.append([-d(av,1),-d(bv,1)])
            for t in range(2,rounds+1):
                for c in delta:
                    clauses.append([-d(av,t),-d(bv,t),p((1-side)*n+c,t-1)])
    block('row_twins',lambda:twins(0))
    block('column_twins',lambda:twins(1))
    def final_bic():
        for a,b in itertools.combinations(range(n),2):
            common=[c for c in range(n) if A[a][c] and A[b][c]]
            delta=[c for c in range(n) if A[a][c]!=A[b][c]]
            for c in common:
                for e in delta:
                    clauses.append([p(a,rounds),p(b,rounds),
                                    p(n+c,rounds),p(n+e,rounds)])
    block('terminal_bic',final_bic)
    return A,clauses,off+nv*rounds,counts,d,p


def direct(A, schedule, rounds):
    """Independent direct replay of the exact Finset Rank recursion."""
    n=len(A); R=set(range(n)); C=set(range(n))
    if len(schedule)!=2*n or any(t<0 or t>rounds for t in schedule): return False
    for t in range(1,rounds+1):
        X={a for a in R if schedule[a]==t}
        Y={b for b in C if schedule[n+b]==t}
        if any(A[a][c]!=A[b][c] for a in X for b in X for c in C): return False
        if any(A[a][c]!=A[a][e] for c in Y for e in Y for a in R): return False
        R-=X; C-=Y
    return all(not(A[a][c] and A[b][c] and A[a][e]) or A[b][e]
               for a in R for b in R for c in C for e in C)


def assignment(schedule,rounds,d,p):
    yes=set()
    for v,t in enumerate(schedule):
        yes.add(d(v,t))
        for u in range(1,rounds+1):
            if 0<t<=u: yes.add(p(v,u))
    return yes


def sat(clauses,yes):
    return all(any((x in yes) if x>0 else (-x not in yes) for x in c) for c in clauses)


def tests():
    # Test all schedules of the smallest nondegenerate k=2 family at one round,
    # plus reproducible randomized schedules and a known valid k-round schedule.
    A,C,_,_,d,p=encode(2,1)
    checked=0
    for schedule in itertools.product(range(2),repeat=12):
        assert sat(C,assignment(schedule,1,d,p))==direct(A,schedule,1)
        checked+=1
    rng=random.Random(10083)
    for k,r in ((2,2),(3,2),(3,3),(5,4)):
        A,C,_,_,d,p=encode(k,r)
        for _ in range(100):
            schedule=[rng.randrange(r+1) for _ in range(6*k)]
            assert sat(C,assignment(schedule,r,d,p))==direct(A,schedule,r)
            checked+=1
        if r==k:
            schedule=[i+1 if i<k else 0 for i in range(3*k)]*2
            assert sat(C,assignment(schedule,r,d,p))
            assert direct(A,schedule,r)
            checked+=1
    return checked


if __name__=='__main__':
    P=Path(__file__).resolve().parent
    tested=tests()
    k=15; rounds=14
    A,C,nvars,counts,d,p=encode(k,rounds)
    path=P/'rank14.cnf'
    with path.open('w') as f:
        f.write(f'p cnf {nvars} {len(C)}\n')
        for c in C: f.write(' '.join(map(str,c))+' 0\n')
    meta={'family_k':k,'rows':3*k,'columns':3*k,'rounds':rounds,
          'variables':nvars,'clauses':len(C),'clause_blocks':counts,
          'cnf_bytes':path.stat().st_size,'cnf_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
          'independent_schedule_tests':tested,'symmetry_breaking':False,
          'semantics':'Exact Rank14 twin-class deletions followed by terminal Bic; no circuit encoding',
          'formalized_encoding':False}
    (P/'encoding.json').write_text(json.dumps(meta,indent=2)+'\n')
    print(json.dumps(meta))
