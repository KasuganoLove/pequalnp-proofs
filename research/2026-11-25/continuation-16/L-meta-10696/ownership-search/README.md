# L-meta-10696: structural route and bounded monotone search

No complete replacement theorem, shorter one-NOT counterexample, or new Lean
certificate was obtained here. Root owns the task lease and its closure.

## Exact graph and available monotone upper bound

The12 edges are02,13,04,24,05,25,45,06,16,26,36,46. The graph is K5 minus
edge56 on{0,2,4,5,6}, together with triangle{1,3,6}. Vertices0,2,4 are true
twins forming a clique. Its complement is K2,4 on{1,3} x {0,2,4,5}, plus
edge56. Merging true twins by OR alone is invalid because it loses their
internal clique edges.

Let S=x0 OR x2 OR x4 and let T be the at-least-two function on these three
variables. The target is

    T OR (S AND (x5 OR x6)) OR (x1 AND x3)
      OR (x6 AND (x1 OR x3)).

The verified13-gate implementation computes the first two terms in8 gates,
the triangle on{1,3,6} in4 gates, then ORs their outputs. The explicit control
inside verify.py passes all128 input assignments. This is an upper bound,
not a proof that13 gates are necessary.

Deleting a true twin leaves an8-edge graph on6 vertices, with the analogous
10-gate monotone construction. Repeating leaves a7-gate construction on5
vertices. A proposed inductive lower bound would need a **proved3-gate
saving** under a suitable restriction; ordinary constant propagation does
not supply that just from the graph's true twins. No such lemma was found
or proved during this bounded investigation.

## Checked-source reuse and computational scale

The local L1425/L1427/L1439/L1443/L1445/L1447 results are fixed five-variable
truth-table batches, not an unrestricted one-NOT elimination theorem.
The remote-status agent found newer checked six-vertex replacement proofs;
their graphs have9 or10 edges and are not isomorphic to the8-edge minor.

L-meta-9539 has a useful generic signed live-wire compiler. Its actual
certificate is `search 7 rows = false` for a fixed six-variable graph,
giving binaryCost>=8 while allowing any number of free NOT operations.
Together with a9-gate monotone witness, that proves replacement whenever
a NOT is present; a circuit with no NOT is returned unchanged.

For10696, an analogous **new** certificate of binaryCost>=12 would suffice:
a circuit containing a NOT would have at least13 total gates, and the
verified13-gate monotone control would be no longer. The zero-NOT case is
again immediate. This stronger binary-cost theorem has **not** been proved.

The raw9539 recursive checker has no memoization. Its initial live-wire
surplus is7+1-6=2. The proposed10696 query has binary budget11 and7 raw
inputs, so its surplus is5. Full truth-table separation has111 positive and
17 negative assignments, hence1,887 opposite-labelled pairs. Exact first
layer enumeration yields86 surviving branches: none dropping both operands,
two retaining one, and84 retaining both. The two one-retained cases exploit
N(5) being contained in N(6). These counts explain why replacing only the
target table and numeral in the existing kernel certificate is not a
validated runtime plan.

Root separately ran a bounded one-NOT SAT query; its evidence is in
../constructive/ and is not duplicated here.

## One authorized20-second monotone heuristic

search12.cpp searches12 binary AND/OR gates on all128 assignments. It starts
from one-gate erasures of the13-gate control and occasional random circuits,
with a fixed random seed10696. The run ended after20.0001 seconds,
308,248,576 repeated-state evaluations, and38,522 restarts. No solution was
found. The best returned circuit fails exactly on masks66 and98, with no
false positives. These are the missing1-6 edge input, with x5 optionally on.

verify.py independently evaluates that returned circuit and the control on
every input. It deliberately labels the returned12-gate circuit **incorrect**.
There was no second stochastic run and no inference of a lower bound from
search failure.

Reproduce the bounded heuristic with:

```sh
g++ -std=c++20 -O3 search12.cpp -o search12
./search12 > search-result.json 2> search.log
python verify.py
```

## Final signed probe

The shared signed-search source is in
../../L-meta-10487/signed-probe/probe.cpp. Root authorized a separate60s
probe for10696 after the smaller10487 query completed. The10696 run ended
UNKNOWN after60.0041 search seconds, with11,266,048 nodes,642,650,848
separation tests, a600,000-state failed-cache cap, and121,728KiB peak RSS.
Its complete small result metadata is in ../signed-probe/. This query allows
unbounded free NOTs; it is not the at-most-one-NOT circuit synthesis problem.
No further10696 search was started, and no formal certificate was obtained.

The live-wire method is attributed to the checked L-meta-9539 source
recorded by ../status-audit/. This folder contains our own bounded search
and audit artifacts, without copying that full third-party Lean file.
