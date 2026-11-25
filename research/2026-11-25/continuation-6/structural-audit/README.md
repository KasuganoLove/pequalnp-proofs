# L-meta-5126: bounded structural sanity checks

## Scope

This directory records two finite **nonminimum** circuits. They test possible intermediate claims in the task sketch. Neither circuit is a counterexample to L-meta-5126, whose hypotheses include `IsLeastAO`.

The upstream theorem [L_meta_3760](https://github.com/open-goat/pequalnp-proofs/blob/76473d61fe19eff99fb56af72a5557eb51c01c5c/lean/PEqualNP/Outside/L_meta_3760.lean) already proves exactly the universal first-rung premise: no least circuit for a bipartite C4-free graph has precisely one junk gate. No search for a counterexample to that established premise was run here.

The finite semantics mirror [TopForm definitions](https://github.com/open-goat/pequalnp-proofs/blob/76473d61fe19eff99fb56af72a5557eb51c01c5c/lean/PEqualNP/Defs/TopForm.lean): every AND/OR gate has exactly two earlier input wires; a junk gate is an AND true on some assignment where the graph edge function is false; TopForm forbids a clean AND in the strict input cone of another AND. `wmax` is tested on all assignments, not only on pairs.

## Example A: a later junk gate need not be a rectangle

Inputs are `a=0, b=1, c=2, d=3`. The graph edges are `ac, ad`.

| Gate index | Wire | Definition |
|---|---:|---|
| 0 | 4 | `a OR b` |
| 1 | 5 | `c OR d` |
| 2 | 6 | `H = wire4 AND wire5` |
| 3 | 7 | `a OR c` |
| 4 | 8 | `J = H AND wire7` |
| 5 | 9 | `output = J AND a` |

The output is exactly `ac OR ad`. Gates 2 and 4 are exactly the junk gates, both are false on every singleton, the circuit is TopForm, and every gate reaches the output. Nevertheless, `J = ac OR ad OR bc`, and it has no representation `OR(A) AND OR(B)` with disjoint A and B. The script checks all 81 assignments of each variable to A, B, or neither.

The two-gate circuit `OR(c,d); AND(a,previous)` computes the same graph function. Hence the six-gate example is not least. Its valid lesson is only that **one-hot-off plus TopForm is insufficient by itself to infer that both junk gates are pure rectangles**. A proof for least circuits needs an additional minimality or non-nesting argument.

## Example B: two unsafe gates can filter each other

The graph is the matching with edges `ad, bc`. Form

* `H1 = (a OR b) AND (c OR d)`;
* `H2 = (a OR c) AND (b OR d)`;
* `output = H1 AND H2`.

Expanding these expressions with four ORs and three ANDs gives seven gates. Exactly H1 and H2 are junk; both are one-hot-off, TopForm holds, and **both have empty `wmax`**. Yet their conjunction is exactly `ad OR bc`: each eliminates the other's false positives. H1's false pair inputs are `ac, bd`; H2's are `ab, cd`.

The graph has a three-gate circuit `AND(a,d); AND(b,c); OR(previous two)`. Thus this example is also not least. It rules out deleting an arbitrary dirty gate merely because its individual `wmax` is empty, without handling joint filtering by another dirty gate.

## Validation and reproduction

Run with Python 3 and no third-party dependencies:

```sh
python3 check_examples.py
```

The checker independently evaluates every assignment for both original circuits and both smaller competitors: 16 rows per example, 32 rows total. It also checks bipartiteness, the common-neighbor definition of C4-freeness, two junk gates, their singleton values, strict cone dependencies, TopForm, all gates reaching output, all `wmax` conditions, and 81 disjoint factor pairs for each of four dirty gates (324 pairs total).

The result is `PASS`; the full checked truth tables are in `examples-results.json`. This directory's validation is **Python enumeration, not Lean verification**. A separate agent was assigned a Lean `decide +kernel` formalization of Example A; its status and source are recorded separately, not assumed here.

## Latest upstream delta

`upstream-delta.json` records a bounded comparison from `b9ee4cd40b7d244de81c9c4d1403325dd7767c8b` to `76473d61fe19eff99fb56af72a5557eb51c01c5c` (head commit 2026-11-25 04:58:13 UTC): 129 commits and 129 added Outside files, with no Defs/helper changes. The 32 new complete L-files were classified from available task statements or direct final-theorem reads. No new generic two-junk normal form was identified.

New erasure results include L5863, L6037, and L6142. The exact correction preserved here is that **L6037 erases an OR gate by redirecting to an earlier operand**, producing a smaller pointwise-below circuit; it is not an AND-gate erasure result. The recently added R5198/R5200/R5202 reductions concern the plane-order-3 finite-sample two-output problem, not the generic bipartite two-junk task.

No lease calls, remote mutations, broad synthesis, or fresh checker runs on upstream sources were performed for this audit.

## Curated files

* `README.md`: interpretations, exact limitations, and reproduction command.
* `check_examples.py`: independent finite checker.
* `examples-results.json`: truth tables and all checked results.
* `upstream-delta.json`: pinned upstream comparison and scoped findings.
* `manifest.json`: hashes and byte sizes of the four files above.
