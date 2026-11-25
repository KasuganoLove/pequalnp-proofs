# L-meta-11315: eleven-gate control and signed lower-bound instance

The parent supplied an eleven-gate monotone factorization. The explicit gate
list in baseline.json has been independently checked on all128 assignments.
Writing t=x0 OR x1, its four final terms are

`x4 AND (t OR x2)`, `(t OR x3) AND (x5 OR x6)`, `x0 AND x3`, `x5 AND x6`.

Eight gates construct the shared signals and these terms; three OR gates join
the terms. Output wire17 follows the seven raw inputs and eleven gates. The
literal graph has exactly the eleven edges in the public statement.

## Completed ordinary search

The signed live-wire replay uses the existing L9539 recursion, allowing
unbounded free NOT operations and at most nine binary AND/OR operations.
It uses the full128-assignment domain:108 positives and20 negatives, yielding
2160 Cartesian positive/negative pairs and a4320-bit Lean sample encoding.

The one authorized run completed with `EXHAUSTED_NO_MODEL` in0.402974 seconds,
exit0, visiting56,211 nodes and performing4,542,808 separation checks. Its
start and end were `2026-11-25T13:58:18.972294+00:00` and
`2026-11-25T13:58:19.388783+00:00`. Only the complete raw-input sublist passes
initial separation. The replay has no memoization, polarity canonicalization,
sorting, constant skipping, or duplicate skipping. The process was capped at
60 seconds and1GiB; it reported peak RSS6656KiB.

This ordinary program execution is not itself a Lean theorem. A formally
proved rejection would establish binaryCost>9. For a circuit containing a
NOT, total gate count would then be at least11, so the verified eleven-gate
monotone circuit is a no-longer replacement. A circuit without NOT is already
monotone. The parent is pursuing that formal proof separately; this checkpoint
does not assert an official acceptance.

## Independent candidate audit and splitting fallback

The sibling formalization/independent-audit.py reads the parent's candidate
without modifying it. For candidate SHA256
`09ef326be4a9fb250111f398d3f10418d8a562d57b490cc4ee41f3945df4fd84`, it verifies
the exact posted statement, every packed input bit and label, and the parsed
witness on every input. The sample polarity is positive lower half, negative
upper half, so F equals the complement of goal. After explicitly normalizing
the instance parameters, witness, statement, permitted import change and
comments, the generic source is identical to checked L_meta_9539.

The audit also independently constructs the92 first-level successors in the
literal source order. Of these,84 retain both operands,6 retain the first,
and2 retain the second. Every guard agrees between the128-bit raw truth table
and the4320-bit paired representation. This is a finite-data check, without
another recursive search or Lean run.

## Reproduction and attribution

Compile literal-probe.cpp with `c++ -std=c++20 -O3`. The program has the
nine-gate budget and60-second deadline in its source. run.py first rechecks
the baseline and then records the ordinary run; it overwrites run.json and
literal-result.json, so use a copy to preserve the checkpoint.

The signed live-wire method is reused from checked L_meta_9539, which credits
L9136, L9146 by partymejker, L8633 by k-sandhu, and L8463/L1449 under
Apache-2.0. The instance data, baseline verification, ordinary replay and
independent audit are the present work. The complete canonical Lean proof,
its strict checker results, and official PR are managed by the parent.
