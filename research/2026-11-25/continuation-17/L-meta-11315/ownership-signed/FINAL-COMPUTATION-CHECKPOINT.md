# L-meta-11315 completed computation checkpoint

The parent reported a heartbeat HTTP410 at2026-11-25T14:21:23.452684Z.
All computation described here had already finished. This worker stopped
new11315 work at that notice. No cause of the410 is inferred here, and no
official acceptance is claimed for this worker's candidate.

## Completed evidence

1. The eleven-gate monotone control is correct on all128 assignments.
2. The full-domain literal signed search, with at most nine binary gates and
   free unbounded NOTs, completed with no model:56,211 nodes in0.402974s.
3. The independent audit of the parent's original literal Lean candidate
   SHA09ef326be4a9fb250111f398d3f10418d8a562d57b490cc4ee41f3945df4fd84
   verifies its exact statement, sample bits/polarity, witness and limited
   template changes. This audit is not a Lean build or a kernel verdict.
4. A smaller sample set consisting of eleven edge positives and all twenty
   negatives also completed literal rejection:670,154 nodes in3.3541s.
   It requires all seven raw inputs, has126 first-layer successors, and
   corresponds to width440 in the paired Lean representation.
5. Using only the seven maximal negative assignments admits a sampled model.
   The literal search found one in0.003736s. Its reconstructed circuit has
   nine binary gates and two NOTs; it fits the eighteen selected assignments
   but fails36 of the full128 inputs. It is not a public-task counterexample.
   Fourteen raw-input sublists separate this smaller instance, so assuming
   all seven inputs necessary would be incorrect.

## Full-domain profiling for proof splitting

All92 first branches were profiled with the same literal C++ recursion.
They reject in a combined0.48719435s. Their node counts sum to56,210, exactly
one less than the original root search. The largest first branch is54 with
8069nodes; branch1 has2132nodes.

The eight one-retained first branches have the following second-layer sizes:

| First branch | Second children |
| --- | ---: |
| 1 | 102 |
| 4 | 96 |
| 7 | 96 |
| 10 | 94 |
| 29 | 98 |
| 32 | 94 |
| 54 | 110 |
| 58 | 94 |

All784 second states were profiled:16,659 total nodes in0.101036703s.
The largest is branch54/child10 with451nodes. Raw128-bit and paired4320-bit
guards agree for every generated second state. There is no sorting,
deduplication or omitted keep-none branch; branch54 has two keep-none cases.

These profiles are ordinary computation. They do not certify the Lean
search result or predict a strict-checker's memory usage.

## Reproduction and retained files

The original ownership-signed/MANIFEST.json remains unchanged. The separate
FINAL-SUPPLEMENT-MANIFEST.json records later sources, results and audits.
Compiled binaries and regenerable large state/input dumps are excluded from
that curated supplement, with their hashes recorded as exclusions.

Compile branch-profile.cpp with a C++20 compiler and run it to recreate the
first-branch JSON. Run formalization/independent-second-level.py after the
existing first-level audit to regenerate the second-state list. The input
format for second-profile.cpp is one whitespace-delimited state per line:
parent-index, child-index, next-budget, extra, frontier-length, then the
hexadecimal frontier signatures from that JSON. It outputs one JSON record
per state. The completed profile output is retained separately.

For the partial-sample experiments, partial-samples/probe.cpp accepts
`edges_all` or `edges_maximal`; run.py caps a run and reconstructs any model.
partial-samples/audit.py independently verifies the selected data and sampled
model, and regenerates the width440 first-layer states. These programs were
not rerun after the410.

## Unexecuted next idea

The parent proposed collecting a smaller subset of positive/negative pairs
that witnesses every failed separation test in the original literal trace,
then adding assignment-coverage pairs and replaying with that fixed subset.
The stop arrived while this worker was reasoning about its invariants.
No adaptive-pair source, selected-pair list, collection run, replay, or result
was created. It remains an unexecuted plan, not evidence.

Attribution remains as in the original checkpoint: the signed live-wire
framework is from checked L9539 and its credited upstream predecessors.
No11315 Lean or strict-checker job was run by this worker.
