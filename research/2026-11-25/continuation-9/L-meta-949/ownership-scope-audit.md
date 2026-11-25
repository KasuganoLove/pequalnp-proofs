# L-meta-949: independent statement and evaluator audit

Reviewed at **2026-11-25 08:06 UTC**. The root agent owns the live reduction-only
lease. This agent read the task and definitions, then stopped before starting
enumeration or SAT synthesis because upstream L-meta-950 already supplies the
exact logically opposite result.

## Exact evaluator scope

`AndCountCircuit 6` counts AND gates only. Each operand is an arbitrary OR of
selected raw vertices and selected earlier AND outputs. Empty sides, overlapping
raw supports, arbitrary output selections, and repeated use of earlier gates are
allowed. `WellFormed` requires every selected gate predecessor to have a smaller
index. No side-disjointness, unit-off, or C4-free condition is implicit.

The task's correctness requirement is partial: reject every maximal independent
set and accept its augmentation by each vertex outside it. It does not require
acceptance of every positive edge input. This distinction was checked before
considering synthesis.

## Exact contradiction with the existing theorem

The unchanged tracked file
`lean/PEqualNP/Outside/L_meta_950.lean` has SHA-256:

`0b7e2f524d8cf838ed8e00ccb86224d0fa9ba587dfb9e5f750c1325d73a4cc3a`

Its public theorem universally quantifies over the same graph and circuit types.
Its antecedent is exactly `C.WellFormed` together with the same partial
maximal-independent-set/augmentation condition. Its conclusion is exactly the
existence of a biclique cover with `k ≤ C.size` which 949 negates. In particular,
950 does **not** add full computation, graph girth, disjoint operand supports,
empty output-vertex sets, or circuit minimality as premises.

For any hypothetical witness to 949, applying 950 to that witness's well-formed
and partial-correctness hypotheses produces the cover its final hypothesis
denies. This is an exact logical contradiction, not a stronger-hypothesis
comparison.

The final 950 proof obtains a cover with `min C.size 4` bicliques: it handles
sizes 0, 1, 2, and 3 separately, and uses the six-vertex cover bound 4 above that.
Thus the previously proposed 156-graph witness search has no valid positive
target under the current statement and existing theorem.

The remote-status agent independently confirmed that the local source hash
matches the public checked proof: PR #1995 merged at
2026-11-23 19:56:33 UTC, run 45247366970. That agent owns the fetched public
provenance records. The fresh task desk still offering 949 is a task-state
inconsistency; it does not weaken the theorem's quantifiers.

## Work and submission boundary

- No enumeration, SAT process, stochastic search, or new Lean compilation was
  started by this agent for 949.
- No official full proof or reduction file was produced.
- No lease operation or remote write was performed.
- Root should use the existing theorem and public provenance when resolving the
  stale positive task through the documented task workflow. A positive
  existential witness must not be fabricated, and an arbitrary unresolved
  subgoal should not be advertised as progress toward that false witness.
