# Continuation 7 — Petersen primitive-reader obstructions

Date: 2026-11-25, Asia/Singapore (UTC+8).

This checkpoint studies **L-meta-1884**. The full 18-gate suffix lower bound
remains unproved. The new results constrain how a correct circuit can read its
raw variables. They are ordinary Lean-checked research, not an official task
submission or strict-checker verdict.

## Exact task and the remaining canonical case

The task permits an arbitrary map `σ : Fin 10 → Fin 10` and an arbitrary unary
Boolean function `u`. It asks whether every `FanInTwo` circuit of size at most
18 fails on some input when its initial wires are
`List.ofFn (x ∘ σ) ++ [u (x 0)]` and its target is the Petersen edge function.
The map is not assumed to be a permutation.

The existing checked reduction `R_meta_1884_773` and checked results L2594 and
L2596 already remove the arbitrary relabeling and unary-function choices.
The remaining L2598 uses canonical wires `[x0, ..., x9, NOT x0]`. The new
lemmas below concern this canonical case; they do not redo the existing
normalization or assume that its unresolved lower-bound child is proved.

## 1. Primitive joins force another reader

`lean/Pnp1884UniqueRead.lean` imports only `PEqualNP.Defs`. Its main result is
`primitive_join_forces_another_reader`:

> If a circuit correctly computes the Petersen edge function on canonical
> free-NOT0 inputs, and one AND/OR gate combines a nonzero raw variable `v`
> with a distinct primitive wire, then another gate must also read `v`.

The distinct primitive wire may be another raw variable or the free NOT0
wire. Either operand order is allowed. The conclusion does not need a size
bound or a fan-in restriction on the other gates.

The proof has two substantive components. `sole_reader_collision` propagates
equality through the entire circuit when changing one input leaves its sole
reader's output unchanged. It masks forward references as false, in agreement
with the actual circuit evaluator, and treats the chosen output wire
explicitly. `pinning_certificate` supplies a negative-to-positive Petersen
input pair for every nonzero variable, distinct primitive wire and pinned
Boolean value. The other primitive stays at the value that blocks the chosen
AND/OR gate. All entries of this finite certificate are checked by
`decide +kernel`.

The correct circuit cannot output a raw variable directly: singleton inputs
make that variable true while the Petersen edge function remains false.
`output_not_raw` discharges that possible exception in the packaged theorem.

## 2. Effective readers, including NOT-tail semantics

The original conclusion counts syntactic occurrences. The root model allows a
NOT gate to carry additional listed inputs after its first input; those tails
do not affect its value. The public reader-count reductions correctly ignore
them.

`lean/Pnp1884ActiveRead.lean` strengthens the argument to this exact convention:
`activePins` takes only the first NOT input and the whole input list for every
other operator. `activePins_eq_rec` proves equality to the recursor expression
used in L5367 and L5369. `eval_active_congr` and
`sole_active_reader_collision` propagate equality from agreement on these
effective inputs.

The strengthened `primitive_join_forces_another_active_reader` guarantees a
different gate that actually reads `v`; an unused NOT-tail occurrence cannot
satisfy the conclusion. `primitive_join_forces_active_head` gives the explicit
head-versus-membership formulation. These results still do not need a fan-in
or minimum-size assumption.

## 3. Why this does not yet finish the lower bound

L5367 gives the checked inequality `15 + r ≤ C.size`, where `r` counts gates
that actively read wire 0 or wire 10. Thus an 18-gate candidate has at most
three such readers. The unresolved L5369 excludes exactly that remaining
regime.

Our new theorem forces extra readers of a variable `v ≠ 0`. Even when the
primitive join uses wire 0 or 10 as its other operand, the extra reader is a
reader of `v`, not automatically another reader counted by `r`. A global
incidence bound or additional structural argument is still needed. We do not
infer `r ≥ 4` from this result and do not claim a contradiction to the size
budget.

The source review and upstream classification audit record this boundary.
All three existing reduction slots of L1884 are occupied; these research
lemmas were not submitted as a fourth reduction or as a complete proof.

`reader-classification/` makes the remaining local cases explicit. Its Python
checks cover all 324 pairs of other raw variables for the nine nonzero
variables, and all 16 Boolean partner functions for both gate operations.
For a sole reader, a partner depending on a nonedge pair must be a constant
identity for that operation. On an edge pair, the only additional possibilities
are NAND of that edge for an AND join, and AND of that edge for an OR join.
The pivotal-input premise is already present in L6081/R1884_412; the archive
credits it and does not present the table as a new task proof.

Two explicitly verified 29-gate circuits realize these remaining forms while
having exactly three active readers of wire 0 or 10. They demonstrate why the
size bound still matters. Both were checked on all 1,024 assignments in
Python; neither is an 18-gate counterexample or a new Lean theorem.

## 4. Bounded counterexample search

`bounded-search/` preserves source, fixed-seed settings, candidate circuits,
and a separate scalar verifier. Forty explicit 20-gate baseline circuits
were verified on all 1,024 Boolean assignments. The search considered 30,400
two-gate deletions, 30,240 one-field edits around representative seeds, then
180 seconds of NOT-enabled local annealing using the complete truth table in
every fitness evaluation.

No 18-gate counterexample was found. The saved best 18-gate candidate is wrong
on 11 assignments: five false positives and six false negatives. It computes
the graph obtained by replacing Petersen edge `{2,3}` with nonedge `{2,5}`.
It is a reproducible near miss, not a solution. Search failure is not a proof
of a lower bound. The evaluation count includes repeated candidate states.

## Validation and provenance

The original primitive-reader module, its active-reader strengthening, and
their axiom-audit modules were checked with the project's pinned Lean 4.36.0
environment. Per-file results and hashes are recorded in `validation.json`
and `manifest.json`; compiler and axiom output is in `validation/`.

The axiom audits distinguish the kernel-checked finite pinning table from the
classical circuit proofs. No `sorryAx`, new axiom or `native_decide` is used.
There was no strict project-checker run for this partial development and no
official PR or acceptance claim.

Wire helpers retain attribution to our earlier 1031/2343/5126 developments and
upstream L2668 / L1499 / PR #3112. The collision argument, pinning certificate
and primitive-reader exclusion are the new work. The active-reader convention
is taken from the actual public L5367/L5369 statements.

To reproduce the ordinary builds, copy the files under `lean/` to the project
Lean root and compile in this order:

```sh
lake env lean -j1 -o .lake/build/lib/lean/Pnp1884UniqueRead.olean Pnp1884UniqueRead.lean
lake env lean -j1 -o .lake/build/lib/lean/Pnp1884ActiveRead.olean Pnp1884ActiveRead.lean
lake env lean -j1 Pnp1884UniqueReadAudit.lean
lake env lean -j1 Pnp1884ActiveReadAudit.lean
```

The modular research imports and `#print axioms` audit files are for this
checkpoint. They are not presented as an official one-file submission.

The independently allocated lease was renewed successfully during the work
and released with `missing_lemma` at 05:48:53 UTC after more than 28 minutes.
No other session's lease was changed. Work then continued on a separately
allocated task. This public checkpoint contains no lease credentials.
