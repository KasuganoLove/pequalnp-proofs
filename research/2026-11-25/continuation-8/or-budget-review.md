# Independent review: Pnp4201OrBudget.lean

## Reviewed immutable version

**Result: no correctness defect found in the reviewed scope.** The file proves useful normalization and deletion facts under an OR budget. It does not prove the104-OR lower bound.

* Source: `lean/Pnp4201OrBudget.lean`,343 lines,14,855 bytes.
* Frozen SHA256: `e2b63e64080ec8919a421d0c64e8fc0d679546e858cd479190cb794189e70858`.
* Imported research dependency: `lean/Pnp2343Pruning.lean`,54,373 bytes, SHA256 `4f080984395e3362d5164a3ca1528beee970f42ca58b651130aa6c817098cb5d`.
* The implementation agent confirmed that this frozen source compiled with exit0. The reviewer observed an empty `OrBudget-lean.log` and did not run compilation.
* The implementation agent separately reported an exit0 axioms audit: all eight principal theorems use only `propext`, `Classical.choice`, and `Quot.sound`. The reviewer also found no `sorry`, explicit new axiom, `native_decide`, or `unsafe` declaration in either inspected source file.

## Checks

### OR count and physical deletion

`orCount_eq_public` matches the task's exact OR predicate by case analysis on every `GateOp` constructor. The general `bypass_opCount` proves an equality: the bypass count plus the indicator of the deleted operation equals the original count. Redirecting wire indices changes only input lists, not operators. Thus deleting an AND preserves the OR count; deleting an OR lowers it by one. The derived inequality is sufficient to keep every bypass candidate inside the original operation budget.

### Normalization, constants, and forward references

The inspected `simplify` emits either no gate or one gate with the original operation. `simplify_countP` and `elim_countP` therefore control every operation predicate, not just total size. Empty and unary gates are propagated into constants or aliases without adding compensating OR gates.

The normalizer does not assume the original circuit reads backward. Its state lookup uses default false for nonexistent current wires, matching the public evaluator's forward-reference behavior. The imported semantic invariant preserves every wire value. The resulting nonconstant output is a real wire; the constant-output case is rejected explicitly using the supplied nonconstancy hypothesis. The output circuit is `IsAO2`, with exact two-input AND/OR gates and backward references, while preserving the entire function and not increasing any operation count.

### Correct minimization domain

`LeastBudget n f p K C` minimizes total gate count **among Monotone2 circuits computing f with `opCount p ≤ K`**. `exists_least_budget` applies `Nat.find` to that exact class. It never replaces a low-OR candidate by an unrestricted minimum-size circuit.

`least_budget_normal_form` first chooses such a minimum, then normalizes it. The normalized circuit remains within the same p,K budget and has no greater total size, so its minimum property follows against the same comparison class. There is no use of unrestricted `IsLeastAO` or `IsMinimalMonoCircuit`.

### Bypass semantics and the false-wire case

The alias lemmas require the replacement to be either an earlier wire or beyond the original final wire range. The imported bypass proof handles renumbering and default-false semantics under these exact restrictions.

A bypass to a missing wire need not preserve `ReadsBack`; this is not a gap. Its use in the minimum contradiction requires only `Monotone2`, which is the comparison class in `LeastBudget`. The file establishes the required operation budget and full output equality before invoking minimality.

### All assignments, not a sample set

Correctness is stated as `circuitFun n C = f`. `least_budget_no_alias_order` checks the preservation implications on every positive and every negative assignment. The AND negative-incomparability and OR positive-incomparability corollaries therefore use the full function, not a finite witness sample inherited from the2343 research file.

## Limits relevant to future use

1. The normal-form existence theorem explicitly requires f to be nonconstant. Applying it to the PG4 target still needs the easy zero-input/edge-input witnesses.
2. `least_budget_gate_productive` gives a gate true on **some positive assignment**. It does not assert an edge-pair witness, gate pivotality, or any local cleanliness property.
3. AND negative-incomparability supplies full negative assignments. OR positive-incomparability supplies full positive assignments. Neither automatically restricts those witnesses to a preferred finite sample family.
4. This file imports local research `Pnp2343Pruning`. It is not currently a self-contained official task submission obeying Defs-only import restrictions; packaging such a submission would require the appropriate helper inlining or permitted-import proof route.

No source mutations, new compilation, lease operations, or remote writes were performed by the reviewer. The source hash was rechecked against the author's frozen hash before this review was finalized.
