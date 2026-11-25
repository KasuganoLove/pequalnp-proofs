# Independent scope review

Reviewed modules: `Pnp2343Pruning`, `Pnp2343QuadClean`, `Pnp2343CleanCost`,
`Pnp2343FreeOr`, and `Pnp2343CounterexampleShape`. Review date: 2026-11-25.

The source review found no mathematical-scope or wire-index error in the final
composition. Ordinary Lean compilation and the separate axiom audit are
recorded in `validation.json`; this review is not an official project verdict.

1. **Free-OR semantics.** The added OR reads the original 26-bit list. Every
   index at least 26 therefore reads false at that stage, even if it would
   numerically name a later gate's wire. `charged_wires` states the complete
   equality with the original circuit run on its augmented 27-bit input.
2. **Gate offset.** Original gate `r` has wire `27+r`. After charging the free
   OR, it becomes gate `r+1`, with wire `26+(r+1)`, which is equal to `27+r`.
3. **Nonbinary free OR.** Empty lists, one-element lists, repeated indices and
   out-of-range indices are permitted. The charged circuit is only asserted to
   satisfy `Monotone2`, as required by the counting composition; no unjustified
   `IsAO2` or `ReadsBack 26` assertion is made.
4. **The minimum being used.** `LeastSamples 27` minimizes over monotone
   earlier-wire circuits fitting the same fixed augmented samples. It does not
   minimize a 26-input charged circuit, and it does not require equality with a
   complete graph function on all inputs.
5. **Normalization cost.** Normalization does not increase total gate count.
   The formal conclusion is `D.size ≤ C.size`; no equality of sizes is needed.
6. **Exact finite families.** Positive samples use the subtype of all incident
   point-line flags. Negative samples use the subtype of all quadrangles.
   The shape proof does not replace them by a hand-selected test subset.
7. **Three different negatives.** `small_normal_shape` proves pairwise
   distinctness of `Q11`, `Q10`, and `Q01` by their conflicting operand values.
   It asserts a necessary form of a hypothetical counterexample, not that the
   form is impossible.
8. **The remaining hypothesis.** Output rejection does not imply rejection at
   every AND gate. A negative can activate an internal gate and be filtered
   later. The conditional bound explicitly retains this assumption.
9. **Local ranks.** AND negative signatures strictly decrease; OR positive
   signatures strictly increase. Interleaving the other operation and sharing
   gates prevents directly summing these ranks into a total gate bound.
10. **Strict-checker reuse hazard.** Two inherited proofs unfolding `gateAt`
    were replaced with direct `List.getD_eq_getElem` proofs. This avoids that
    identified source of the generated `gateAt.eq_1` dependency which affected
    a prior official reduction. This change does not establish compatibility
    with every rule of the project's strict single-file checker.

The existing cut R-meta-2343-811 splits on a direct AND-to-AND input. Its
negative side still permits AND-to-OR-to-AND paths. Replacing that condition
with absence of any AND ancestor would strengthen the hypothesis and is not
justified by the cut's statement.
