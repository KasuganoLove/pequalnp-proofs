# L-meta-1031: finite tests for AND soundness, and a conditional ownership bridge

## Verified result

`Pnp1031OwnershipFinite.lean` proves a direct equivalence for **any** simple graph
`G` and **any** `Monotone2` circuit `C`. Every AND gate is globally sound for the
graph edge function if and only if every AND gate rejects:

1. The all-false input.
2. Every input `pairInput u v` with `¬ G.Adj u v`, including `u = v`.

Here global soundness means that whenever the gate is true, some graph edge has
both endpoints active. Repeated endpoints supply the singleton tests; they must
not be omitted. The zero test handles nullary AND gates, including the empty
input domain. The theorem needs no output-correctness, minimum-size,
triangle-free, or four-cycle-free hypothesis. Its precise Lean statement is:

```lean
theorem all_and_sound_iff_finite_tests {n : ℕ} (G : SimpleGraph (Fin n))
    (C : Circuit) (hmono : Monotone2 C) :
    AllAndSound G C ↔ RejectsNonedgePairs G C
```

This is a condition on **all AND gates of the same circuit**. Testing just one
chosen gate does not establish its global soundness: an earlier untested AND
can supply a larger conjunction. The finite condition is equivalent to global
AND soundness, not a strictly weaker normalization assumption.

### Why the finite test is complete

Consider an input containing no graph edge. Induct on wire indices. A true raw
input witnesses itself, an out-of-range reference is false, and a true OR has
a true earlier input. Thus, as long as no true AND has appeared, every true wire
has an active raw variable that makes that wire true on every input containing
the variable. If an AND became true, its at-most-two input wires would provide
at most two such witnesses. This yields a true zero, singleton, or nonedge-pair
test at that AND, contradicting the hypotheses. The Lean proof explicitly
handles input-list lengths zero, one, and two, as well as references unavailable
in the current circuit prefix.

## Conditional route to the target ownership normal form

`Pnp1031OwnershipBridge.lean` composes existing upstream theorems. For a
triangle-free and four-cycle-free graph, **given** a minimum Monotone2 circuit
computing the graph edge function and passing these finite tests, it constructs
a circuit of the same minimum size whose AND gates are globally sound and each
own a nonempty star of graph edges.

The file keeps the remaining premise explicit in `existence_bridge`:

```lean
∃ C, IsMinimalMonoCircuit n C ∧ EdgeCorrect G C ∧ RejectsNonedgePairs G C
```

**This archive does not prove L-meta-1031.** We have not established that every
graph covered by the task admits a minimum circuit satisfying that premise.
The direct equivalence identifies the premise exactly with existence of a
globally clean minimum circuit. It does provide a finite collection of circuit
evaluations for checking a candidate's cleanliness.

The bridge is a research composition, not an official submission file. It
imports upstream outside proofs, which the task's submission import rules do
not allow. Those dependencies would need to be inlined for an official file.
The direct equivalence file imports only `PEqualNP.Defs`.

## Attribution and existing results

- The `Wire` evaluation helpers in `Pnp1031OwnershipFinite.lean` are copied from
  [L_meta_1906](https://github.com/open-goat/pequalnp-proofs/blob/72c6f42af03b1daed876cf3c65638fccd31f20b7/lean/PEqualNP/Outside/L_meta_1906.lean).
  The new part is the independent-input wire witness induction and the
  finite-test equivalence.
- [L_meta_4101](https://github.com/open-goat/pequalnp-proofs/blob/72c6f42af03b1daed876cf3c65638fccd31f20b7/lean/PEqualNP/Outside/L_meta_4101.lean)
  supplies the vertex-cover size budget from finite gate tests.
- [L_meta_4320](https://github.com/open-goat/pequalnp-proofs/blob/72c6f42af03b1daed876cf3c65638fccd31f20b7/lean/PEqualNP/Outside/L_meta_4320.lean)
  builds a globally sound circuit within that budget.
- L_meta_1906 supplies a no-larger globally sound circuit where every AND owns
  at least one graph edge.
- [L_meta_1600](https://github.com/open-goat/pequalnp-proofs/blob/72c6f42af03b1daed876cf3c65638fccd31f20b7/lean/PEqualNP/Outside/L_meta_1600.lean)
  shows that a sound AND in a four-cycle-free graph owns no edges or a star.

These upstream results are reused, not claimed as new results of this work.
Gate productivity or edge pivotality alone is not the `Owns` predicate; this
archive uses the actual ownership theorems.

## Validation and reproduction

Both source files passed ordinary Lean compilation with exit code 0; their
logs are empty, indicating no errors or warnings. The four upstream bridge
dependencies were also compiled successfully. No strict project checker was
run on these research artifacts. `validation.json` records the toolchain,
source dependency hashes, and checkout head observed at archive time. One
comment in the bridge was clarified after compilation; proof text is unchanged.

From a configured checkout of the recorded upstream source and pinned Lean
toolchain, place both research files at the root of `lean/`, then run there:

```sh
LEAN_NUM_THREADS=1 lake env lean -j1 Pnp1031OwnershipFinite.lean
LEAN_NUM_THREADS=1 lake build PEqualNP.Outside.L_meta_4101 PEqualNP.Outside.L_meta_4320 PEqualNP.Outside.L_meta_1906 PEqualNP.Outside.L_meta_1600
LEAN_NUM_THREADS=1 lake env lean -j1 Pnp1031OwnershipBridge.lean
```

The checkout's ordinary build may compile additional prerequisite modules on a
fresh machine. Neither research file contains `sorry`, `admit`, new axioms,
`unsafe`, or `native_decide`.
