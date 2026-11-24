# L-meta-2391: checked gate-pruning lemmas

This archive contains a complete Lean proof of a useful necessary condition on
minimum monotone circuits. It does **not** prove the assigned statement that
every minimum AO2 circuit for the order-three projective plane has no dirty AND
gate. No official proof file or PR for that statement was created.

## Checked results

The single source file `Pnp2391Pruning.lean` imports only `PEqualNP.Defs` and has
no additional local source dependencies. Its namespace is `Pnp2391Pruning`.

* `graph_sandwich`: a monotone Boolean function below the edge function of a
  graph is equal to the graph function if it accepts every edge-pair input.
* `prune_explicit_zero`: replacing a gate by an explicit false signal and then
  propagating constants produces an actual AO2 circuit for any nonconstant
  resulting function, with at least one fewer gate than the original list.
* `least_gate_productive`: for any nonempty finite graph, **every real gate of
  every least AO2 circuit** computing its edge function accepts at least one
  graph edge-pair input. The statement is about all gates, not only AND gates.
* `plane3_gate_productive`: the preceding conclusion specialized to the exact
  order-three incidence graph used in L-meta-2391. Nonemptiness is witnessed by
  point zero and line zero.
* `prune_small_gate`: the same physical simplification for any AND/OR gate with
  at most one input. This includes a constant and a unary wire alias.
* `least_no_small_replacement`: a gate of a least AO2 graph circuit cannot admit
  a constant or unary replacement whose value is pointwise below the old gate
  and agrees with it on every graph edge-pair input. The replacement is
  evaluated on the same earlier prefix of gates. This supplies the physical
  deletion step needed for a safe earlier-wire alias.

The final theorem accepts the exact semantic hypotheses it uses. It does not
assume that equality on edge-pairs alone preserves arbitrary circuit behavior:
the pointwise domination hypothesis controls all negative inputs, and
monotonicity extends agreement on minimal positive inputs to all positive
inputs.

## Why the productivity argument is valid

Suppose a gate is false at every edge-pair input. Replace its value by false.
All subsequent gates are monotone, so the output can only decrease. At each
edge-pair, the replaced value was already false, so the circuit still accepts
that edge-pair. Every positive input contains an edge-pair, and monotonicity
therefore forces the modified circuit to accept every positive input. It
computes exactly the original graph function.

This semantic modification initially uses a constant that is excluded by AO2.
The proof does not leave that model issue implicit. A forward pass stores each
old wire as a constant or an alias of an earlier retained wire. An AND reading
false becomes false; an OR reading false aliases its other input. The general
simplifier also handles true constants and unary aliases. Only binary AND/OR
gates with earlier inputs are emitted. The replaced gate emits no gate, so the
gate count decreases strictly. Since the graph is nonempty, its edge function
is nonconstant; the final output status must therefore be a genuine wire.

The resulting circuit satisfies the actual `PEqualNP.TopForm.IsAO2` definition:
AND/OR operations only, exactly two inputs per emitted gate, and `ReadsBack`.
Gate-input repetitions are allowed by that definition. The smaller equivalent
circuit contradicts `IsLeastAO`.

## What remains missing for L-meta-2391

A productive gate can also accept a nonedge. For example, in the order-three
incidence graph, the signal

`(P[0] OR P[1]) AND (L[0] OR L[1])`

accepts the edge `(P[0], L[0])` and also the nonedge `(P[0], L[1])`, since zero
does not belong to `1 + {0,1,3,9}` modulo 13. This is only an illustrative gate
signal; it is not a circuit computing the whole incidence function and is not
a counterexample to the original assignment.

Thus productivity removes gates with no useful edge behavior but does not
remove mixed gates carrying both useful edge behavior and dirt. The stronger
small-replacement lemma handles a gate when a suitable earlier input or wire
already matches all its edge behavior and is pointwise below it. A general
reason every dirty AND of a minimum plane circuit must have such a replacement
is still missing. An existence theorem for a clean minimum normal form would
also not by itself prove the assignment's universal claim about every minimum
circuit.

## Validation and reproduction

The full 913-line file passed ordinary Lean checking with exit code zero on
2026-11-24. `pruning-compile.log` is the final compiler output. It contains
style-linter warnings from copied helper proofs and no errors. This research
helper was not run through the project's strict checker or an official task
checker, and no official acceptance is claimed.

Pinned environment:

* Project commit: `89b96c0f464824a164434fb460926400b9943047`.
* Lean toolchain: `leanprover/lean4:v4.36.0`.
* Mathlib revision: `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`.

From a fresh checkout, with `elan` installed:

```sh
git clone https://github.com/open-goat/pequalnp-proofs.git pequalnp-pruning-check
cd pequalnp-pruning-check
git checkout 89b96c0f464824a164434fb460926400b9943047
cd lean
elan toolchain install leanprover/lean4:v4.36.0
lake exe cache get
LEAN_NUM_THREADS=1 lake build PEqualNP.Defs
cp /absolute/path/to/pruning-archive/Pnp2391Pruning.lean ./Pnp2391Pruning.lean
LEAN_NUM_THREADS=1 lake env lean -j1 Pnp2391Pruning.lean
```

Use the archive's actual absolute location in the `cp` command. The task-local
validation used the same final command, with
`ELAN_HOME=/workspace/scratch/65f339da29fe/pnp-tools/elan` and that installation's
`bin` directory on `PATH`. Single-threaded execution was used to avoid the
session's observed multithreaded runtime stalls. No further Lean source files
from this research session are required.

## Provenance

The wire-evaluation and constant-propagation core was adapted from the already
merged `lean/PEqualNP/Outside/L_meta_1680.lean`. The `CleanGate`, `CleanL`,
`simplify_clean`, and `clean_elim` machinery was adapted from the already merged
`lean/PEqualNP/Outside/L_meta_1425.lean`, converting its status datatype to the
sum-type representation used here. Operation-preservation and the fold proof
for AND/OR preservation follow
`lean/PEqualNP/MetaComplexity/Helpers/LocClean.lean`. All these sources are at the
pinned project commit above; the necessary declarations are included in this
file and rechecked in its own namespace.

The graph sandwich, physical zero/small-gate wrappers, edge-productivity
theorem, exact-plane specialization, and small-replacement minimality theorem
are the new composition and proof work in this archive. The original assigned
statement remains unresolved.
