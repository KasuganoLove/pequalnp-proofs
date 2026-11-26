# AND cleanliness through constant propagation

This is a research bridge for the clean-circuit child L-meta-8323 of L-meta-4201.
The source has passed ordinary Lean compilation with an empty log, and an
importable olean was built. This directory does not assert an official checker
verdict or an unconditional lower bound for arbitrary circuits.

## Exact result

`PEqualNP.Outside.Pnp4201CleanNormalize.normalize_nonconstant_clean_budgets`
takes a Monotone2 circuit C, a nonconstant target f, exact full-input equality
`circuitFun n C = f`, and `AndClean n f C`. The last premise says every AND in C
is false on every target-negative input. It produces D satisfying:

- `TopForm.IsAO2 n D` (only binary AND/OR gates, with backward reads);
- `circuitFun n D = f` on every input;
- `D.size ≤ C.size`;
- `opCount p D ≤ opCount p C` for every Boolean operation selector p;
- `AndClean n f D`.

The original C need not have backward reads. Nullary/unary gates, missing reads,
and forward references are handled by the already checked constant-propagation
semantics. Nonconstancy ensures the final output represents an actual retained
wire rather than a statically known Boolean constant.

## Proof invariant

`AndOff gs w` records that every AND emitted while executing gs on prefix w has
value false. Its indexed equivalence identifies these values with the stored
values in the full final wire list. The append lemma preserves the old
accumulator's property. An emitted gate has the same operation as its original
gate (`simplify_op`), and its newly allocated wire value is the original gate's
value (`simplify_sound` and `simplify_some_stat`). Induction over the eliminator
therefore preserves AndOff for each target-negative input. The existing
normalization wrapper supplies full output equality and all operation budgets.

## Attribution and dependencies

The constant-propagation construction is imported from our earlier
`Pnp2343Pruning.lean`, which attributes its elimination machinery to upstream
L-meta-1680, L-meta-1425 and related prior research. The operation budgets and
wrapper are reused from `Pnp4201OrBudget.lean`. The additional theorem here is
the semantic preservation of every AND's target-negative behavior. Dependency
hashes are recorded in validation.json; the parent research archive contains
the dependency sources. This module is a research module, not itself a
Defs-only official submission file. The final task file must inline the
necessary dependency declarations under the official import restrictions.

## Reproduce

In the restored pequalnp Lean checkout with its pinned toolchain, Mathlib cache,
and the two dependency modules compiled:

```bash
source /workspace/scratch/65f339da29fe/pnp-env.sh
cd /workspace/scratch/65f339da29fe/pequalnp-proofs/lean
LEAN_NUM_THREADS=1 lake env lean -j1 -o .lake/build/lib/lean/Pnp4201CleanNormalize.olean Pnp4201CleanNormalize.lean
```

This directory deliberately contains no compiled binary. The ordinary compile
log is empty because the frozen source produced no errors or warnings.
