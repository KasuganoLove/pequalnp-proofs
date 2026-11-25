# L-meta-12128: frozen structural partial and an unassembled stronger route

Root released this task with `missing_lemma` at **2026-11-25 15:32:41.409774 UTC**, HTTP 200. No further mathematics, solver run or Lean build was performed for this task after that instruction.

This package contains a genuine ordinary-Lean-checked **partial**, not a complete public submission. It also records a stronger route using existing helpers that was identified but **not assembled or compiled**.

## The exact function

The six-input target is the truth table

`4276676736 * 2^32 + 4269860864 = 18368186720953886720`.

It is monotone and has 28 true assignments. All singleton and pair inputs are false, so directly fixing two inputs false cannot leave the four-variable pair-threshold core used in L-meta-11315. The input-complement step below addresses that obstruction without a new generic gate-elimination theorem.

## What was formally checked

`Pnp12128Structural.lean` proves these two endpoints for every legal six-input AND/OR/NOT gate list computing the exact target:

- `binary_ge_nine`: at least nine non-NOT gates.
- `with_not_ge_ten`: if any listed gate is NOT, at least ten total gates.

The second endpoint does not assume there is at most one NOT. Here `countBinary` is the reused helper's count of all non-NOT gates, including nullary and unary AND/OR gates; the legal circuit premise restricts operations to AND/OR/NOT.

The proof uses the unchanged seven-input semantic helpers with an initial list containing **only six physical input wires**. The seventh semantic coordinate is ignored. Initial wire 3 is the complement of raw variable 3. Because `ori (NOT var3) = var3`, the existing `trans_binary` lemma keeps the same counted binary budget. This construction does not change the input length seen by the original circuit or assume reads-back.

For the transformed function `H(x)=F(x XOR 8)`, `H(0)=false`. The proof then fixes inputs 5 and 3 false. The six-input tables are:

1. `16788998196968685800`
2. `9294867679535825128`
3. `18374379617126377704`

The essential-input witnesses are assignments 47 and 11; assignment 3 stays true. The remaining variables `{0,1,2,4}` compute the four-variable threshold-at-least-two function. Two applications of the existing `remove_var` lemma plus the fixed `U4` lower bound give nine non-NOT gates. The proof handles the mixed-polarity intermediate function; no monotonicity of `H` is assumed.

The source SHA-256 is `d0a864aa7780832cf7d61b89401df8e4b727899dae931d73f1112e22a525a44c`, 4,933 bytes. Ordinary Lean passed with **exit 0 and an empty log**, from **15:28:04.569413 to 15:28:23.267709 UTC**, 18.698 seconds wall time and peak RSS 2,992,936 KiB. This worker did not run a separate `#print axioms` audit or the project's strict checker for this partial.

## Research import and exact dependency

The module imports `PEqualNP.Outside.L_meta_12030`. This is an intentional **research-only import**, using the ordinary-checked helper module published in [upstream PR #16085](https://github.com/open-goat/pequalnp-proofs/pull/16085):

- Public head: `2372e819a59762ba46009b456bcb7e27a226aca8`.
- Imported source: `lean/PEqualNP/Outside/L_meta_12030.lean`.
- Imported source SHA-256: `052c0e4396cdacee1909ddbf8b6e39d859bb960676599515c5ad60b9a202d11b`.
- The reusable helpers derive from ptrdsh's merged L-meta-11315 / [PR #15263](https://github.com/open-goat/pequalnp-proofs/pull/15263), itself adapted from L-meta-10458 in the Apache-2.0 repository.

**The official L-meta-12128 task allows only `PEqualNP.Defs`.** This research module cannot be submitted unchanged. A complete official file would have to inline the required attributed helpers, prove the complete exact public statement, and pass the strict checker. The partial does not depend on an assumption that PR #16085 has received an official ACCEPTED verdict.

## Stronger total-size route, not yet formalized here

Fixing the original last input `x5` true gives exactly the five-input majority function. Its table is the high 32-bit word `4276676736 = 0xfee8e880`.

Two existing APIs would exclude every full circuit of at most ten gates:

1. `PEqualNP.MetaComplexity.Helpers.gate_elim`, publicly wrapped by `PEqualNP.MetaComplexity.L014`, removes at least one gate when the last raw input is essential and its selected cofactor is nonconstant. It supports the repository's unrestricted legal AND/OR/NOT model, including missing reads and NOT's first-pin semantics.
2. `PEqualNP.Outside.L_meta_1433.Live.bound_fee8e880` has the exact type `HasCircuitSize 5 (targetFn 0xfee8e880) s → 9 < s`. This is a **total-gate** lower bound for arbitrary legal circuits, not a free-NOT binary-gate lower bound.

For this target, input 5 is essential (assignment 7 changes to assignment 39 when it is set true), and its true cofactor is nonconstant. If a ten-gate full circuit existed, `gate_elim` at `n=5`, `b=true`, and residual budget 9 would produce a nine-gate MAJ5 circuit, contradicting the existing lower bound. This is a complete logical route to total size at least eleven, but its endpoint was **not assembled, ordinary-compiled or strict-checked in this task**. The requisite library/Outside oleans were not present, and the worker did not start a large dependency build.

The minimal relevant source paths, hashes and import dependencies are recorded in `helper-provenance.json`. The archive does not copy the full third-party helper sources. The L1433 source explicitly credits live-wire normalization/search to L-meta-517.

## Remaining gap and computation status

The independently handled constructive attempts for ten and eleven monotone gates both ended **UNKNOWN**, with no model or certificate. The constructor verified a thirteen-gate monotone control on all 64 inputs; that evidence is maintained in its separate constructive package. Neither the checked binary partial nor the unassembled eleven-gate total lower-bound route matches that thirteen-gate upper bound. Therefore the requested universal no-larger monotone replacement theorem remains unproved in this checkpoint.

## Reproduction

The completed finite-data computations are consolidated in `audit_core.py`; it performs no synthesis or network operation. `flipped-core-data.json` records the values observed before closure. To reproduce the ordinary partial check, first provide the exact imported L-meta-12030 source/head described above in the pinned checkout and build its olean, then run from `lean`:

```bash
lake env lean -j1 \
  -o .lake/build/lib/lean/Pnp12128Structural.olean \
  Pnp12128Structural.lean
```

The full public task and its imports are preserved in the task's `statement.txt` and `gap.json`. Reproduction commands are documentation; no extra build or solver run was performed after release.
