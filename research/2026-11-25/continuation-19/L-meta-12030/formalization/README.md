# L-meta-12030: complete local structural proof

The canonical candidate `lean/PEqualNP/Outside/L_meta_12030.lean` proves the exact posted statement. Its SHA-256 is `052c0e4396cdacee1909ddbf8b6e39d859bb960676599515c5ad60b9a202d11b`, 58,118 bytes. The exact statement hash is `e50570ddcea1fe3974acf5881b09d0dd3ef181e0ec090dbe67354377e5ef26b4`.

## Proof and attribution

This proof reuses ptrdsh's merged [PR #15263](https://github.com/open-goat/pequalnp-proofs/pull/15263), L-meta-11315, whose generic proof is adapted from L-meta-10458 in the Apache-2.0 repository. The reference is commit `7dd594cc96b1fc5b83ca9266a00cef93d6871df6`, source SHA-256 `e13152ef69931ca79dc9f4354f6752a38f3c17a48863616654032ab41a18b131`. Attribution is also preserved in the candidate's header.

The retained generic prefix, including the four-input finite certificate, is unchanged except for namespace and provenance comments. The new data are the graph table, three restricted tables, explicit change assignments, ten-gate monotone witness, and exact public statement.

The circuit semantics bridge treats NOT as free in an oriented, zero-preserving binary computation. Setting variables 1, 2 and 4 false each saves at least one binary gate, because the current target changes and remains nonzero. Explicit change assignments are 10, 68 and 17; assignment 9 stays true after every restriction. The remaining inputs `{0,3,5,6}` form a complete four-vertex core. The existing `U4` certificate requires at least seven binary gates on that core. Thus the original function requires at least ten non-NOT gates; any circuit containing a NOT has at least eleven gates. A new monotone ten-gate witness fits inside that budget. A circuit without a NOT is returned unchanged.

The proof retains the original `lower_with_not ≥ 11` route even though the monotone witness now uses only ten gates. It does not need a new numerical search or a revised generic lower-bound theorem. As in the reference, the at-most-one-NOT premise is unused; the actual argument handles any legal input circuit that contains a NOT.

## Verification completed by this worker

`prepare_structural.py` independently verifies all 128 assignments of the ten-gate witness, every restriction-table equality, all three change and nonzero witnesses, the K4 singleton/pair conditions, unchanged generic prefix, and exact final statement. It records the four truth tables in `structural-data-audit.json`.

The independent status agent separately recomputed the same data and checked the immutable candidate; its report is `../independent-audit/candidate-data-check.json`.

Ordinary Lean passed with exit code 0 from 15:03:39.288146 to 15:04:22.287464 UTC on 2026-11-25: 42.999 seconds wall time, 36.082 seconds CPU, peak RSS 4,439,600 KiB. The log contains only the reference proof's deprecated `if_neg` warning, not an elaboration error. The output olean was written under `.lake/build/lib/lean/PEqualNP/Outside/L_meta_12030.olean`.

This worker has not run the strict checker or published a PR. Those actions remain with the parent agent; no official acceptance is claimed in this checkpoint.

## Reproduction

With the exact public `gap.json` and `statement.txt` alongside the generator:

```bash
python3 prepare_structural.py \
  --reference /path/to/L_meta_11315.upstream-reference.lean \
  --output /path/to/lean/PEqualNP/Outside/L_meta_12030.lean
```

The generator verifies the reference hash and refuses to overwrite an output containing different bytes. The original ordinary check, from the pinned repository's `lean` directory with the project environment sourced, was:

```bash
lake env lean -j1 \
  -o .lake/build/lib/lean/PEqualNP/Outside/L_meta_12030.olean \
  PEqualNP/Outside/L_meta_12030.lean
```

The candidate is also preserved as `L_meta_12030.structural.lean`. No solver, CNF, LRAT certificate or full seven-input exhaustive circuit search is part of this proof.
