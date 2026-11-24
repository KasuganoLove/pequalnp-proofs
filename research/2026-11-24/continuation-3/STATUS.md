# P vs NP continuation 3

Session began 2026-11-24. Final research checkpoint: 2026-11-25 00:11 Hong Kong time.

Upstream source commit: `89b96c0f464824a164434fb460926400b9943047`. Lean v4.36.0, Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. All work is in the user fork `KasuganoLove/pequalnp-proofs`.

## Official submissions

| PR | Contribution | Observed state |
|---|---|---|
| [#7558](https://github.com/open-goat/pequalnp-proofs/pull/7558) | This round: R-meta-3600-713, incidence budget reduction | Open, unmerged, no official comment at 2026-11-25 00:10 Hong Kong time |
| [#7168](https://github.com/open-goat/pequalnp-proofs/pull/7168) | Previous round: L-meta-3358 | Open, unmerged, no official comment at the same check |
| [#7182](https://github.com/open-goat/pequalnp-proofs/pull/7182) | Previous round: R-meta-3233-713 | Open, unmerged, no official comment at the same check |

PR #7558 head is `8fd875f4a31f93fb14369d75c0efb01490d458be`. It adds one file in one commit; its remote source equals the locally compiled proof byte for byte. It was created using the user's logged-in local Chrome. The desk acknowledged release as `reduced`, HTTP 200.

## Completed local research

### L-meta-3600: proved single-line budget and submitted reduction

The first child is proved in `L-meta-3600/Pnp3600LineSingle.lean`, ordinary Lean exit 0. It adapts upstream L_meta_2462: full correctness is weakened to canonical one-line rejection, and the existing argument's tighter `6 * size` count is exposed. The complementary incidence class's `94 * size` count is still open. Their partition has size `N * (q + 1)`, so the two budgets imply the exact posted `N * q ≤ 100 * size` conclusion.

The reduction compiles and passes the import guard and exact-child diagnostics (601 and 1,260 printed characters). Strict local verification did not complete: the reduction process was killed with exit 137 before a verdict; the canonical child passed its build stage, then its verifier exited 137 and the script reported CHECKER FAULT, exit 3. No strict acceptance or full original-task proof is claimed.

### L-meta-2391: physical pruning and local structure

Three standalone proof files pass ordinary Lean compilation. The strongest result proves every real gate of a least AO2 circuit for a nonempty graph accepts some edge-pair input, including the exact order-three plane. The proof physically propagates constants and aliases and strictly reduces gate count in the contradiction, while returning an exact-binary, no-constant IsAO2 circuit. A stronger theorem excludes pointwise-dominated constant/unary replacements that agree on every edge.

Other checked results characterize safe single-line contexts of pure-point products, preserve arbitrary monotone continuations under the stated reader replacement, specialize the context bounds to the order-three plane, and bound the actual TopForm.wmax of a gate true on two singleton inputs by one under C4-freeness. The full claim that every minimum circuit has empty junk remains unproved: productive mixed rectangles and shared OR readers remain uncontrolled.

### L-meta-3321: context bounds and a concrete no-growth rewrite

Three proof files pass ordinary Lean compilation. They establish at most two distinct safe single-line contexts for two nontrivial pure-point OR factors, at most one with a two-point intersection, the sharp finite example, and the circuit semantics bridge. A concrete five-gate shared singleton-true AND pattern can be replaced while preserving exact total gate count, every other wire value, output, remaining AND values, ReadsBack, Monotone2, and IsAO2.

The rewrite is formalized for six inputs and the specified prefix; the continuation and output may not read the obsolete H wire directly. Arbitrary offset/renaming and the general shared mixed-factor transformation are not yet formalized. The complete normal-form task is still open. No official cut was submitted; the leased task metadata did not allow reductions.

### L-meta-3608: finite-index normalization

The helper passes ordinary Lean compilation and caps operand indices at 23 while preserving evaluation and all stated side conditions, including NOT positions, coverage, multi-read sets, and raw-pair constraints. This retains smaller future-wire references; no unproved ReadsBack assumption was imposed. The full 512-input search and 35-input relaxation both returned UNKNOWN. No complete task proof or counterexample was found.

### L-meta-1405: bounded formula synthesis

The full C5 depth-6 search and both split-root searches returned UNKNOWN, with no candidate formula. The auxiliary P4 depth-5 solver reported UNSAT without a certificate or Lean proof; this does not refute the original task. A known P4 depth-6 formula passed all 4,096 assignments and all 70,897 generated clauses. Source, fixed dependencies, actual logs, calibration, and hashes are retained.

## Task disposition and next continuation

- 3600: desk acknowledged `reduced`, HTTP 200.
- 3608, 3321, 2391: desk acknowledged `missing_lemma`, HTTP 200, after the required investigation window.
- 1405: release requests encountered transient server errors; a later response confirmed HTTP 410, no live lease. The precise earlier release acknowledgement was not received.
- All compiler and search jobs have ended. No live lease is being retained for this batch.

`NEXT_STEPS.md` explains how to reuse the completed proofs, which normalization cases remain open, and which unsuccessful searches should not be repeated without a changed method. Each task folder records exact statements, proof sources, validation levels, provenance, and reproduction commands. Previous-round records remain under continuation-2.
