# P vs NP continuation 3 — 2026-11-24

Base: upstream `89b96c0f464824a164434fb460926400b9943047`. Research fork: `KasuganoLove/pequalnp-proofs`.

## L-meta-3600

The first child of a two-part reduction is proved in `L-meta-3600/Pnp3600LineSingle.lean`, with ordinary Lean compilation exit 0. It adapts upstream L_meta_2462: weakens full correctness to canonical one-line rejection and exposes the existing proof’s tighter `6 * size` count. The complement’s `94 * size` count is still open. The reduction has passed ordinary compilation, allowed-import guard, and exact-child diagnostics (601 and 1,260 printed characters). Local strict verification is currently pending; no official acceptance is claimed.

## L-meta-3608

Full task unproved. A finite-index normalization helper compiles cleanly and preserves the task assumptions. Both solver searches timed out with `unknown`; neither supplies a proof or counterexample. The lease was returned as `missing_lemma`. See its README for the missing transfer argument and reproduction.

## L-meta-1405

Work remains in progress; its eventual search outcome will be recorded separately. No proof is claimed here.
