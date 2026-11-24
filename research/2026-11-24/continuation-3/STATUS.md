# P vs NP continuation 3 — 2026-11-24

Base: upstream `89b96c0f464824a164434fb460926400b9943047`. User fork: `KasuganoLove/pequalnp-proofs`. Status checkpoint: 2026-11-24 23:54 Hong Kong time.

## Submitted: L-meta-3600 reduction

[PR #7558](https://github.com/open-goat/pequalnp-proofs/pull/7558), head `8fd875f4a31f93fb14369d75c0efb01490d458be`, adds one Lean file in one commit. The task desk accepted release as `reduced` (HTTP 200). The remote file equals the locally compiled file byte for byte. Official verdict is pending.

The first child is proved in `L-meta-3600/Pnp3600LineSingle.lean`, ordinary Lean compilation exit 0. It adapts upstream L_meta_2462: weakens full correctness to canonical one-line rejection and exposes the existing proof’s tighter `6 * size` count. The complementary incidence class’s `94 * size` count is still open. The reduction itself compiles and passes the import guard and exact-child diagnostics (601 and 1,260 printed characters).

Strict verification did not complete locally. The reduction process was killed with exit 137 before a verdict. The canonical child copy passed the strict script’s build phase, then its verifier exited 137; the script reported CHECKER FAULT, exit 3. No strict acceptance or full original-task proof is claimed. Both complete logs and exact statuses are retained.

## Archived: L-meta-3608

Full task unproved. A finite-index normalization helper compiles cleanly and preserves the task assumptions. Both solver searches timed out with `unknown`; neither supplies a proof or counterexample. The lease was returned as `missing_lemma`. See its README for the missing transfer argument and reproduction.

## Archived: L-meta-1405

The full C5 depth6 search and both split-root searches returned UNKNOWN, with no candidate formula. The auxiliary P4 depth5 solver reported UNSAT without a certificate or Lean proof; this does not refute the original task. A known P4 depth6 formula passed all4,096 assignments and all70,897 generated clauses. The complete small archive contains source, fixed dependencies, actual logs, and hashes. The task was stopped locally. Three `missing_lemma` release attempts did not return a usable confirmation (timeouts or a non-JSON response); the last confirmed lease expiry is 2026-11-24T16:08:13.218Z. No further task work is running.

## Active work

L-meta-3321 (no-larger clean circuit normalization) and L-meta-2391 (junk-free minimum circuits for the order3 plane) are still under investigation. Their eventual results will be recorded separately. No complete proof is claimed.

## Prior submissions

PR #7168 (L-meta-3358) and PR #7182 (R-meta-3233-713) had no official comments when checked at23:50 Hong Kong time. Historical records remain under continuation-2.
