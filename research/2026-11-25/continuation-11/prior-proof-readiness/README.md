# Existing-proof submission readiness audit

## Result

**No additional submission-ready candidate was established beyond the separately tracked L-meta-8323.** In particular, this audit found no other completed exact posted proof with evidence that the exact task was held during completion and is still open now.

This was a read-only review of existing checkpoints. No new mathematics, Lean compilation, strict checking, lease operation, network request, or remote write was performed. The official-stage completion criterion remains an upstream PR plus an official ACCEPTED verdict; this inventory does not complete that stage.

## Evidence base

The current-status comparison uses the root's existing cached desk snapshot, updated **2026-11-25 09:04:37.107 UTC**, at:

`pnp-session-2026-11-25/continuation-11/desk-current.json`

The source is `https://data.pequalnp.com/data/desk/gaps.json`. `candidate-status.json` records the cache hash and compact status evidence. Absence from the posted/checked/withdrawn lists is recorded only as absence; it is not relabelled as a newly observed rejection or withdrawal.

The bounded archive review covered the overview and continuations 4–10 under `research/2026-11-25`, then followed the explicitly identified complete-proof references into the preceding day's overview and continuations. It also enumerated canonical `L_meta_*.lean` / `R_meta_*.lean` files in those two research dates, distinguishing copied upstream dependencies from the user's own results.

## Completed results that do not yield a fresh open submission

| Result | Existing proof evidence | Current or historical obstacle |
| --- | --- | --- |
| L-meta-7019 | Exact full proof, local strict ACCEPTED | Excluded by request; current cache marks checked. |
| L-meta-8470 | Exact full proof, local strict ACCEPTED | Excluded by request; current cache marks checked. |
| L-meta-3358 | Exact full proof, local strict ACCEPTED; user PR7168 already created | Current cache marks checked. Continuation4 records that another proof was adopted and PR7168 closed as duplicate. |
| L-meta-2982 | The plane essential-input child was already proved during the earlier parent work | Current cache marks checked. It is not an available new task. |
| L-meta-3438 | Earlier complete non-NOT-count component | Current cache marks checked; the archive already noted other contributors' proof PRs. |
| L-meta-2768 | Two complete checked components, not the full original task in our archive | Current cache marks the parent checked. |
| L-meta-2802 / L-meta-2289 | Earlier full proofs already submitted as PR5157 / PR5195 | Both are checked in the current cache. The archive records 2802 merged and 2289 overtaken. |
| L-meta-3233 | Completed reduction, locally and officially accepted as PR7182 | Current cache marks the parent checked. This was already an official contribution, not a new full proof. |
| L-meta-3600 | Repaired exact reduction, local strict ACCEPTED | This is a reduction with an unresolved second child, not a complete task proof. Continuation4 records all three active reduction slots occupied and PR7558 closed. The current cache does not list 3600 among posted tasks. |
| L-meta-2604 | Exact assigned theorem completed under the earlier work; ordinary Lean/format/axioms passed | The original STATUS.json records withdrawal because another contributor proved it before submission. It is absent from the current posted list. The old strict attempt exited137 without a verdict. |
| L-meta-2798 | Exact task refutation, local strict ACCEPTED (refute), 1,903 constants | The 2026-11-25 overview explicitly records task-platform `not_open` at verification. It remains absent from the current posted list. No currently open task was established. |
| L-meta-2534 | Positive twin proved locally, refuting the assigned negation; ordinary compilation/axioms passed | Original STATUS.json records release with `statement_seems_false`, HTTP200. It is absent from the current posted list. No full official-format/refute-check record or presently open target was established. |

The three older cases 2534, 2604, and 2798 were the only plausible unsubmitted full-result exceptions surfaced by the overview. None satisfies the requested current-open condition on the available evidence. The audit does not invent a task route for them.

## Recent still-posted tasks whose full statements remain unproved

The 09:04:37 snapshot still lists 1031, 2343, 5126, 1884, 2590, and GCT232. Their checkpoints explicitly delimit the completed components:

- **1031:** pruning, normalization, finite AND-soundness tests, and a conditional ownership bridge. Missing clean-minimum existence.
- **2343:** sample normalization and a 63-gate lower bound with an additional internal-AND rejection premise. The exact posted task does not supply that premise.
- **5126:** TopForm preservation, small-support dirty witnesses, and a nonminimum sanity example. The two-junk least-circuit exclusion remains open.
- **1884:** missing-variable and active-reader constraints. The complete 18-gate suffix lower bound remains open.
- **2590:** the clean-circuit twenty-gate bound and a dirty-AND necessity theorem. Arbitrary circuits remain outside the proved clean case. Search results do not provide a counterexample or lower-bound certificate.
- **GCT232:** restricted star/block/row-zero analysis and finite coefficient searches. No full complex three-plane exclusion or counterexample, and no complete official Lean proof.

Other reviewed earlier checkpoints 3384, 3608, 1405, 3321, and 2391 likewise explicitly state that the assigned full theorem is unresolved. Complete local helper lemmas are not promoted into full original-task proofs.

## L-meta-8323 remains separate

8323 is still posted and has a complete locally strict-accepted source. This audit was instructed to exclude it. The earlier route audit records that the session held the parent4201 lease but never the exact8323 child lease; this inventory provides no new evidence changing that distinction or establishing the finished-proof/lost-lease exception for that child.

## Sources within the research checkout

- `research/2026-11-25/README.md`: 2798 not-open refutation and earlier official outcomes.
- `research/2026-11-25/continuation-4/README.md`: exact7019, repaired3600, partial1031, official3358/3233 status.
- `research/2026-11-25/continuation-5/README.md`: exact2343 gap versus conditional result.
- `research/2026-11-25/continuation-6/README.md`:5126 scope.
- `research/2026-11-25/continuation-7/README.md`:1884 scope.
- `research/2026-11-25/continuation-8/README.md`:8323/8470 exact outcomes and parent4201 gap.
- `research/2026-11-25/continuation-9/README.md`:2590 conditional scope and949 stale-task audit.
- `research/2026-11-25/continuation-10/README.md`: official completion criterion and GCT232 scope.
- `research/2026-11-24/README.md` and `STATUS.json`:2534 and2604 exact historical dispositions.
- `research/2026-11-24/continuation/README.md`: earlier2802/2289,2768 components,2982 precursor.
- `research/2026-11-24/continuation-2/README.md`:3358/3233 submissions and3384 partial scope.
