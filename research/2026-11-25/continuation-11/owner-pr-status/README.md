# Owner upstream PR audit — 2026-11-25 09:39–09:43 UTC

## Result

There are **no open upstream PRs authored by KasuganoLove**. Both the authenticated recent-PR list and an explicit author/repository search returned the same seven closed PRs (the request allowed the latest ten). No pending FAULT and no officially ACCEPTED-but-unmerged owner PR was found.

Four PRs are merged. Two proof PRs were closed because another proof was merged first. The only rejected PR, #7558, is already locally repaired and archived; it is not a fresh build-fix opportunity.

| PR | Task / artifact | Current state | Latest official evidence | Changed file |
| --- | --- | --- | --- | --- |
| [#7558](https://github.com/open-goat/pequalnp-proofs/pull/7558) | R-meta-3600-713 | Closed, unmerged | [REJECTED (reduce-extra)](https://github.com/open-goat/pequalnp-proofs/pull/7558#issuecomment-7150564742) at original head 8fd875f4a3; [run](https://github.com/open-goat/pequalnp-proofs/actions/runs/45530832936) | lean/PEqualNP/Outside/R_meta_3600_713.lean |
| [#7182](https://github.com/open-goat/pequalnp-proofs/pull/7182) | R-meta-3233-713 | Merged 2026-11-24 20:44:48 UTC | [ACCEPTED, exit 0](https://github.com/open-goat/pequalnp-proofs/pull/7182#issuecomment-7143536847); [run](https://github.com/open-goat/pequalnp-proofs/actions/runs/45470885437) | lean/PEqualNP/Outside/R_meta_3233_713.lean |
| [#7168](https://github.com/open-goat/pequalnp-proofs/pull/7168) | L-meta-3358 | Closed, unmerged | [Another proof merged first](https://github.com/open-goat/pequalnp-proofs/pull/7168#issuecomment-7141555514) | lean/PEqualNP/Outside/L_meta_3358.lean |
| [#5362](https://github.com/open-goat/pequalnp-proofs/pull/5362) | R-meta-2519-608 | Merged 2026-11-24 12:45:24 UTC | Merge metadata confirms completion; comments endpoint returned an empty list, so no separate checker verdict is asserted here | lean/PEqualNP/Outside/R_meta_2519_608.lean |
| [#5212](https://github.com/open-goat/pequalnp-proofs/pull/5212) | R-meta-2782-419 | Merged 2026-11-24 10:53:09 UTC | [ACCEPTED, exit 0](https://github.com/open-goat/pequalnp-proofs/pull/5212#issuecomment-7128803787); [run](https://github.com/open-goat/pequalnp-proofs/actions/runs/45372678880) | lean/PEqualNP/Outside/R_meta_2782_419.lean |
| [#5195](https://github.com/open-goat/pequalnp-proofs/pull/5195) | L-meta-2289 | Closed, unmerged | [Another proof merged first](https://github.com/open-goat/pequalnp-proofs/pull/5195#issuecomment-7129889917) | lean/PEqualNP/Outside/L_meta_2289.lean |
| [#5157](https://github.com/open-goat/pequalnp-proofs/pull/5157) | L-meta-2802 | Merged 2026-11-24 11:59:02 UTC | [ACCEPTED, exit 0](https://github.com/open-goat/pequalnp-proofs/pull/5157#issuecomment-7128994566); [run](https://github.com/open-goat/pequalnp-proofs/actions/runs/45374304707) | lean/PEqualNP/Outside/L_meta_2802.lean |

## Why #7558 should not be reopened as a routine repair

The current PR body explicitly records the prior repair: replace the problematic gateAt unfolding with List.getD_eq_getElem, avoiding the extra compiled declaration gateAt.eq_1. It records the pinned local checker result ACCEPTED (reduce), exit 0, 1,667 constants; this is a **local** result, not a new official verdict. The repair is preserved in the [continuation-4 archive](https://github.com/KasuganoLove/pequalnp-proofs/tree/e2fbf8407858adb89826b2fb7dca90576b0e1866/research/2026-11-25/continuation-4/L-meta-3600).

At **09:40:32 UTC**, the uncached [official step endpoint](https://pequalnp.com/desk/step?gap=L-meta-3600) returned **not_open**. That response deliberately combines “checked already” and “fleet stood it down”; it does not establish which reason applies.

The [public DAG snapshot](https://data.pequalnp.com/data/desk/gaps.json), updated **09:40:17.526 UTC**, has no posted or checked L-meta-3600 entry in the captured selected records and still lists exactly three open reduction records: R-L-meta-3600-421, -584, and -672. There is no currently evidenced valid reopening/submission opportunity. The unchanged remainder child is not proved by repairing the syntax.

## Fork head comparison and concurrent work

A read-only git ls-remote query showed that six of the seven PR branches still match their recorded PR heads exactly. The exception is the closed #7558 branch:

- PR-recorded rejected head: 8fd875f4a31f93fb14369d75c0efb01490d458be.
- Current fork branch codex/reduce-meta-3600-713: 0a0f000c43698759cba85b5cd1e11b0d8a442191.
- Current research branch codex/pnp-research-2026-11-24: 898bcfa033fef210fc7c1706d74026fbe79c3eca.

The audit does not attribute a branch change to either session. It records the difference so that a later action does not overwrite or duplicate already completed work. Full immutable heads and titles are in pr-status.json; the current branch tips are in fork-heads.txt.

## Scope and limitations

Read-only connector calls, public GETs, and git ls-remote only. No comment, push, PR creation/reopening, task allocation, heartbeat, release, Lean compilation, or strict checker was performed. An optional second public-DAG GET returned HTTP 403; the earlier successful response and its current HTTP Date/no-store step response are retained, and the failed request was not retried.

This is a point-in-time audit. It cannot rule out a concurrent Codex session opening a new PR after the queries completed. The actionable recommendation is to continue a legitimately held mathematical task rather than modify any of these seven completed/closed submissions.

