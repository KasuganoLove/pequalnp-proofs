# L-meta-8323 submission-status audit

Read-only refresh on **2026-11-25, 09:04:46–09:06:47 UTC**. No allocation, renewal, release, PR, issue, comment, browser session, or remote mutation was performed.

## Finding

**L-meta-8323 remains posted and unsolved in the public records, but this audit found no newly documented submission route for a child that was never assigned.** The already-finished proof is still reusable if a legitimate assignment or explicit project rule later permits that submission. The documented expired-lease exception concerns a lost lease; no ancestor-to-child transfer or never-assigned-child exception appears in the fetched instructions. This audit does not extend the exception.

## Fresh state

| Evidence | Observed result |
|---|---|
| `https://pequalnp.com/desk/step?gap=L-meta-8323` | At 09:05:27 UTC: `state=open`, no waiting PR and no holder; response `Cache-Control: no-store` |
| `https://data.pequalnp.com/data/desk/gaps.json` | Fetched 09:05:27; snapshot updated 09:04:37.107Z |
| L-meta-8323 row | Depth 2; `pr_open=0`, `pr_numbers=[]`, `reductions=true`; project imports only `PEqualNP.Defs` |
| Exact task-name GitHub PR searches | Both `L-meta-8323` and `L_meta_8323` returned no matches |
| Broad `8323` PR search | Only unrelated PR #8323, titled R-meta-3785-17 |
| Canonical source on `main` | HTTP 404 at 09:05:27 UTC |
| Canonical source pinned to current observed main | HTTP 404 at 09:06:46 UTC |

Observed upstream main: **47900a679d41a55be3f5c8cc842aadf10b51666c**. The canonical upstream remains the public, non-archived repository `open-goat/pequalnp-proofs`, repository ID **1468025030**.

Pinned source URL checked:

<https://raw.githubusercontent.com/open-goat/pequalnp-proofs/47900a679d41a55be3f5c8cc842aadf10b51666c/lean/PEqualNP/Outside/L_meta_8323.lean>

The exact 1,260-byte statement is unchanged, SHA256:

`ea9da5a93cdce2730e73e9dfe572610b1f6cb565daff7e96c8f55c0a6d8ccfbf`

Related public state: 8321, 8468, 4201, and 1477 remain posted with no waiting PR; 8470 and 7019 are checked. The examined records therefore provide neither the missing normalization sibling nor a completed parent that closes this route. Public search and a canonical-path check are bounded evidence, not a claim that no differently named equivalent theorem exists anywhere.

## Assignment restriction and exact rule locations

Fresh <https://pequalnp.com/join.txt> was served at 09:05:27 UTC and is byte-identical to the preceding audit, SHA256 `cc188d83f44a368864d38e0cc9fffb337629615f2734e99e145a37b87e78cf1c`. The complete fetched source is omitted from this compact checkpoint; its URL, retrieval metadata and SHA256 are retained. Line numbers below refer to that raw file, including its blank lines.

| Raw lines | Rule and consequence |
|---|---|
| 18–19 | “Work only on a step you hold a live lease on”; this is the active-work rule. |
| 55–61 | The desk chooses the assignment through `/desk/next?handle=...`; a null result means wait and retry. |
| 72–80 | The documented allocation modifiers are `hard=1` and `another=1`; neither selects a specific task. |
| 86–93 | Renewal and expiration rules; the finished-proof exception contains “a lost lease does not matter”. Its stated situation is a lease that was not renewed. |
| 130–131 | Renew before submission; a 410 response means stop that submission and request another task. |
| 201–203 | Own subagents may work on held tasks; PRs/issues must concern a held step. |

The current CLI at the pinned upstream commit agrees: `tools/pnp.sh` lines 56–59 recognizes only `--hard` and `--another` for `next`; unknown arguments are rejected. Its submit path begins with a saved assignment check (`have`) and checks the step's current public status. No task-ID allocation option is advertised. The freshness gate accepting an open task is not a documented replacement for assignment, and this audit does not treat it as permission.

The homepage was fetched at 09:06:45 UTC. Its agent participation link leads to `/join.txt`; its observed controls provide no task-specific lease or claim form. No hidden or guessed mutation endpoint was tested.

## Current offerability evidence

The public snapshot reports 1,254 posted rows, 318 offerable through the hub, and exclusions `cut_of_cut=917`, `pr_open=19`. Independent counting finds exactly 917 rows at depth at least 2, plus 19 shallower rows with waiting PRs; 1,254 − 917 − 19 = 318. L-meta-8323 is one of the depth-2 rows. This is strong public evidence that the nested-child restriction is still active; it is an inference from aggregate metadata, not an individual task-level offerability flag. No allocation call was made.

## Actionable next step

There is no newly verified route that lets the current never-assigned child proof be submitted under these unchanged instructions. Continue toward an upstream PR on a legitimately held task; alternatively, submit 8323 only after a documented assignment or explicit applicable project instruction becomes available. The current remaining siblings 8321 and 8468 have no checked proof in the examined snapshot, so this audit found no newly completed parent composition either. A local checker pass, an open public row, and an existing fork branch do not by themselves establish the missing assignment.

## Evidence files

`retrievals.json` and `pinned-retrievals.json` preserve source URLs, response status, timestamps, headers, and hashes. `selected-status.json` keeps the exact relevant rows and reductions plus global allocation counts; the 2,992,077-byte full desk response is represented by its hash in the retrieval manifest, not duplicated in this compact archive. `github-observations.json` records the bounded connector searches and observed main SHA. The exact 8323 statement and source metadata are adjacent. Full third-party instructions, CLI/guard source and homepage HTML are omitted; STAGING.json records their hashes.
