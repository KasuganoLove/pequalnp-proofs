# L-meta-8323: current official-submission readiness

Read-only audit completed **2026-11-25 08:27 UTC**. No lease action, proof
modification, compilation, strict check, or remote mutation was performed.

## Result

**The prepared proof remains technically ready and has not been obsoleted by
an observed checked task or parent result.** This is not an official submission
or acceptance. The remaining obstacle is obtaining the task system's legitimate
submission route: the current public record is open but depth 2, which the
automatic offer list excludes. Root is separately handling that route.

## Exact proof and branch

- Repository: `KasuganoLove/pequalnp-proofs`.
- Branch: `codex/prove-meta-8323-2026-11-25`.
- Current branch head: `0873097889691e4d21f575dabed0c1cadd0bcb3a`.
- Canonical source: `lean/PEqualNP/Outside/L_meta_8323.lean`, **179,631 bytes**.
- Source SHA-256:
  `43febc27f36b15f7c0503609ce9179931a9ac0d7a7a5ebae745b93f8fa47e3b6`.
- The remote file's Git blob is
  `6d230f8152291aa66fd65e0cd9bb67fae1c558cd`, exactly matching the archived source.
- Compared with current audited upstream, the branch is one commit ahead and
  583 commits behind, with exactly **one added file**: the canonical 8323 proof.
  Its merge base is `259523a5b265318b84f9377f2feb965fd213f898`. This comparison
  does not itself assert GitHub mergeability or an official CI verdict.

## Upstream compatibility

The audited current upstream snapshot is
[`cd0950a130d9623c6445380890e515c906116816`](https://github.com/open-goat/pequalnp-proofs/commit/cd0950a130d9623c6445380890e515c906116816),
committed at **08:17:48 UTC**. Actual local bytes match all **85** upstream Defs
blobs, with identical path sets. `Defs.lean`, `CheckLemma.lean`, the format guard,
build/check tools, lake configuration, Lean pin, and Mathlib manifest also match.
Actual local Mathlib HEAD remains `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`.

The six CI-wrapper differences already documented in continuation-8 remain:
the added Elan-install and memory-watch scripts/tests, plus the advisory and
authoritative workflows. None of the audited upstream control files changed
since that prior compatibility audit. The full CI wrapper is therefore not
identical to the older local checkout, but the semantic checker and fixed proof
environment are unchanged. No new checker run was warranted to investigate an
observed source or definition change, because no such change was found.

The existing final local strict result remains **ACCEPTED (check)**, exit 0,
2,344 constants, completed at 07:13:19 UTC. It does not substitute for the
official repository's own checker run after a legitimate submission.

## Current task and replacement check

The public desk snapshot updated at **08:22:08.065 UTC** still lists 8323 with
depth 2, `pr_open = 0`, and no PR numbers. The remote-status reviewer fetched the
snapshot and read-only `/desk/step?gap=L-meta-8323`; the latter reported open and
no holder. This audit independently compared the saved current statement with
the canonical declaration and strict statement file: both are exact matches,
SHA-256 `ea9da5a93cdce2730e73e9dfe572610b1f6cb565daff7e96c8f55c0a6d8ccfbf`.

An exact GitHub PR search for `L-meta-8323` returned no matches; the canonical
file was absent from audited upstream. A bare-number search found unrelated
PR #8323 and was not treated as a task match. The current public records also
leave parents **4201** and **1477** posted, with no open PR and no checked or
withdrawn status. Thus no checked replacement for this task, or checked parent
closure, was found. This is a timestamped status audit, not a claim to have
searched every differently named equivalent theorem.

## Evidence files

- `upstream-blobs.json`: fresh pinned Git-tree metadata, fork ref/blob, exact PR
  search result and canonical-file absence.
- `compatibility.json`: actual local SHA comparisons and exact current
  statement comparison; includes the six known CI differences.
- `current-compare.json`: current upstream versus prepared fork branch.
- `task-status.json`: selected public task and parent records, with the source
  endpoint and snapshot timestamp. No lease credential is included.

The user's completion criterion is an **official upstream PR**. A fork review
PR or this readiness audit does not satisfy that criterion. Recheck the live
task and PR state immediately before any eventual official submission.
