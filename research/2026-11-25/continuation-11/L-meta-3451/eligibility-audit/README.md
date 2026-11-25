# L-meta-3451: reduction eligibility and existing-PR source audit

Read-only audit on 2026-11-25, approximately 09:24–09:29 UTC. No lease action, external write, installation, solver, Lean compilation, or strict checker was run.

## Reduction is not eligible

Fresh public desk data, served **09:25:23 UTC**, snapshot updated **09:24:27.696 UTC**, agrees with the parent's current allocation record: the L-meta-3451 row has **no `reductions: true` field** and no `reductions_live` field. The public reduction list contains **zero** entries with parent L-meta-3451. Global `reductions_open: true` is present, but does not grant permission to a row without the required flag.

The task remains posted, not checked or withdrawn; its desk row reports `pr_open: 0`. A separate live status request served 09:25:22 UTC reports three anonymous holders. The parent's live lease is independently established by its own allocation; the anonymous public response does not identify accounts.

Primary URLs:

- <https://data.pequalnp.com/data/desk/gaps.json>
- <https://pequalnp.com/desk/step?gap=L-meta-3451>
- <https://pequalnp.com/join.txt>

This is confirmed by actual official intake enforcement. [PR #11761](https://github.com/open-goat/pequalnp-proofs/pull/11761), R-meta-3451-1, was closed unmerged at **02:55:02 UTC**. Its [official comment](https://github.com/open-goat/pequalnp-proofs/pull/11761#issuecomment-7151355038) states that the task is not open to reductions because its row lacks the flag, and that a full proof remains welcome.

The sketch's instruction to propose a cut therefore conflicts with the actual per-row submission gate. It does not supply a usable exception. Other inspected reduction PRs #11106 and #7052 are closed unmerged; no accepted live R3451 artifact was found in the desk list or local source tree. A reduction should not be submitted under the current row.

## PR #11549 is auxiliary work, not a complete proof

- URL: <https://github.com/open-goat/pequalnp-proofs/pull/11549>
- Current observed head: `33a61afa8d2972a676159968e6b0b9940f973baf`
- Source fork: `wneb-creator/pequalnp-proofs`
- Changed file list: exactly `lean/PEqualNP/Outside/L_meta_3451.lean`
- Full source: **168,031 bytes, 3,662 lines**
- SHA256: `4a0687272d92a47f45a32d19edf41cf9ecee5a89eb59af23dfc54e0b471f7a2f`
- Source URL: <https://raw.githubusercontent.com/wneb-creator/pequalnp-proofs/33a61afa8d2972a676159968e6b0b9940f973baf/lean/PEqualNP/Outside/L_meta_3451.lean>

The PR remains open/unmerged in the connector metadata. Its only current observed official verdict is [REFUSED before any build](https://github.com/open-goat/pequalnp-proofs/pull/11549#issuecomment-7150855066), posted **02:32:26 UTC**, because `partial` appears in the line-4 comment. The linked run is <https://github.com/open-goat/pequalnp-proofs/actions/runs/45532816252>.

Reading the full source establishes that removing the forbidden comment would not complete the task:

1. The header itself says the unrestricted statement remains unproved.
2. There are **zero `theorem` declarations** and no declaration of the canonical target `PEqualNP.Outside.L_meta_3451`.
3. Every result is an auxiliary lemma inside `PEqualNP.Outside.L_meta_3451_aux` and subordinate namespaces. The file ends by closing that namespace.
4. Its final `Prune.edge_sensitive_normalization` obtains a size-minimal equivalent circuit whose AND gates each affect some incident positive input when zeroed. This does **not** make its AND gates false on singleton or nonincident point-line inputs, as required by the posted theorem.
5. Other sections cover restricted relations, small support, formulas, dependency counts, and pruning. They are not assembled into the unrestricted statement.

A lexical scan found no `sorry`, `admit`, `axiom`, `unsafe`, `native_decide`, or `initialize` token in this file. That is not a validation of the auxiliary lemmas: no local compilation was performed in this audit, and the official run stopped before compilation. The decisive defect is absence of a proof of the requested theorem. The original source was read unchanged; this compact checkpoint preserves its pinned URL and SHA256 rather than copying the third-party draft.

## PR #9850 is also not repairable by formatting alone

The other proof-looking title, [PR #9850](https://github.com/open-goat/pequalnp-proofs/pull/9850), is closed/unmerged. Its head is `06316581e1ca8f3bac966e9c7c5ba70519a0e7e9` in `whereisrsi/pequalnp-proofs`.

The entire 21-line file was read; its metadata is retained, while the unfinished source body is omitted from this checkpoint. Its attempted main proof is literally `:= by sorry` at line 19. The [official refusal](https://github.com/open-goat/pequalnp-proofs/pull/9850#issuecomment-7144411996) names that same token. An hourly sweep closed the unchanged PR at 04:32:03 UTC. This is an actual proof hole, not a forbidden word occurring only in a comment.

## Recommendation

Do not spend a strict-check run on a cosmetic rewrite of either candidate. Neither supplies the full task proof, and the current task row does not permit a reduction. Useful restricted lemmas can be preserved as research with source attribution; they cannot be relabeled as the posted theorem.

Adjacent source hashes/URLs, lexical audit, selected task record, retrieval metadata, and PR metadata preserve the evidence. The third-party draft source bodies are intentionally omitted. No contributor's source or PR was modified.
