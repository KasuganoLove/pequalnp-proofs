# PR14022: officially merged and checked

Read-only audit on 2026-11-25, 12:27–12:37 UTC. No lease allocation, renewal, release, PR edit, comment, workflow action, or proof compilation was performed by this audit.

## Final verified status at 12:37 UTC

PR14022 was merged upstream at **12:30:48 UTC**, merge commit `1fc91c4a3a59d36d4c1490dcd945a5449ead499f`. The public desk snapshot updated12:35:52.311, retrieved12:36:51, lists **L-meta-10221 as checked** with file SHA256 `9f4dcb5a1635683d7bc7ff3e4d05f307ba8b7aa8f1ff538901f726b32239f3bc`. The merge commit and current upstream main both contain exactly the submitted Git blob `1f0d7cf983743bb6e5f588a28908f2d0682d4389` (109453 bytes). The step API now returns not_open; the separate checked-table entry establishes the reason in this case.

The exact statement proved is that the 5×5 Boolean matrix with mask15768118 has no AND/OR representation of at most10 gates on the required one-left/one-right inputs. This is the negative twin of L-meta-10220. The file attributes its proof mechanism to tb-16's already checked L-meta-9195; this submission specializes that mechanism to this matrix.

**Precise outcome:** officially merged and recorded checked. The comments API still returns no comments, so no explicit comment containing ACCEPTED was observed. Do not invent an official run identifier, constant count, or textual verdict. This is a completed official proof submission, regardless of the advisory workflow's earlier approval state.

No registration repair, new lease, replacement PR, or edit to the recorded file is needed. Preserve the proof and provenance. See `merged-final-status.json` and `merged-selected-rows.json` for the final evidence.

## Earlier registration evidence, 12:27–12:33 UTC

Official upstream PR https://github.com/open-goat/pequalnp-proofs/pull/14022 exists for the user's `L-meta-10221` proof, at head `bc59c2be036e28415543dcb42dd8da78d4439163`. The fresh public desk is now consistent with GitHub: its 12:26:52.692 snapshot lists `pr_open: 1` and `pr_numbers: [14022]`. At 12:29:28, the step endpoint returns `pr_open`, says the PR is waiting for its check, and directs the worker to ask for another open step. Thus the earlier no-PR display does not justify inventing a registration operation or creating a duplicate PR.

No authoritative verdict was observed in the fresh PR comments. The advisory workflow has `action_required` and no jobs. The API response alone did not identify its cause. The parent subsequently reviewed the actual GitHub page in the user's local Chrome and reported that GitHub explicitly requires a maintainer's approval for this workflow. That observation explains the advisory workflow's wait; it does not establish why the separate authoritative checker has not yet commented. No browser action or remote change was performed by this audit.

## Documented flow

The fresh https://pequalnp.com/join.txt (retrieved 12:27:11 UTC, SHA256 `2a4fd84354251825cf5bf5c44b736444c087f1926c9b432036b88326140277a1`) documents a new option for a checked proof of an open task: `tools/pnp.sh next --proof-of <step>`. The corresponding explicit query is `gap=<step id>&have=proof` on the existing next endpoint, alongside the owner's handle. The text allows this when another agent holds the open task and describes the race terms. It does not explicitly extend this route to a task with an existing pending PR.

The current `tools/pnp.sh`, Git blob `26e3f7b7d7320c872e89a3c2bbbf3b01ebdb6766`, confirms that argument mapping. Its submit flow is: check status, prepare exactly one added file, read the stored task lease, renew immediately before submission, create the GitHub PR, then release the lease with `reason=submitted`. There is no separate registration endpoint in this public script or join instructions. The script's `still_open` check permits only `open` and `leased`, stopping on `pr_open`.

Join lines150–154 and the script put a `Lease:` line into the PR body to link the submission to the lease's frozen terms. PR14022's current body does not contain this line. The public documents do not state a retroactive correction requirement, nor that absence of the line prevents proof checking. Current CONTRIBUTING.md still says the proof is judged from the file. Because the desk has now recognized PR14022, the missing line must not be asserted as the cause of a failed or stalled check.

The helper reads the lease identifier from its local per-task state file. No public account/step read endpoint for recovering another session's lease identifier is documented. The step status response contains no lease identifier. The source path `site/desk/src/index.js`, mentioned by the helper, was not present in the public upstream repository (404); no server behavior is inferred from that missing source.

## Exact task and file match

The current row names `lean/PEqualNP/Outside/L_meta_10221.lean` and theorem `PEqualNP.Outside.L_meta_10221`, with project imports `PEqualNP.Defs` and `PEqualNP.Defs.Represents`. The submitted file uses exactly those project imports plus `Mathlib.Tactic`. Its final theorem is the current mask15768118, Fin5 representation-at-most10 negation. Tokens match after ignoring whitespace and the posted redundant outer parentheses under negation.

At 12:31:41 UTC the local source copy exactly matches the PR Git blob `1f0d7cf983743bb6e5f588a28908f2d0682d4389`: 109453 bytes, SHA256 `9f4dcb5a1635683d7bc7ff3e4d05f307ba8b7aa8f1ff538901f726b32239f3bc`. An earlier downloaded copy had one extra final LF; the current checked copy does not. The audit did not edit the proof.

## Historical protocol recommendation before the merge was observed

The earlier recommendation was to continue tracking the existing official PR and its authoritative comment. If the originating Codex has its valid task record and the owner chooses to add the documented Lease line, that record is the source; do not invent or publicly search for a lease identifier. Nothing in the retrieved protocol requires a new allocation or a second PR to register the already recognized submission. A new proof-of allocation solely to backfill this pending PR is not an explicitly documented workflow.

The protocol audit itself performed no local proof compilation. The final verified result above supersedes the earlier pending status: merged and checked are now directly observed. An explicit ACCEPTED comment remains unobserved. The parent agent owns any broader stage-completion statement, local validation, browser interaction, lease decisions, and remote changes.

## Source URLs

- https://pequalnp.com/join.txt
- https://github.com/open-goat/pequalnp-proofs/blob/main/tools/pnp.sh
- https://github.com/open-goat/pequalnp-proofs/blob/main/CONTRIBUTING.md
- https://data.pequalnp.com/data/desk/gaps.json
- https://pequalnp.com/desk/step?gap=L-meta-10221
- https://github.com/open-goat/pequalnp-proofs/pull/14022
- https://github.com/KasuganoLove/pequalnp-proofs/blob/bc59c2be036e28415543dcb42dd8da78d4439163/lean/PEqualNP/Outside/L_meta_10221.lean
