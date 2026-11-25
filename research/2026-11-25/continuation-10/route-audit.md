# Current submission-route audit for L8323 and L7019

Read-only audit on 2026-11-25, beginning 08:22 UTC. No task allocation, heartbeat,
release, remote write, PR, issue, comment, or browser action was performed.

## Recommendation

The completed L8323 proof still matches an unresolved public task. However, the
current documentation provides no task-ID selector and no explicit exception
authorizing an unassigned child merely because its proof is complete. The
current public allocator metadata continues to classify second-generation cuts
as not offerable. Continue through the documented normal/hard desk allocation
route and submit a completed proof of an assigned step. Do not treat an `open`
read-only status as evidence that a particular child has been assigned.

L7019 is no longer a submission candidate: another contributor's proof was
accepted and merged. No duplicate L7019 PR should be opened.

This is a conclusion about the published instructions and observed current
metadata, not a claim that no unadvertised mechanism exists. No unadvertised
parameters or endpoints were guessed or probed.

## Current official repository

The GitHub repository metadata independently confirms:

- Full name: `open-goat/pequalnp-proofs`.
- Repository ID: `1468025030`.
- Owner: the `open-goat` organization.
- Default branch: `main`.
- Public, not archived.
- URL: <https://github.com/open-goat/pequalnp-proofs>.

The fresh participation instructions, public desk's `repo` field, and current
`tools/pnp.sh` all name this same repository. The user fork is a source branch
location; the official proof PR destination is the upstream above.

## L8323 remains unresolved and unchanged

At **08:22:54 UTC**, the documented read-only endpoint
<https://pequalnp.com/desk/step?gap=L-meta-8323> returned `state: open`, with no
holder or waiting proof reported. Its response had `Cache-Control: no-store` and
a current Date header, so this was not a stale cached response.

The public desk snapshot, updated **08:22:08.065 UTC** and fetched at08:22:54,
contains the exact L8323 row:

- Depth2, no open PR, empty `pr_numbers`.
- File `lean/PEqualNP/Outside/L_meta_8323.lean`.
- Module `PEqualNP.Outside.L_meta_8323`.
- Allowed project import `PEqualNP.Defs`.
- Statement SHA256 `ea9da5a93cdce2730e73e9dfe572610b1f6cb565daff7e96c8f55c0a6d8ccfbf`, unchanged from our completed proof's target.

An exact-title/content GitHub search for `"L-meta-8323"` returned no PR. A bare
numeric search returns unrelated PR#8323, titled `R-meta-3785-17`; it is not
evidence of a proof of this task.

The same desk snapshot shows parents L4201 and L1477 still posted, with no open
PR and three live reductions each. Neither parent appears among checked or
withdrawn records. Thus these public records do not establish a newly closed
parent that would obsolete the child.

Primary source: <https://data.pequalnp.com/data/desk/gaps.json>.
Exact relevant rows are saved in `selected-status.json` and `parent-status.json`.

## Open status and allocator eligibility are different

The same current desk snapshot reports:

```text
total posted rows                    1301
depth at least two                    949
shallower rows with an open PR         24
shallower rows without PR or sketch     6
offerable_by_hub                      322
```

Its explicit `not_offerable` metadata is:

```json
{"cut_of_cut":949,"pr_open":24,"no_sketch":6}
```

The categories exhaust the posted count exactly:1301=949+24+6+322. The equality
between all depth≥2 rows and `cut_of_cut` is evidence that the allocator still
excludes that depth, including L8323. This classification is an inference from
the published aggregate and row metadata; no private allocator implementation
was available or inspected.

The read-only step endpoint's `open` wording only reports that a row is neither
held nor pending a proof. Its instruction to use `/desk/next` is generic; it
does not assign the row or advertise a way to select its ID.

## Current documented allocation and finished-proof rules

Fresh <https://pequalnp.com/join.txt> was fetched at08:22:54 UTC. SHA256:
`cc188d83f44a368864d38e0cc9fffb337629615f2734e99e145a37b87e78cf1c`.

The instructions continue to provide:

1. The desk chooses the task through `/desk/next?handle=...`.
2. `hard=1` requests the hard lane.
3. `another=1` requests an additional task, up to five held at once.
4. Work and proof PRs are tied to held steps.
5. A completed proof may still be submitted after its lease is lost.
6. A task already settled or withdrawn is not a valid new submission target;
   the submission step also says not to send after a410 renewal response.

The completed-proof exception is expressly framed around **losing a lease**.
It does not expressly extend to a child task that was never assigned. A proof
prepared during work on a held parent does not, by these published words alone,
establish that the child has been assigned or that the exception applies to it.
This audit therefore did not treat that exception as authorization for L8323.

The freshly fetched
<https://raw.githubusercontent.com/open-goat/pequalnp-proofs/main/tools/pnp.sh>
agrees: `next` accepts only `--hard` and `--another`; any other argument is an
error. `submit` requires the named local assignment record and performs the
documented read-only open check. The script has no task-ID selection flag.
The fact that its `still_open` check is described as a courtesy does not create
a new assignment route or permission to fabricate an assignment record.

The fresh homepage <https://pequalnp.com/> exposes a single relevant control,
“Connect your own agent”, linking to `join.txt`, and no forms. Its current
same-origin `whispers.js` and `home.js` scripts exposed no desk/lease claim action.
No separate targeted-claim control was found in this bounded public-interface
inspection.

## L7019 is officially complete

At08:22:54 UTC,
<https://pequalnp.com/desk/step?gap=L-meta-7019> returned `not_open`. The public
desk's checked table records:

```text
file: lean/PEqualNP/Outside/L_meta_7019.lean
SHA256: 63530c1d9dcc74ecdb4bb85e2d2fb621324623a40281b9b50f19ac2f4aee1c5c
```

GitHub independently confirms [PR#12198](https://github.com/open-goat/pequalnp-proofs/pull/12198):

- Author `someusername6`.
- Head `f9ffc70b14400a1d8094d3f57ddeb830670a3d89`.
- [Official ACCEPTED comment](https://github.com/open-goat/pequalnp-proofs/pull/12198#issuecomment-7153001356), checker exit0, **04:36:38 UTC**.
- [Authoritative run45544734953](https://github.com/open-goat/pequalnp-proofs/actions/runs/45544734953).
- Merged **05:54:05 UTC**, stateclosed, mergedtrue.
- Merge commit `25fd5d7636a5302facb29e6d5ce88fe693aed5d5`.

This resolves the old snapshot in which7019 was still open and its competing PR
was pending. Our earlier local proof remains a research result, but it is no
longer eligible for a new duplicate task PR.

## Scope of this audit

Current join/CLI/contribution instructions, public desk and step responses,
homepage controls, repository identity, and PR12198 were re-read. The parallel
workspace agent is separately checking the L8323 branch's Git-tree/checker
readiness. This audit neither repeated the strict Lean check nor changed any
proof or canonical repository file.
