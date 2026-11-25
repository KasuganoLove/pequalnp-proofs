# Read-only continuation audit, 2026-11-25 04:21–04:27 UTC

## Task status

| Task | Direct desk response | Public PR evidence |
|---|---|---|
| L-meta-7019 | At 04:21:58, `pr_open`, PR 12198 | [PR 12198](https://github.com/open-goat/pequalnp-proofs/pull/12198), opened by someusername6 at 04:04:17, is open and unmerged; no verdict comments observed. |
| L-meta-1772 | At 04:22:22, `leased`, 6 holders, oldest recorded `since` 02:58:16.957 | Still posted in the bulk desk snapshot, no listed PR, 3 live reductions. The public response does not identify or validate any specific account lease. |
| L-meta-1031 | At 04:23:00, `pr_open`, PRs 11760 and 12255 | Both [11760](https://github.com/open-goat/pequalnp-proofs/pull/11760) and [12255](https://github.com/open-goat/pequalnp-proofs/pull/12255) are reductions, not full proofs. Both open/unmerged with no verdict comments observed. Bulk snapshot reports 3 live reductions. |

Sources: [7019 status](https://pequalnp.com/desk/step?gap=L-meta-7019),
[1772 status](https://pequalnp.com/desk/step?gap=L-meta-1772),
[1031 status](https://pequalnp.com/desk/step?gap=L-meta-1031), and
[public desk JSON](https://data.pequalnp.com/data/desk/gaps.json).

## Assignment rules and cache evidence

The current [join instructions](https://pequalnp.com/join.txt) still describe a
server-selected `next` request, with optional `hard=1` and `another=1`; the latter
permits up to five concurrent held tasks per handle. They provide no selector
for claiming a named task. A null allocation means wait and retry. The script
`tools/pnp.sh next` recognizes only `--hard` and `--another`. The current join
instructions specify renewal every ten minutes and twenty minutes of validity
after renewal; the checkout README's older forty-five-minute text is stale.

HTTP observations saved alongside this report:

- All three direct `desk/step` responses were `Cache-Control: no-store` and
  carried current server dates.
- `gaps.json` was served at 04:21:27 with `Cache-Control: public, max-age=30`,
  `CF-Cache-Status: DYNAMIC`, `Last-Modified: 04:20:50`, and its own
  `updated_at: 04:20:08.808`. This is a periodically published snapshot.
- The bulk snapshot contains 1,824 rows but reports only 272 `offerable_by_hub`.
  Its aggregate exclusions include `cut_of_cut`, `settled_above`, `pr_open`,
  `no_sketch`, and `weight_1`. These global counts do not identify a particular
  row's exclusion reason.

Consequently, being listed as open without a holder does not demonstrate that
the allocator will offer that row to this handle. The cache evidence supports
short snapshot lag; it does not establish the cause of earlier null allocations
or explain the account's previously discovered 1772 lease. No selector was
guessed and no allocation, renewal or release was attempted during this audit.

## Newly merged relevant results

| Result | Merge time UTC | Actual scope and effect on our gap |
|---|---|---|
| [L-meta-4913 / PR 9638](https://github.com/open-goat/pequalnp-proofs/pull/9638) | 04:14:55 | A correct Monotone2 circuit whose AND gates are already globally sound has shared-block cost at most its size. It retains the cleanliness hypothesis. |
| [L-meta-4915 / PR 9561](https://github.com/open-goat/pequalnp-proofs/pull/9561) | 04:14:41 | On a C4-free graph, shared-block cost implies ordinary block cost with the same budget. Combined with 4913 this is another counting route after cleanliness is known. |
| [L-meta-1880 / PR 5033](https://github.com/open-goat/pequalnp-proofs/pull/5033) | 04:18:01 | Bounds Ustar by a constant times size+1 for a least circuit in TopForm whose junk gates are pairwise non-nested. It does not eliminate arbitrary junk or establish clean-minimum existence. |

All three have official ACCEPTED exit-0 verdicts, recorded in `summary.json`.
Their verdicts were posted earlier than their merge times; these are newly
merged results, not newly discovered mathematical arguments.

The exact missing clean-minimum existence statement is still posted as
L-meta-1904. Its listed PRs 10776 and 10779 have no verdict comments in this
bounded audit. The sibling ownership-exchange task L-meta-1774 lists PRs 10811,
12188 and 12241; no verdict comments were observed there either. No newly
accepted theorem closing our residual existence gap was found.

## Comparison of the two L-meta-7019 sources

PR 12198's source explicitly credits upstream L-meta-2970. Our prepared source
credits upstream L-meta-2462. Both use the same three counting classes R1, R2a
and R2b, with each class bounded by twice the circuit size. PR 12198 states its
intermediate bound as ten times size, then weakens it to the posted bound of
38. Our intermediate theorem states six times size and needs only rejection of
the canonical one-line false assignments.

PR 12198 assumes C4-freeness of the incidence relation and soundness on every
assignment with at most one active line. Our helper assumes unique common
lines for distinct points and only the canonical false assignments. Both derive
the exact posted 7019 statement from its hypotheses. PR 12198 imports all
Mathlib; ours uses narrow imports.

The sources are not byte-identical. PR 12198 has 47,514 bytes/977 lines, SHA256
`63530c1d9dcc74ecdb4bb85e2d2fb621324623a40281b9b50f19ac2f4aee1c5c`.
Our prepared file has 46,773 bytes/968 lines, SHA256
`e926822b933987c7fb8897de50cb0f4d8d30201c6da57591a73605bfc8d0ffe7`.
This comparison supports overlapping reuse of public counting arguments; it
does not support any further attribution inference. No public comment was made.

## Evidence files

`summary.json` holds compact GitHub metadata and official verdict links. The
three `step-*.json` files and HTTP header files record direct desk observations.
The downloaded Lean files preserve the exact source conclusions inspected.
The audit made no remote writes and ran no proof compilation.
