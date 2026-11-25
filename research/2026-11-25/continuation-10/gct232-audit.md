# L-gct-232: live task, no currently allowed reduction

Read-only follow-up on 2026-11-25. No lease operation or remote write.

## Exact opposite and present state

The opposite of L-gct-232 is **L-gct-231**, not233.

- L231 asserts existence of a three-dimensional complex subspace of symmetric
  4×4 matrices `t` such that `permanent(J + t) = 24` throughout the subspace.
- L232 is the literal negation of that existence statement.

The public desk snapshot updated08:22:08 UTC lists both as posted, depth0, with
no open PR and no existing reductions. Neither is checked or withdrawn. There
is no L-gct-233 row in the examined posted/checked/withdrawn records.

Read-only live queries at **08:29:27 UTC**, with `Cache-Control: no-store`, show
both231 and232 leased with one holder each:

- <https://pequalnp.com/desk/step?gap=L-gct-231>
- <https://pequalnp.com/desk/step?gap=L-gct-232>

Those public responses do not identify the holders. Exact GitHub searches for
`"L-gct-231"` and `"L-gct-232"` returned no matching PRs.

## A reduction PR is not permitted by the current row

L232 has **no `reductions: true` field**. The current public guard explicitly
rejects a reduction when `g.reductions !== true`; omission therefore means it
is not open to reduction. The same requirement is stated in current join.txt.
Holding a live L232 lease does not by itself enable a cut.

Sources:

- <https://data.pequalnp.com/data/desk/gaps.json>
- <https://raw.githubusercontent.com/open-goat/pequalnp-proofs/main/.github/scripts/outside-guard.mjs>
- <https://pequalnp.com/join.txt>

The parent owns any subsequent proof/submission or lease decision. No R_gct_232
file or altered task metadata was produced.

## Related checked results and their limits

The current checked table was compared with the existing local GCT sources.
All six files below match their current official checked source hashes exactly;
the signatures and hashes are preserved in `gct-related.json`.

| Result | Relevant statement | Limitation for232 |
|---|---|---|
| L214 | A 4×4 coefficient-vanishing space has dimension at most6. | Does not give the required symmetric dimension bound below3. |
| L216 | Dimension at most3 if every row and column sum vanishes, together with the quadratic/cubic/quartic coefficients. | Symmetry does not itself imply those row/column hypotheses; even the conclusion permits dimension3. |
| L217 | Dimension at most5 with zero row sums and the remaining coefficient conditions. | Neither the required hypotheses nor a strong enough bound follow directly. |
| L222 | An explicit first-row/first-column cross family keeps the permanent at24 when sums of `a` and `b` vanish and `a 0 = 0`. | Its symmetric specialization forces `a = b` on the nonzero coordinates and `b 0 = 0`, leaving two free dimensions, not three. |
| L224 | No two-dimensional circulant family at the 6×6 all-ones base point. | Different dimension and a special circulant model. |
| L226 | No four-dimensional level space for3×3 matrices over `ZMod5`. | Different field, matrix size, and dimension threshold. |

No checked opposite231 or immediately applicable symmetric4×4 dimension≤2 result
was found in this bounded current inventory. This audit did not start a new
mathematical proof or compile any Lean code.
