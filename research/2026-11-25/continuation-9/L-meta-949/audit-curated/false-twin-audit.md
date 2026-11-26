# L949 is contradicted by the already checked L950

Read-only audit on 2026-11-25, for the parent's live L949 allocation. No lease,
PR, comment, remote write, Lean source edit, or compilation was performed here.

## Decisive finding

L949 asks for a six-vertex graph `G` and a well-formed `AndCountCircuit 6` which
fits the maximal-independent-set / one-vertex-augmentation partial function,
but has no biclique cover of `G` with at most `C.size` bicliques.

The already checked theorem `PEqualNP.Outside.L_meta_950` states that **every**
such graph and circuit has exactly such a biclique cover. The circuit model,
partial-function tests, bound direction, and cover definition are the same.
In particular, L950 does not require full edge-function computation, internal
cleanliness, disjoint gate sides, or a C4-free graph.

The logical contradiction is the following direct application, with the goal
being the negation of the exact public L949 statement:

```lean
rintro ⟨G, C, hWellFormed, hPartial, hNoCover⟩
exact hNoCover (PEqualNP.Outside.L_meta_950 G C ⟨hWellFormed, hPartial⟩)
```

This snippet documents the exact implication of the existing checked theorem;
it was not compiled as a new proof in this audit. There is no mathematically
valid positive witness or satisfiable positive reduction to seek for L949,
assuming the checked library is consistent.

## Official evidence

- [Immutable public L950 record](https://data.pequalnp.com/data/lemma/L-meta-950.9e3e68e9e0ad.json): status `checked`, contributor `sanchan`.
- Recorded merge time: **2026-11-23T19:56:33.901Z**.
- Recorded PR: [#1995](https://github.com/brilliant-hq/pequalnp-proofs/pull/1995).
- Recorded authoritative run: [45247366970](https://github.com/brilliant-hq/pequalnp-proofs/actions/runs/45247366970), runner ID `run-024810`.
- The artifact still uses the repository's previous `brilliant-hq` owner in its
  historical URLs; current canonical owner is `open-goat`.
- Source: [L_meta_950.lean at commit351fec](https://github.com/open-goat/pequalnp-proofs/blob/351fecac1b6c1fba40b6e45be9bf0058aa141b8a/lean/PEqualNP/Outside/L_meta_950.lean).
- Source size: **193,409 bytes**.
- Source SHA256: `0b7e2f524d8cf838ed8e00ccb86224d0fa9ba587dfb9e5f750c1325d73a4cc3a`.

That SHA256 matches both the local upstream file and the current desk's checked
artifact record. The file begins with `import Mathlib` and `import PEqualNP.Defs`.
Its final theorem proves a biclique cover with `min C.size 4` bicliques: arbitrary
six-vertex graphs have a four-biclique cover, while circuits of size zero through
three are handled by explicit structural arguments.

## Current desk conflict

The [public desk snapshot](https://data.pequalnp.com/data/desk/gaps.json) updated
**2026-11-25T08:04:35.343Z** simultaneously lists:

| Row | Status |
|---|---|
| L949 | Posted, no open PR, no existing reductions, no `kind` field, reductions allowed. |
| L950 | Checked with the source hash above. |

Neither row appears in that snapshot's withdrawn table. A contemporaneous
read-only [L949 step query](https://pequalnp.com/desk/step?gap=L-meta-949) reports
two holders; this audit did not access any private lease identifier.

The existence of a live L949 allocation therefore does not indicate that its
mathematical alternative remains unresolved. The already accepted opposite
statement is decisive.

## Documented submission route

Fresh [join.txt](https://pequalnp.com/join.txt), saved as `join-current.txt`, says
that a false statement is handled by proving its **negated twin**, as an ordinary
proof PR. Here that twin is L950, and it is already checked.

The repository's `.github/scripts/outside-guard.mjs` also determines submission
kind from the desk row: an absent `kind` field means `check`; only a row posted
with `kind: refute` can be judged as a negation of its recorded statement. L949
has no `kind` field. Sending a negation under the L949 proof filename would
therefore not follow its current advertised check mode. A positive reduction
would not repair the false mathematical target.

The documented release reason `statement_seems_false` is applicable. The parent
owns any release or subsequent allocation; this audit took no such action.

## Related existing library results

These sources were read to avoid duplicate search work:

| Result | Actual scope |
|---|---|
| L906 | Exact partial AND-count minima for two disjoint triangles (4), a five-cycle (3), and an explicit seven-vertex graph (3). Its seven-vertex statement by itself does not give the corresponding biclique-cover lower bound. |
| L950 | Universal six-vertex partial AND-count-to-biclique-cover theorem, contradicting L949. |
| L958 / L962 | C4-free partial-function AND-count lower bounds at vertex-cover thresholds4 /5. |
| L635 | Petersen's partial-function AND-count minimum is exactly6, without an internal cleanliness premise. |
| L217 | Generic C4-free full-function AND-count bound for thresholds `t ≤ 5`; this threshold restriction matters. |

The first useful audit outcome is the completed opposite theorem, not a new
finite-search cut. The separate 156-graph synthesis was paused when this evidence
was found.

## Saved records

`public-950.json` is the immutable official artifact record.
`selected-current-status.json` preserves only the relevant public rows from the
fresh desk snapshot. `current-step-949.json` preserves the read-only public step
status. These files contain no private lease IDs or account credentials.
