# L-meta-2600: strengthened ledger and exact remaining obstacle

## Status and target

This is a bounded mathematical audit for the live task L-meta-2600. It does not prove the task, construct a counterexample, or make an official submission. No SAT, Lean compilation, or strict checker was run for this audit. `check_obstructions.py` performs two small ordinary-computation checks described below.

The exact public statement asks for a lower bound of **63** gates for strict binary AND/OR circuits computing the full 26-input PG(2,3) edge function. Operands must be distinct earlier wires. It has no assumption that raw inputs have multiple readers, no cleanliness assumption, and no star-profile assumption.

The point-line convention is `p = l + d` for `d ∈ {0,1,3,9}`. The earlier L-meta-650 ledger uses `p + l ∈ {0,1,3,9}`. A line permutation `l ↦ -l` gives the graph isomorphism, but a formal composition needs this permutation bridge explicitly.

## What the smaller counterexample budget changes

In a least TopForm representative write

```text
t = |tops \ centreless|, c = |centreless|,
j = |junk|, o = |orN \ lam|, u = |Ustar|,
e = 2c + j + o.
```

The checked counting and cover estimates give

```text
52 + t + e <= size + u + 1,
52 <= 4t + u.
```

For a hypothetical counterexample to L2600, `size <= 62`; hence

```text
t + e <= 11 + u,
4e + 8 <= 5u.
```

The earlier size-at-most-63 investigation had `4e+4 <= 5u`. The new budget strengthens the constant by four, but it does not close the ledger.

Existing zero-junk and single-junk results leave `j >= 2`. The earlier transfer argument excludes `c=o=0`; the ordinary-Lean checked single-exception theorem excludes `c=0,o=1` because it gives `u<=1`. The previously recorded single-centreless argument would exclude `c=1,o=0`, but that composition was not formalized here.

An explicit surviving scalar tuple is

```text
(t,c,j,o,u,size) = (12,0,2,2,5,62).
```

It gives `68 <= 68`, `52 <= 53`, and `24 <= 25` in the three relevant inequalities. Thus arithmetic alone cannot discharge the task.

`pending-case.json` additionally realizes the covered/uncovered edge counts geometrically in the task's exact labels: take the twelve point centres 1 through 12, omit all four edges at point 0 and the edge `(1,13)`, and retain the remaining 47 edges. They form twelve stars, eleven of size four and one of size three. Their standard partial implementation costs 35 preparation ORs, 12 ANDs, and 11 output ORs, for 58 gates. Four hypothetical gates remain within 62. This is **not** a construction completing the missing five edges; the semantic completion is precisely unproved.

## Why nonempty raw sides do not give a vertex cover

The inference `centreless=∅` plus positive-edge-to-top trace implies that chosen raw centres cover every edge is invalid without an additional argument. A small exact control uses the matching function `F=ab OR cd`:

```text
H = c AND (a OR d)
J = d AND (b OR c)
F = (a OR H) AND (b OR J).
```

The expansion is exactly `ab OR cd`. H and J are dirty AND gates. The final AND is the only top, its raw sides are `{a}` and `{b}`, and TopForm holds. It fires on the edge `cd` even when both raw centres are false. Consequently neither chosen centre covers all positive edges, despite `centreless=∅`, the raw-side shape property, and positive-edge-to-top trace.

`check_obstructions.py` checks all 16 assignments, identifies the dirty gates and top, computes raw OR supports and cones, and verifies these claims. Its result is `raw-guard-control.json`. The circuit has seven gates while the matching has a three-gate implementation, so it is **not minimum**. This example does not refute a theorem with a new substantive minimality argument; it shows why `t>=13` cannot simply be inferred from the presently available shape/trace premises.

## One possible refinement, still a paper argument

For `c=0,o=2`, suppose there is exactly one mixing OR m and one other exceptional OR d. A possible extension of the existing single-mixer transfer proof is to partition uncovered-edge tests according to a chosen true operand of d. Tests where d is false can be assigned arbitrarily. Within each class, if d is true on all tests, one fixed operand is true on all tests, so the common-truth induction can pass through d by that operand. All remaining earlier ORs are lambda gates; an earlier clean OR firing on an uncovered edge would contradict the fact that m is the unique mixer.

The existing unique-mixer routing and negative-cross argument should then limit each class to one uncovered edge, giving `u<=2`. This avoids the unsupported assumption that the other exceptional OR has a nonempty raw support. **The composition has not been formalized or independently reviewed as a complete proof here.** It does not cover two mixing ORs, and the surviving numerical tuple does not force the mixing set to have size one.

## The five-deletions route remains separate

R_meta_2600_1 combines two hypotheses: every circuit correct when a chosen vertex is false has at least 58 gates, and some vertex in every correct circuit of at most 62 gates makes at least five gates simultaneously constant or equal to earlier wires. Its combination proof does not prove either premise.

After liveness pruning, counting raw operand occurrences gives at most `size+1 <= 63`, so at least one of the 26 essential inputs has at most two occurrences. This is not by itself a five-deletions argument. In the ordinary 64-gate point-star implementation, a point-centre input has one raw occurrence; fixing it false only deletes its star AND and one combining OR by elementary constant propagation. The global size-at-most-62 hypothesis would need to supply the missing structural step. No such step was established here.

The existing desk snapshot updated at 2026-11-25 11:23:56.820 UTC identifies the two exact children as L-meta-4043 (minusVertex) and L-meta-4045 (freeFive). Both were in gaps with pr_open=0 and an empty PR list, each with one live reduction. The canonical-first-gate residual L-meta-6230 and star-profile normalization L-meta-8225 also had no PR in that snapshot. The selected records and source hash are saved in child-status-snapshot.json. This was an existing snapshot, not a fresh network retrieval; a separate audit agent was asked to perform a narrow update. No current completion state is inferred beyond the recorded timestamp.

## Sources and reproduction

The ledger and existing proof scope come from the checked upstream sources L-meta-7862, L-meta-9047, L-meta-8725, L-meta-8791 and the earlier local single-exception module `Pnp650SingleMixer.lean`. The latter is an ordinary-Lean checked local lemma with explicit shape and trace premises, not an official full PG3 lower bound. The transfer APIs are the attributed generic slice of upstream L-meta-5228.

Run `python check_obstructions.py` in any ordinary Python 3 environment to regenerate the two small JSON controls. They do not require private lease information or remote access. All statements about hypothetical completion remain explicitly marked as unproved.
