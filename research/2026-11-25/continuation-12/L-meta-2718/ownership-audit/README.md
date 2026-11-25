# Bounded scope and reuse audit for L-meta-2718

Work was authorized under the parent's live L-meta-2718 lease obtained2026-11-25 at09:59:14 UTC. The parent handles lease operations and official submission. No official proof or new reduction is claimed here.

## Exact scope

The task assumes a fan-in-at-most-two monotone26-input circuit of at most63 gates. Its output must accept the52 incident point/line pairs of the order-three plane with difference set `{0,1,3,9}` and reject only the degenerate maximal false inputs. It asks for another circuit satisfying the same promise and budget whose output has syntactic additive degree at most1 on the point side or the line side.

`HasLineDegree` is the exact definition in `PEqualNP/Defs/LineDegree.lean`: AND sums operand degrees, with repeated inputs counted repeatedly; OR takes their maximum. It is the degree of the output wire, not a semantic polynomial degree and not a statement about every internal AND being sound.

An exact Python enumeration found704 maximal false inputs. The236 degenerate inputs used in this task have point/line cardinality types:

| Points | Lines | Count |
|---|---|---|
|0|13|1|
|1|9|13|
|2|6|78|
|3|3|52|
|6|2|78|
|9|1|13|
|13|0|1|

The omitted468 inputs have types `(3,4)` and `(4,3)`,234 of each. Our earlier2343 quadrangle-negative family belongs to the omitted `(4,3)` class. Its output-rejection premise therefore cannot be imported into2718.

`enumerate_families.py` reproduces the data. The new constructive attempt's independent verifier separately evaluates the literal quantified predicate on all8192 point subsets; it does not reuse the preparer's bitmask maximality test.

## Sibling2716 is accepted, although not merged

Fresh GitHub metadata and comments were retrieved for [official PR4938](https://github.com/open-goat/pequalnp-proofs/pull/4938). The PR remains open and unmerged, so its file is absent from upstreammain. It nevertheless received **ACCEPTED, checker exit0** on2026-11-24 at18:24:06 UTC:

- [Verdict comment7140592888](https://github.com/open-goat/pequalnp-proofs/pull/4938#issuecomment-7140592888)
- [Runner45456538469](https://github.com/open-goat/pequalnp-proofs/actions/runs/45456538469)
- Accepted head `1e1b84679544b083d3e240bac25ae6be219b8dcd` in `jackryan225/pequalnp-proofs`.

Its final theorem exactly matches the public2716 statement in the09:04:37 desk snapshot after whitespace normalization. It rules out the promised≤63 circuit with line-side degree≤1. The parent reduction uses plane duality for the other side. Consequently the desired2718 normalization is a substantive nonexistence step, not a routine syntactic cleanup. This audit does not re-run the accepted proof or assert that the PR is merged.

The PR author credits the accepted `L_meta_1500` proof as the basis of the adaptation. The immutable source metadata preserves that provenance. This compact publication omits third-party source bodies and excerpts; SOURCE_PROVENANCE.json and STAGING.json retain their URLs and hashes.

## Existing cut routes and remaining obligations

`R_meta_2718_1` splits off the finite classification of nondegenerate maximal inputs, then requires an unrestricted64-gate lower bound on all maximal inputs and rejection of the omitted triangle/quadrangle rows. Our cardinality enumeration is consistent with its geometric premise, but neither output rejection nor the unrestricted lower bound follows from the2718 premise.

`R_meta_2718_236` minimizes circuit size within the promised class and uses physical gate erasure. Its substantive premise asserts the existence of a safe redirection whenever both side-degrees exceed1. Generic erasure semantics do not supply that existence assertion.

[PR12102](https://github.com/open-goat/pequalnp-proofs/pull/12102), merged at09:28:46 UTC, supplies `R_meta_2718_106`. It minimizes the number of binary gates, then asks for safe AND bypass when both degrees exceed2. Its low-degree branch uses exactness at degree≤2 and a64-gate lower bound for exact circuits of degree≤2. The PR description reports separate local proofs for the elementary bypass and exactness premises, while identifying safe-bypass existence and the lower bound as remaining work. That description is not itself fresh proof-status evidence for every generated child.

[PR12812](https://github.com/open-goat/pequalnp-proofs/pull/12812) was a normalization-only cut and closed unmerged at09:40:33 UTC. None of these cuts supplies the full conclusion by itself.

## What the2343 helpers do provide

The compiled generic `Pnp2343CleanCost.plane_bound_of_negative_family` applies if **every internal AND** rejects a negative family covering every nonedge pair. It cannot replace that premise with output rejection.

A particularly small family suffices here: all points, all lines, and for each of the13 points, that point together with all9 nonincident lines. These15 inputs are all among the posted236 degenerate maximal negatives and cover every nonedge pair, including diagonal singleton pairs. The finite coverage was independently enumerated in `fifteen-negative-cover.json`.

Combining that coverage with the existing generic conditional bound shows the precise obstacle: any hypothetical promised≤63 circuit must contain an AND firing on one of those15 negative inputs, while a later portion of the circuit suppresses the output. This has not been promoted to a new Lean theorem here and does not establish the required safe bypass.

## Constructive test

The sibling directory `../search63/` contains the parent's authorized single300-second stochastic search for a concrete63-gate circuit satisfying exactly the posted finite promise. Such a witness, combined with accepted2716 and the dual-side bridge, would support the negated-twin route. Failure to find a witness is not a lower-bound proof.

## Fresh10:11 child-status check

The parent supplied a desk snapshot updated2026-11-25 at10:11:03.816 UTC. Only selected rows are retained in `fresh-child-rows.json`.

| Route | Obligation | Fresh state | PRs |
|---|---|---|---|
|Sibling2716|No promised63-gate line-degree1 circuit|Posted, with official ACCEPTED unmerged proof|4938|
|R2718_1|5739: finite geometry classification|Checked|Source hash verified|
|R2718_1|5741: all-maximal-input64-gate bound|Posted|None listed|
|R2718_1|5743: omitted triangle/quadrangle rejection|Posted|None listed|
|R2718_236|8845: generic erase-gate semantics|Checked|Source hash verified|
|R2718_236|8847: safe redirection exists at high degree|Posted|None listed|

The fetched5739 and8845 sources match the fresh desk's SHA256 values exactly. The snapshot lists the newly merged R2718_106 as a live reduction, but no generated child rows for that route were identified through its unlock relationship or the degree-two statement scan. Their status is not inferred. No completed full2718 route was found.

The bounded constructive run also found no valid witness. Its independent final check misses exactly incident pair(point0,line4), while rejecting all236 required negatives. This invalid circuit does not refute2718.
