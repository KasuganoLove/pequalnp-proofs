# L-meta-9815: bounded restriction and local-star audit

2026-11-25 UTC. This work was performed under the root agent's live assignment to L-meta-9815. The parent manages its eventual closure. This directory contains ordinary finite computations and a source audit, **not a new Lean proof, a 24-gate circuit, or an official submission**.

## Exact task and current public evidence

The target is the negation of `HasCircuitSize 14 F 24`, where `F` is the 19-edge function in the adjacent `gap.json`. `HasCircuitSize` permits AND, OR and NOT with fan-in at most two and counts every gate, including NOT. The exact positive twin is **L-meta-9813**, not the numerically adjacent 9814. The official desk snapshot dated 14:30:11.706 UTC, retrieved at 14:31:16.735970 UTC, lists both twins as open with no PR numbers. An exact-ID GitHub search also returned no matching 9815 PR during this audit. These are timestamped observations, not ongoing status guarantees.

Official sources:
- Task desk: https://data.pequalnp.com/data/desk/gaps.json
- Task status: https://pequalnp.com/desk/step?gap=L-meta-9815
- Repository base: https://github.com/open-goat/pequalnp-proofs/tree/57164c3618362178843e2ea37bd01613f4037ae2

## Explicit 25-gate control

`baseline-25.json` gives a completely explicit circuit: seven left-centered stars followed by their OR. It has **7 AND gates and 18 OR gates**. The independent scalar evaluator checks all **16,384** assignments against the literal posted edge list and finds zero errors. This is ordinary computation, not a Lean certificate.

The graph has degree two at vertices 0, 2, 7 and 12, and degree three elsewhere. Exhaustive subset enumeration finds cover number seven, with exactly two minimum covers: the two bipartition sides. Pairwise neighborhoods have at most one common vertex, so the graph has no C4. The standard star construction therefore gives 19 + 7 - 1 = 25 gates. This calculation does not assert that every unrestricted circuit admits such a construction without increasing its size.

## Restriction recursion: useful diagnostic, insufficient bound

`restriction_dp.py --checked-cores` visits 5,599 induced graphs after removing isolated vertices. It obtains only **20**, versus the required lower bound 25. This is a finite diagnostic of the implemented rules, not a formally verified new lower bound and not a claim that every possible elimination argument is limited to 20.

The implemented source-level rules are:

1. An essential input fixed to a nonconstant cofactor saves at least one total gate (`Helpers/Elim.gate_elim`).
2. For an essential input whose two cofactors are nonconstant, some polarity saves two gates (`L314_aux.p1b` / the relabeled version `p1d`).
3. Under the checked no-funnel and nonconstant-cofactor conditions, some variable has one of the saving profiles (3,3), (4,2), (2,4) (`L314_aux.Readers.fanout_step`). The recursion takes the minimum over the possible variables and profiles; it does not choose the most favorable existential branch.
4. Independent OR variables add one gate each to a nonconstant residual graph function (`Helpers/PadOr.pad_down`). If no graph edge remains, the OR of d inputs has d-1 gates.
5. Exact forest, cycle, and long-thread bounds from L104, L106 and L204.
6. Fifty-eight syntactically exact small-graph clauses from 21 currently checked source files. Their immutable file hashes and exact clause extraction were independently checked by `verify_checked_core_catalog.py`. The extraction covers only the explicit canonical clauses retained in the catalog; helper-defined graphs and other unrecognized theorem formats were not exhaustively mined.

Every rule above counts total gates. In particular, the output 20 cannot be reinterpreted as twenty binary gates plus the number of NOT gates.

The no-funnel test compares the four pinned cofactors as canonical constant/linear/quadratic monotone functions. A pair is a funnel precisely when three of those four functions coincide. The source proof still needs to be instantiated and checked in Lean before this diagnostic could become a formal certificate; no such instantiation was attempted here.

## Local replacement obstruction

`verify_baseline_and_substars.py` enumerates subsets of one to four centers from either side of the bipartition. For all **14 one-star, 42 two-star, and 70 three-star** standalone subfunctions, an existing checked bound reaches the standard star cost. Forests use L104. A nonforest with at most three centers reduces by pendant-variable restrictions to C6, whose unrestricted minimum is eight gates (L106; also an explicit clause in L-meta-927). Each pendant deletion is applied while the cyclic residual is nonconstant.

This rules out saving one gate by computing just one of those standalone subfunctions more cheaply and then inserting it unchanged into the standard construction. It does **not** rule out global sharing between the selected and unselected stars, alternate intermediate functions, or an unrelated circuit.

For four-star subfunctions, only 22 of 70 cases are closed by the implemented forest/cycle/theta333 routes. Forty-eight remain unresolved by these routes: 38 leave a six-cycle after pendant stripping but lose an additional covering contribution, eight leave a nine-vertex ten-edge theta core, and two leave the ten-vertex twelve-edge subdivision of K4. These labels are finite structural diagnostics, not lower bounds for the residual cases. L-meta-3516's known subdivision-of-K4 result is monotone and must not be used as an unrestricted AND/OR/NOT bound.

## Reproduction

Use Python 3 with its standard library. Put this directory one level below the exact task `gap.json`:

```sh
python independent/verify_baseline_and_substars.py
python independent/verify_checked_core_catalog.py /path/to/pequalnp-proofs
python independent/restriction_dp.py --checked-cores
```

The second command requires the pinned public repository files referenced by `checked-source-status.json`, with byte hashes matching the catalog. No network call, package installation, solver, native binary or Lean compilation is part of these commands.

`source-references.json` records the primary proof paths, immutable URLs and SHA256 hashes. The public archive omits the full downloaded desk, third-party Lean sources, regenerated per-subset tables, and the earlier exploratory recursion output. No lease IDs or private authentication data are included.
