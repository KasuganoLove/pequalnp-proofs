# L-meta-2733 conceptual audit

Status: paused on the root's report that renewal returned HTTP410 at 2026-11-25 09:20:24 UTC. No cause of that response is inferred. No new Lean module, solver run, strict check, lease operation, or remote write was performed by this worker. This note records only work completed before the pause.

## Exact scope

The task negates existence of a Monotone2 suffix of at most24 gates after two explicit binary AND/OR gates. The first gate reads two distinct raw inputs from14 variables; the second reads two distinct wires from the original14 plus the first gate. Its code must be minimal under graph automorphisms. Thus an existential witness gives a total circuit with at most26 gates.

Monotone2 allows zero, one, or two inputs, constants via empty gates, repeated wires, and forward or out-of-range reads that evaluate to false. The suffix does not have an explicit ReadsBack premise. Any exhaustive lower-bound model must account for that semantics or prove a normalization first.

The target has21 graph edges. The ordinary seven-star circuit has27 gates: seven three-input neighbor ORs cost14 OR gates, the seven star ANDs cost7 gates, and their final disjunction costs6 OR gates. This is an upper bound, not a proof of optimality.

## Existing checked results inspected

- **L_meta_1981:** any Monotone2 circuit has an equivalent no-larger Monotone2 circuit satisfying ReadsBack14.
- **L_meta_1983:** the exact Heawood function requires27 gates under ReadsBack and the absence of any AND gate in the ancestor cone of another AND. This forbids an AND-to-OR-to-AND path too, not merely direct AND-to-AND input.
- Its internal `pairCleanBound` gives edge-count plus a vertex-cover budget at most size+1 when every AND gate rejects zero, singleton and nonedge-pair tests. Output correctness alone does not give this internal gate premise.
- **L_meta_1483:** an unconditional twenty-gate bound for an isomorphic Heawood labeling, via the existing generic `n+tau≤size+1` argument. It does not give27.
- **L_meta_634:** the Heawood graph in a different explicit labeling has exact AND-count minimum7 in the free-OR AndCountCircuit model.
- **L_meta_4187:** the exact task labeling, with freeOR(0,1), needs at least7 suffix AND gates under boundary correctness. Its internal `collapse (n : Nat) (C : Circuit)` is already generic: it constructs an AndCountCircuit with size exactly the original AND count and matching all nonempty inputs. Consequently a new copy of the separate n=27 conversion L4682 is unnecessary for this conceptual route. The nonempty-input limitation is explicit; the37 negative rows and their augmentations are nonempty.
- **L_meta_2274:** existing first-gate reduction to an edge-deleted problem or the three free-OR representatives(0,1),(0,7),(0,9). The remote audit reports its substantive child lower bounds still open.
- **L_meta_3537:**65 listed canonical first-two-input patterns for the same adjacency-mask list (row0=1408, row1=8832). It checks canonicality of those patterns. This worker did not establish a converse completeness theorem; one cannot infer exhaustive coverage from canonicality alone. Four operation pairs would give260 cases if completeness is separately supplied.

Local definitions and named sources were read directly. The independent remote-status worker reported that its fresh official checked hashes match local L634/L4187/L1981/L1983/L2274 sources.

## Raw-read counting route

For a least circuit after a valid live/binary normalization, at least size−1 input occurrences read internal gate outputs. At most2*size input occurrences exist. Thus at size26 the number of raw-variable occurrences is at most27. Since all14 raw variables are essential, at least one raw variable must be read exactly once.

This is only an entry point. It does not imply a contradiction. In particular, the ordinary27-gate star circuit reads each of the seven star-center variables once and each opposite-side variable three times, for28 raw occurrences. Therefore the needed stronger claim cannot be that every variable must be read at least twice. A useful global lower bound would have to show that savings from singly-read variables force compensating additional reads elsewhere. This worker did not prove such a bound.

The earlier UniqueRead/ActiveRead archive proves collision restrictions for a primitive gate directly combining raw inputs. Its active-read convention treats NOT tails correctly, but that archive's endpoint is not a general lower bound on all raw occurrences and cannot supply the missing global count automatically.

## Literature boundary

The primary paper by Stasys Jukna, *Lower Bounds for Tropical Circuits and Dynamic Programs*, arXiv:1406.3065, Remark10 (page18), explicitly distinguishes the single-output bilinear Boolean function from its multi-output linear form, and distinguishes unrestricted Boolean circuits from tropical and multilinear Boolean circuits:

https://arxiv.org/pdf/1406.3065

That discussion explains why a generic biclique/arithmetic lower bound cannot simply be imported into this Boolean task. Its statement about what was known is historical to the paper; this note does not present it as a verified2026 literature classification. The root independently located primary counterexamples to a general quadratic single-level conjecture; none of that by itself supplies a Heawood counterexample.

## Outcome

No full2733 proof, refutation, or additional eligible official submission was obtained. The unrestricted case still allows internal dirty or nested AND gates. AND≥7 and a clean/no-nested27-gate bound do not resolve that case. The root owns the exact-CNF diagnostic and the workspace worker owns the bounded26-gate witness search; this worker did not duplicate either.
