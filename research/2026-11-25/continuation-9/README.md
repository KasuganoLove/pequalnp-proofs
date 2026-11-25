# Petersen clean-circuit lower bound: frozen research result

This checkpoint contains the completed clean-circuit part of **L-meta-2590**, its ordinary Lean validation, bounded searches, and an audit of reusable upstream proofs. The full L-meta-2590 statement is still unproved here. This is a public research-review artifact in the owner's fork, not an official proof submission or an official acceptance.

## Completed mathematics

For the exact fifteen-edge Petersen function in the public statement, `Pnp2590Graph` identifies the Boolean expression with its graph function and verifies that the graph has fifteen edges, no four-cycle, and vertex-cover number at least six.

`Pnp2590CleanBound` then proves:

- Any clean TopForm AO2 circuit for this function has at least six AND gates and fourteen OR gates, hence at least twenty gates in total.
- Any correct **initially clean** Monotone2 circuit has at least twenty gates and fourteen OR gates. Here clean means that every actual AND gate being true implies that the target output is true on the same input.
- Any hypothetical correct Monotone2 circuit with at most nineteen gates contains an actual AND gate that is true on some target-negative input.

The normalization preserves total-size and OR-count bounds inside the clean class. It does not prove that every arbitrary circuit can be made clean without cost, and it does not transfer the six-AND bound to an arbitrary original non-TopForm circuit. The dirty witness is an arbitrary negative input, with no extra pair-support or singleton-off property.

The two source modules compiled successfully with empty logs. Six audited key declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`. No strict project-checker run was performed for this conditional component. See [the exact scope and validation](L-meta-2590/clean-case/README.md).

## Search evidence

The stochastic diagnostic tested 702,630,000 mutations in 55 seconds. Its best saved nineteen-gate candidate missed one of thirty extremal samples. Independent evaluation on all 1,024 Boolean inputs found nine errors. It is not a counterexample.

A separate diagnostic exported the exact public `PEqualNP.Defs.LratEncoding.enc2` formula for ten inputs, nineteen gate slots and thirty extremal samples. It has 138,019 clauses, maximum DIMACS variable index 166,533, and SHA256:

```text
0a6e7d9fd083accd834a76b6bd2bc6b129cafe2e1a717acec6262524c9757757
```

CaDiCaL returned **UNKNOWN** after the configured 300-second limit. Neither this run nor the stochastic run supplies a Lean certificate or a circuit lower bound. The generated 5.4 MB CNF and executable binaries are omitted because they are reproducible from the retained sources.

To regenerate the CNF in the pinned project environment, run from its `lean/` directory:

```sh
lake env lean --run /absolute/path/to/L-meta-2590/ExportCNF.lean 19 /absolute/path/to/petersen-19.cnf
```

The diagnostic solver invocation was:

```sh
cadical --no-colors -t 300 -w petersen-19.solution petersen-19.cnf
```

`ExportCNF.lean` is a research utility with an IO entry point, not a submitted proof file. Search source, logs, results, independent verification and commands are retained beside it.

## A useful upstream result

Source inspection found a stronger internal theorem in the already checked upstream `L_meta_2446.lean`:

```lean
directSplit monoRoot signedRoot :
  ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 edge 15
```

It is an unconditional sixteen-gate lower bound for the Petersen graph with vertex 9 set false, including the project's FanInTwo AND/OR/NOT circuits. The public wrapper's first-OR assumption is unused. This result belongs to the upstream authors; it is not a new theorem proved by this checkpoint. The source header's certificate and helper attributions are preserved in the copied audited source.

One possible continuation would combine this bound with a theorem that some vertex-zero restriction of a hypothetical nineteen-gate circuit saves at least four gates. No such universal saving theorem was obtained. The existing nine-variable certificate machinery also cannot be reused as a ten-variable certificate merely by dropping its signed case. See [the ownership handoff](L-meta-2590/ownership-handoff.md) and the upstream audit.

## Task handoff

The desk returned an existing owner-handle lease for L-meta-2590, which was renewed successfully at 07:45:34 UTC. Renewal returned HTTP 410 at 07:53:45 UTC. New proof work stopped; subsequent work only collected already-running validation output and packaged completed artifacts. The exact sanitized record is in [lease-handoff.json](lease-handoff.json).

The later read-only public snapshot still listed L-meta-2590 as open to work with a holder, not as checked. A closed lease alone is therefore not evidence that the mathematical task has been solved. A new live assignment is needed before further task work.

## Reproduction and provenance

Use Lean 4.36.0 and Mathlib commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. The definitions and semantic checker environment were verified against upstream commit `259523a5b265318b84f9377f2feb965fd213f898`; the actual ordinary proof checkout was `57164c3618362178843e2ea37bd01613f4037ae2`. [Continuation 8](../continuation-8/README.md) includes the exact dependency and environment audit.

The clean-case README records the module build order and full theorem scope. New code reuses the archived clean normalization, clean-class minimization, OR counting, and upstream L1501/L2235 helper proofs, preserving their Apache-2.0 attribution. The archive manifest records every retained file's SHA256. No private lease identifier, account token, or executable binary is included.

The raw upstream blob table referenced by continuation 8's environment report is supplied here as `supporting-evidence/env-upstream-blobs.json`. Continuation 8 itself remains the immutable earlier checkpoint; its historical plan to seek an official PR should be read with the current submission-state explanation in the stage overview.

## Subsequent stale-task audit: L-meta-949

While packaging, the desk offered L-meta-949 for a reduction. Two independent source reviews found that the officially checked L-meta-950 is its exact logical opposite under the same partial-function assumptions. The existing proof was already merged in upstream PR #1995. Positive witness search and positive-cut construction were therefore not started.

The assignment was returned with `statement_seems_false` at 08:07:05 UTC, HTTP 200. [The audit](L-meta-949/audit-curated/false-twin-audit.md) preserves the task, exact premise comparison and official proof provenance. GitHub records the merge at 19:56:27 UTC on November 23; the desk's later status timestamp is 19:56:33.901 UTC. These are distinct events. No new proof or official PR is claimed for this audit.
