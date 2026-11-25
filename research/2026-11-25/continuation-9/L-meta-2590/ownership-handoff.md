# L-meta-2590 ownership and elimination handoff

Work stopped on the root agent's lease-expiry instruction: the shared lease
renewal returned HTTP 410 at 2026-11-25 07:53:45 UTC. No theorem synthesis,
counterexample search, or Lean compilation continued after that instruction.
The already saved candidate was independently evaluated on all 1,024 inputs
as a factual archival check.

## Completed bounded search

`Pnp2590OwnershipSearch.cpp` searches valid 19-gate, binary, backward-reading
AND/OR circuits. It scores the exact fifteen edge inputs and fifteen maximal
independent-set inputs. Its initial candidates are obtained by removing one
gate from 20-gate vertex-cover constructions. It uses random mutations and
simulated annealing; it is not exhaustive and produces no lower-bound
certificate.

The completed run used seed 259001 and a 55-second wall-time limit:

```sh
g++ -O3 -std=c++20 Pnp2590OwnershipSearch.cpp -o Pnp2590OwnershipSearch
./Pnp2590OwnershipSearch 55 259001 ownership-search-1.json > ownership-search-1.log 2>&1
```

It ended after 702,630,000 mutations and 23,421 restarts, with one of the thirty
sample rows incorrect. Exit status 1 means the time limit was reached without
a perfect candidate. Wall-time stopping makes the exact mutation count machine
dependent, even with the fixed seed.

`Pnp2590OwnershipVerify.py` independently checks a saved candidate on every input:

```sh
python3 Pnp2590OwnershipVerify.py ownership-search-1.json --output ownership-search-1-verification.json
```

For the saved best candidate, the only failed extremal sample is mask 264,
the positive edge {3,8}. Across all 1,024 assignments, the candidate has nine
errors. It is not a counterexample to L-meta-2590. No absence-of-counterexamples
claim follows from this heuristic run.

## Stronger-than-public theorem found inside upstream L-meta-2446

The downloaded source `upstream-audit/L_meta_2446.lean` contains:

```lean
theorem directSplit
    (m : ∀ k, k ≤ 15 → ¬Live false graph k inputs.toFinset)
    (s : ∀ k, k ≤ 14 → ¬Live true graph k inputs.toFinset) :
    ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 edge 15

theorem monoRoot : Impossible false graph 15 inputs.toFinset
theorem signedRoot : Impossible true graph 14 inputs.toFinset
```

Consequently `directSplit monoRoot signedRoot` proves the unrestricted
nine-input FanInTwo lower bound 16. The public theorem's representative-pair
and first-OR hypotheses are not used in its final proof. Root independently
confirmed this exact statement. The remote-status reviewer independently
confirmed that `HasCircuitSize` includes AND/OR/NOT, permits input lists of
length at most two, and does not add a ReadsBack hypothesis.

The internal `edge` function is exactly the ten-input task's Petersen function
with vertex 9 set to false, on the retained labels 0 through 8. The deleted
edges are (4,9), (7,9), and (9,6). A future eligible claim for an unrestricted
deleted-Petersen child can reuse this proof after checking its public statement
and the project's exact submission/import rules.

## Why this does not yet prove L-meta-2590

The known deleted-vertex lower bound would contradict a 19-gate Petersen
candidate if some vertex-zero restriction could always be implemented with
at least four gates saved. No such four-gate-saving theorem was found or
proved. A direct raw-reader count alone does not imply it. Shared intermediate
signals, especially dirty AND gates, are the remaining obstruction.

The workspace agent separately completed the clean-circuit lower bound 20 and
the implication that every correct Monotone2 circuit of size at most 19 must
contain a dirty AND. Those are conditional/structural results and do not give
the unrestricted lower bound.

## Assessment of extending the L-meta-2446 certificate engine

Its reusable mathematical core is forward semantic synthesis (`Live`) with
two operand-retention flags, exhaustive next-gate branching (`enum_step`),
oriented positive/negative row separation, and restriction lower-bound cuts
(`Slice`, `poolCut_sound`, `valid_exclude`). The packed `Forest` implementation
also depends on nine raw variables, 512-bit full truth tables, 152 selected
positive/negative row pairs, graph-mask charts, symmetry maps, and many prior
induced-subgraph bounds.

Deleting the signed-root half does not turn the existing certificate into a
ten-input proof. A ten-input monotone generator would need a new state forest,
appropriate restriction/symmetry data, and an adjusted extraction and checking
bridge. The unrestricted deleted-Petersen lower bound 16 is a promising
restriction rule for that generator, but no new generator or certificate was
completed here. Proceed only under a fresh valid lease.

## Frozen source and result hashes

| Artifact | SHA-256 |
| --- | --- |
| Pnp2590OwnershipSearch.cpp | 9e450e30cdf31fd7e67623a0bedb41749f3ea8c2707b70f4ce4978cf221c9b2d |
| ownership-search-1.json | 6b95138a4ac12ab27af6ee9d706575a034e4f0ce8b27a46e121e80b305c5dbd3 |
| ownership-search-1.log | 4bd534e3904287d53ff25403c58cf62364d97427f7dd54200448351eab01a046 |
| Pnp2590OwnershipVerify.py | 91ca2fe2181947af5af96ff7bf57c7a6e220edd6a75892ffa921050af1fab6c4 |
| ownership-search-1-verification.json | e45bf98e20a240489b3697845bc3f2d62a61f8bc67331c8a0dbad265d01d0cae |
| upstream-audit/L_meta_2446.lean | 605dd7edce03d051f286b53b076f95a008d7aa544ff27a7ebf87d9bf1c192071 |

No new Lean theorem module, strict-checker run, remote write, or lease action
was performed by this agent for L-meta-2590.
