# L-meta-2348: structural analysis and a 29-gate calibration

## Status

No proof of the leased 27-gate impossibility statement was found. The constructions below are not counterexamples to that statement. In particular, the explicit witness has 29 gates and exceeds the bound by two. No broad SAT search was used.

## The exact obstacle

The task concerns an AND/OR circuit for the 14-input Fano incidence function with 21 quadratic prime implicants. Every gate has two distinct earlier operands, the first gate is OR, and the circuit has at most 27 gates. At the two singleton assignments on the marked incidence (point 0, line 0), both directional derivatives are assumed zero. These derivatives use OR as addition and the formal product rule for AND; they are not the Boolean finite-difference derivative of the computed function.

Interpret the circuit as a monotone formal polynomial: an OR gate adds polynomials, an AND gate multiplies them, and input wires are variables. Repeated occurrences are retained in this polynomial, even though Boolean evaluation is idempotent. A formal derivative at the point-only singleton is nonzero exactly when some output monomial has line-variable exponent one and no variables outside the marked pair. The reverse derivative makes the symmetric test. Because the exact Boolean output has the marked pair as a prime implicant and rejects each singleton, every output monomial supported on that pair contains both variables. Therefore both zero derivatives force both exponents to be at least two in every such monomial.

This is a useful proof-tree interpretation, but it does not bound how different proof trees share gates in the DAG. Converting it into a gate-count contradiction is the remaining mathematical obligation.

## Explicit calibration at 29 gates

The script `constructive/construct_29.py` starts with a standard 27-gate point-star circuit. Each of seven points contributes two OR gates to combine its three incident line inputs and one AND gate with the point input; six OR gates combine the seven stars. Its output is wire 40 and the point-0 star is wire 16. It appends:

- wire 41 = OR(40,16);
- wire 42 = AND(40,41).

The resulting output is F AND (F OR star0), hence F. On every singleton input, both inputs to the final AND are false. Its product-rule derivative is consequently zero in either direction for every incidence. The two final operands are distinct wire indices, so the distinct-operand condition remains satisfied.

`constructive/fano_double_reread_29.json` records all gates, two explicit derivative witness arrays for the marked incidence, and verification results. The Python script checked all 16,384 Boolean inputs against the exact Fano predicate, all earlier/distinct/binary operand conditions, the first OR gate, and both directional derivatives for all 21 incidences. The original 27-gate circuit has both marked derivatives true. These are exhaustive computations, not a Lean proof of semantic correctness. The optional Lean scratch certificate was not completed. Earlier runs timed out during symbolic circuit evaluation; a later staged attempt was stopped during session wrap-up. No Lean certificate of this witness is claimed.

## Local four-variable neighborhood

`constructive/local_dag.cpp` checks the function pq OR pQ OR qP. A usual four-gate formula computes it. A six-gate formula can additionally make both marked derivatives zero. Exhaustive enumeration of 17,244,252 ordered partial circuits found no such circuit with at most five gates, binary AND/OR gates, and distinct earlier operands. It enumerates every unordered distinct operand pair and both operations at each gate, with no pruning that removes repeated-computation nodes. Truth tables use 16 bits plus two formal-derivative bits.

For an explicit six-gate construction, set a = q OR Q, b = p AND a, c = q AND P, d = b OR c, e = d OR b, and output d AND e. The first four gates compute the target, and the last two preserve it while making both marked derivatives zero.

This establishes a local cost for that four-variable model only. It does not establish that the entire Fano circuit incurs the same two-gate cost: gates shared with other neighborhoods could change the accounting.

## Symmetry reduction

`flag_stabilizer_orbits.json` contains eight point/line permutations fixing the marked flag and their compositions with a duality, giving 16 symmetries of the marked instance. They reduce the 91 unordered first-OR input pairs to 14 orbits. Representatives and orbit sizes are:

| Pair | Orbit size |
|---|---:|
| (0,1) | 4 |
| (0,2) | 8 |
| (0,7) | 1 |
| (0,8) | 8 |
| (0,11) | 4 |
| (1,2) | 16 |
| (1,3) | 2 |
| (1,8) | 8 |
| (1,9) | 8 |
| (1,11) | 4 |
| (2,4) | 8 |
| (2,6) | 4 |
| (2,8) | 8 |
| (2,10) | 8 |

This is preprocessing, not a proof: each representative still requires an appropriate lower-bound argument.

## Existing reductions and limits

- `PEqualNP/Outside/R_meta_1480_1.lean` already isolates live double-read AND gates and separates same-gate, chained, and incomparable cases.
- `R_meta_1480_2.lean` supplies flag transitivity and the first-AND/first-OR split.
- `R_meta_1480_873.lean` proposes a formula-normalization route; a no-cost normalization is itself the hard step.
- The checked theorem `L_meta_1483.lean` proves a general Fano lower bound of 20 gates through a live DAG branch-budget argument. It does not reach 28.

Jukna, *Disproving the Single Level Conjecture* (SIAM Journal on Computing 36, 2006; ECCC TR05-021), shows that general monotone quadratic circuits need not admit equally small single-AND-level circuits. Its section 3.5 gives a lower bound for K2,2-free graphs only for explicitly single-level complexity C^1; Lemma 3.13 also assumes a single-level circuit. Its general counterexample uses saturated extensions, so it does not itself disprove a special Fano normalization. It also does not establish one.

Primary sources: https://eccc.weizmann.ac.il/report/2005/021/ and https://web.vu.lt/mif/s.jukna/ftp/single1.pdf . A Fano-specific normalization, or an independent DAG accounting argument strong enough to exclude 27 gates under the derivative condition, remains necessary.

## Reproduction commands and last observed results

Run from the repository root:

```sh
python3 research/2026-11-24/L-meta-2348/constructive/construct_29.py
g++ -O3 -std=c++17 research/2026-11-24/L-meta-2348/constructive/local_dag.cpp -o /tmp/pnp-2348-local-dag
/tmp/pnp-2348-local-dag
```

The Python command exited 0 and reported all 16,384 inputs checked, 29 gates, distinct earlier binary operands, first gate OR, and all 21 incidences with both derivatives false. The C++ executable exited 0 and reported no circuit of at most five gates after 17,244,252 ordered partial circuits. The executable and Python command were both rerun successfully during finalization.

The unverified Lean scratch attempt is deliberately omitted from this archive. It is not suitable for submission and is not part of the computational certificate.
