# A precise barrier for a 63-gate star construction

Status: an independently reasoned mathematical argument; **not formalized or checked in Lean**. It does not establish the complete 64-gate PG(2,3) lower bound.

## Lemma: ANDs do not save gates for pairwise singly overlapping Boolean sums

Consider an acyclic monotone binary AND/OR circuit with several outputs, exactly computing

    f_i(x) = OR {x_v : v in S_i},

where `|S_i ∩ S_j| ≤ 1` for distinct outputs. Constants may be propagated and unused gates removed. Then there is an OR-only circuit computing all those outputs with no more gates.

Take an AND gate g last in topological order among the remaining AND gates. Every route from g to an output contains only OR gates. Let T be its singleton support: the variables v on whose singleton assignment g is true. For every reachable output i, `g ≤ f_i`, hence `T ⊆ S_i`.

* If T is empty, replace g by false and propagate that constant. This decreases all affected outputs and leaves every singleton response unchanged.
* If T={v}, replace g by the input x_v. Monotonicity implies `x_v ≤ g`; again all affected outputs decrease and all singleton responses are unchanged.

In both cases each new output is still monotone, is bounded above by its old linear output, and is true on all of that output's required singleton assignments. These three facts imply it is exactly the same Boolean sum on every assignment, not just on singletons.

If |T|≥2, at most one output is reachable from g, because two such outputs would both contain T. If there is no reachable output, delete g as dead. Otherwise let S be the unique output's support. Evaluate on the assignment z that is false exactly on S and true outside S. Since `g ≤ OR(S)`, g(z)=false; at least one operand h of this AND is false at z. Monotonicity gives `h ≤ OR(S)`: every assignment on which OR(S) is false is bounded by z. Also `g ≤ h`. Bypass g by h. Only the one output can increase. Its OR-only downstream cone remains bounded above by OR(S), because every newly introduced term is h and all old terms were already bounded by that output. The output therefore remains exact. No other output changes.

Each step removes an AND without adding a gate; iterate. Constants introduced in the empty-support case are propagated through the OR-only downstream cone and do not require a new counted gate.

## Applying the lemma to the PG(2,3) point-star architecture

The 13 line-neighborhood sets of the 13 points each have size4 and pairwise intersection exactly1. Their exact Boolean sums consequently need at least39 total gates, even if arbitrary ANDs are allowed in their shared multi-output preparation.

For the OR-only lower bound, remove constant or singleton-copy gates. Any useful OR gate whose support has at least2 variables can reach at most one output, since its support is contained in every reachable output. Each four-variable sum requires at least3 such gates (the usual binary DAG source-count argument). Thus there are at least13×3=39 gates.

Suppose a candidate is of the form

    OR_{p=0}^{12} (point_p AND h_p(lines)),

with h_p depending only on the 13 line variables. Set all point variables except point_p to false, and point_p to true. Exact graph correctness then forces h_p to be exactly the OR of p's four incident lines. The preparation therefore costs at least39 gates. The13 point ANDs and their12-gate OR combination bring this architecture to at least64.

Thus introducing ANDs only into the shared line-only preparation cannot produce63 gates. A63-gate witness would need a different architecture, such as mixing point and line information before this final star decomposition. This conclusion is architectural and does not exclude arbitrary26-input circuits.

## Why the same peeling argument does not prove the graph lower bound

A Boolean sum OR(S) has one maximal negative assignment: all variables outside S true. This gives a single operand h bounded by the entire target. The graph function has many incomparable maximal negative assignments (independent vertex sets). A last AND may have one false operand on one independent set and the other false operand on a different one. There is then no justified global choice of an operand to bypass. Treating these choices as uniform would silently assume the missing normalization theorem.
