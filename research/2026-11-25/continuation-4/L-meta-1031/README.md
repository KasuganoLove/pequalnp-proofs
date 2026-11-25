# L-meta-1031 continuation: physical pruning and circuit-model normalization

This is partial research for L-meta-1031, not a proof or refutation of its full statement.
The task asks for some minimum AND/OR circuit on a triangle-free, four-cycle-free graph
such that every AND gate owns a nonempty star of edges. Its three live reduction slots
were already occupied when this lease was issued.

## What current upstream already supplies

- `L_meta_1599`: every graph edge is owned by some AND gate.
- `L_meta_1600`: a semantically clean AND gate has a star-shaped set of owned edges,
  under the no-four-cycle hypothesis.
- `L_meta_1906`: from a clean minimum circuit, obtain a no-larger clean circuit in which
  every AND gate owns an edge. This was independently identified by the remote-status agent.
- `L_meta_2668`: erasing a gate of a minimum Monotone2 graph circuit loses an edge-pair;
  in particular, each AND gate accepts some edge-pair.

The last statement is weaker than nonempty ownership: an accepted edge may also make an
AND ancestor true. It must not be substituted for ownership.

## New physical alias lemma

`Pnp1031Pruning.lean` proves `erase_edge_preserving_alias`.
For a Monotone2 circuit computing the graph edge function, suppose gate `r` and a redirect
wire `i` satisfy both of the following:

1. Whenever wire `i` is true, gate `r` is true, on every input.
2. They have equal values on each graph edge-pair input.

The wire is either earlier than gate `r`, or past the complete circuit so that it reads as
false. The actual project operation `CircuitMoves.eraseGate` then preserves the entire
output function and Monotone2, and its size plus one equals the old size. All later reads
and the output index are physically renamed. This handles arbitrary gate position and
fanout, rather than only a fixed five-gate prefix.

Reason: erasure can only lower the output, and it preserves all minimal true inputs
(edge pairs). Monotonicity therefore forces equality on every input. Minimality rules
out such a gate. The same earlier-wire deletion is proved to preserve `IsAO2`, yielding
an `IsLeastAO` version of the contradiction.

The wire-erasure implementation and its evaluation invariants were adapted from upstream
`L_meta_2668`, which credits the bypass construction to willakone's L-meta-1499 / PR3112.
The new work is the semantic criterion, its physical size-saving conclusion, and the
pure-product applications below.

## Pure-OR product applications

Let a gate compute `OR(S) AND OR(T)`, where `S,T` are finite sets of original inputs.
If `S ∩ T = {c}` and every graph edge joining a member of `S` to a member of `T` touches
`c`, the gate can be replaced by original input `c` and deleted. Such a gate is impossible
in a minimum Monotone2 circuit or a least IsAO2 circuit. This condition includes two
point-only OR supports in a bipartite incidence graph with a singleton overlap.

More generally, if no graph edge joins `S` to `T`, a minimum Monotone2 circuit containing
this product must have at least two elements in `S ∩ T`. The empty-overlap case permits
zero erasure, and the singleton case permits the preceding alias erasure.

Consequently, in a graph with no four-cycle, the actual `TopForm.wmax` set of safe raw-input
AND partners of such a product has at most one member. The proof reuses the previously
saved `Pnp2391Wmax` argument: two distinct accepted singletons force every safe partner to
be a common neighbour, and the no-four-cycle condition bounds their number by one.

These are local restrictions on pure-OR operands. They do not show that every dirty AND
has that form or that all shared OR-reader configurations can be removed.

## Model normalization

`Pnp1031Normalization.lean` reuses the verified constant-propagation core from the previous
2391 research, itself adapted from upstream L-meta-1680 and L-meta-1425.

Its new `normalize_nonconstant` theorem takes any Monotone2 circuit computing a
nonconstant Boolean function and produces an IsAO2 circuit with the same function and
no more gates. Unary gates, constants and forward reads are eliminated by the status
mapping; all gates continue to count toward size. The nonconstant premise is necessary
for this general statement because exact-two AND/OR circuits cannot compute constant true.

For graph edge functions, `normalize_graph` also handles the edgeless case explicitly
with a zero-gate circuit whose out-of-range output reads false. Thus for an IsAO2 circuit
computing any graph edge function, `IsLeastAO G C` is equivalent to
`IsMinimalMonoCircuit n C`. This removes the previous mismatch between the two minimum
circuit models without assuming any cleanliness property of AND gates.

## Remaining gap

The full1031 task remains open in this work. Existing clean-circuit ownership and star
lemmas reduce attention to the existence of a clean minimum circuit, but the new local
rewrites do not establish that global property. Products with larger shared supports,
non-pure operands and shared OR contexts still require an argument preserving total
all-gate size.

## Validation

- Pruning: ordinary pinned Lean4.36.0 compilation, exit0; one inherited unused-simp warning.
- Normalization: ordinary pinned Lean4.36.0 compilation, exit0; inherited style warnings only.
- No official checker verdict or PR is claimed for these partial research files.
