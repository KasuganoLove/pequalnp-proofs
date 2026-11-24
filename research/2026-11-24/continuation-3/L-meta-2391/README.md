# L-meta-2391: verified pruning and local structural results

## Status

The assigned theorem is **not proved**. It says that every least AO2 circuit
for the order-three projective-plane incidence graph has no dirty AND gate:
`TopForm.junk G C = ∅`. We have not submitted an official proof or reduction
for that statement. The work below is reusable, ordinarily Lean-checked
research progress. No strict-checker acceptance is claimed.

The universal quantifier matters. Producing one clean minimum circuit would
not establish that every minimum circuit is clean. Conversely, showing an
unclean representation is not a counterexample unless its minimality is
established. The familiar 64-gate star construction supplies an upper bound;
we did not assume a 64-gate lower bound. The checked `L_meta_1484` result
examined during this work gives 38 gates under a different lower-bound route.

## Completed formal results

### Physical pruning and minimality

`Pnp2391Pruning.lean` proves:

- `least_gate_productive`: every real gate of every least AO2 circuit for a
  nonempty graph function accepts at least one edge-pair input.
- `plane3_gate_productive`: that result for the exact order-three incidence
  graph of the assigned statement.
- `least_no_small_replacement`: a gate in a least circuit cannot be replaced
  by a constant or unary AND/OR alias which is pointwise below the original
  gate and agrees with it on all edge-pair inputs.

These are actual gate-count arguments. The proofs first modify the gate and
then propagate constants and aliases, producing a smaller circuit satisfying
`TopForm.IsAO2`: only AND/OR gates, exactly two inputs, and earlier-wire reads.
No forbidden constant gate remains. The correctness argument uses both
pointwise domination and preservation of every minimal positive edge input.
See `PRUNING.md` for precise hypotheses, proof structure, and attribution.

### Pure-point products and safe line readers

`Pnp2391Local.lean` proves:

- A product `OR(S) AND OR(T)` on a point singleton p is true exactly when
  `p ∈ S ∩ T`. The empty and singleton intersection cases are explicit lemmas.
- A common raw input p is pointwise below that product. Combined with the
  small-replacement theorem, this supplies the semantic ingredients for
  deleting the singleton-intersection case; no standalone combined circuit
  corollary is asserted in this file.
- A line l is a sound context for `OR(S) AND OR(T) AND y_l` exactly when all
  points of S lie on l or all points of T lie on l.
- Each sound reader may choose its own incident factor. Replacing the reader
  by that factor AND y_l preserves any monotone continuation that previously
  computed the incidence function. The continuation may share reader outputs.
- In a C4-free incidence, there are at most two such line contexts when both
  factors contain at least two points. If their intersection contains two
  points, there is at most one.
- The exact relation `p = l OR p = l+1 OR p = l+3 OR p = l+9` on `Fin 13` is
  proved C4-free, and both context bounds are specialized to it.

The reader theorem is a semantic rewrite, not an implemented root-circuit
rewiring with a verified gate-count bound. It does not apply to arbitrary
mixed factors or an OR chain between the product and its readers without
additional analysis.

### Safe partners of general singleton-active gates

`Pnp2391Wmax.lean` uses the actual `TopForm.wmax` definition. It proves that a
safe raw-input AND partner of a monotone gate must be adjacent to every
singleton input on which that gate is true. Therefore, in a graph with no
four-cycle, a gate true on two distinct singleton inputs has at most one safe
raw-input AND partner. Gate monotonicity is an explicit premise. The
monotonicity machinery in the pruning file supplies it for AND/OR circuits.
No intermediate gate is assumed sound merely because the output is sound.

## Remaining obstruction

Productivity does not imply cleanliness: a gate can be true on both a real
edge and a nonedge. The productive mixed rectangles, their shared OR readers,
and general cleanup contexts remain uncontrolled. The new small-replacement
theorem works when an appropriate earlier wire or constant is available; we
have not proved that every dirty gate in a minimum plane circuit has one.

The C4-free bounds restrict distinct raw-input contexts, not the number of
syntactic readers. They therefore do not by themselves pay for a global
transformation or exclude every possible dirty AND. A broad reduction was
not submitted because the remaining child would mostly restate this missing
normalization argument.

The separate L-meta-3321 work also has a checked fixed shared-reader rewrite.
It preserves size and all relevant remaining wire values for its specified
prefix; without a strict size reduction it cannot alone contradict the
universal minimum-circuit claim here.

## Validation

All three source files passed ordinary Lean checking with exit code 0 on
2026-11-24, using the project at
`89b96c0f464824a164434fb460926400b9943047`.

- `local-compile.log` and `wmax-compile.log` are empty.
- `pruning-compile.log` contains style warnings but no errors.
- No strict checker or official task checker was run on these research files.
- No new axioms, admitted goals, or imports of other Outside proofs are used.

After checking out the pinned project and building `PEqualNP.Defs`, copy the
three files into the project's `lean/` directory and run there:

```sh
LEAN_NUM_THREADS=1 lake env lean -j1 Pnp2391Pruning.lean
LEAN_NUM_THREADS=1 lake env lean -j1 Pnp2391Local.lean
LEAN_NUM_THREADS=1 lake env lean -j1 Pnp2391Wmax.lean
```

The files are independently checkable and do not import each other. Full
setup instructions and upstream provenance for the copied elimination core
are in `PRUNING.md`. The local context proof extends our previously checked
L-meta-3321 work. The elementary graph pair-input lemma in the Wmax file is
adapted from upstream `L_meta_1876`. SHA-256 hashes are in `MANIFEST.json`.
