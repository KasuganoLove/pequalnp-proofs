# PG4 graph bridge for L-meta-4201

## Checked result

`Pnp4201Graph.lean` passed ordinary Lean compilation with exit0 and an empty log. Its compiled olean was also produced successfully for use by the other research modules. This is a research bridge, not a standalone official task submission and not a proof of the104-OR lower bound.

Frozen source SHA256:

`3d08e8a902e29a8ca20fbd5714537708a0ef917c294b316baaedfdc2995de78c`

The file imports `PEqualNP.Defs` and the existing `Pnp4201Cover105` geometry proof. All new declarations are under `PEqualNP.Outside.Pnp4201Graph`.

## Exact graph and proven interfaces

`pg4` is the simple graph on `Fin42` obtained by symmetrizing the public directed relation:

`u<21 ∧ 21≤v ∧ (v+21-u)%21 ∈ [0,5,7,17,20]`.

The same graph definition already appears in upstream [R_meta_2379_1](https://github.com/open-goat/pequalnp-proofs/blob/57164c3618362178843e2ea37bd01613f4037ae2/lean/PEqualNP/Outside/R_meta_2379_1.lean) and [L_meta_5058](https://github.com/open-goat/pequalnp-proofs/blob/57164c3618362178843e2ea37bd01613f4037ae2/lean/PEqualNP/Outside/L_meta_5058.lean). The first also contains a related directed-to-undirected function bridge inside its AND-count reduction. This module does not claim a new graph definition. A bounded audit of those exact-relation sources and the1477/4199 reductions did not locate the precise NoFourCycle/105-edge interface needed here.

| Declaration | Meaning |
|---|---|
| `bipartite` | Adjacent vertices have opposite colors under `decide(v.val<21)` |
| `noFourCycle` | Exact `PEqualNP.TopForm.NoFourCycle pg4`: two distinct vertices have at most one common neighbor |
| `orderedEdges_card` | The filter of ordered pairs `(u,v)` with `u<v ∧ pg4.Adj u v` has cardinality105 |
| `edgeFinset_card` | The standard undirected edge finset has cardinality105 |
| `graphFun_true_iff` | The public directed incidence target is equivalent to `graphFun pg4 ∅ x=true` for every input |
| `computes_iff` | Public full-input circuit correctness is equivalent to `circuitFun42 C = graphFun pg4 ∅` |
| `nonconstant` | Zero input and the incident pair `{0,21}` give different graph-function values |
| `allANDSafe_iff` | Public target safety of every actual AND gate is exactly the corresponding `TopForm.BelowF pg4 C j` condition |

The final row is only a translation of an explicit hypothesis. It does **not** prove that every correct circuit is safe at all AND gates, or that a safe circuit exists within any OR budget. No TopForm existence or OR-count lower bound is asserted here.

## Finite checking and reuse

`Pnp4201Cover105` already proves the21×21 incidence count and common-line bound. The NoFourCycle proof reuses that common-line theorem and argues by the point/line sides. The dual line-line case is deduced by exchanging the roles of the two common points and the two lines; no second four-vertex search is performed.

Three small21×21 kernel certificates connect the `Fin21` point/line indexing with the public `Fin42` adjacency relation. The ordered-edge count is derived symbolically from the105 incidences using an injective point-line map. A separate kernel certificate checks the standard `Sym2(Fin42)` edge container. None of these certificates enumerates four independent `Fin42` vertices or all Boolean inputs on42 variables.

The semantic bridge is symbolic and holds for all42-variable Boolean assignments.

## Reproduction

From a project checkout with Defs built, put both source files in `lean/` and run from that directory:

```sh
LEAN_NUM_THREADS=1 lake env lean -j1 -o .lake/build/lib/lean/Pnp4201Cover105.olean Pnp4201Cover105.lean
LEAN_NUM_THREADS=1 lake env lean -j1 -o .lake/build/lib/lean/Pnp4201Graph.olean Pnp4201Graph.lean
```

`Graph-lean.log` and `Graph-build.log` are empty successful logs. `validation.json` records source hashes and the compile/build results. No strict project checker or remote submission was run for this research module.
