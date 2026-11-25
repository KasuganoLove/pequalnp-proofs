# L-meta-11020/11021: cost measure of the reported lower bound

Read-only source audit, 2026-11-25. No solver, Lean compilation, allocation, or remote mutation was performed for this audit.

## Finding

The public 11020 sketch reports that its checked-row elimination recursion reaches 15. The public elimination interfaces that match the described rules count **all gates, including NOT**. They do not establish that this graph needs 15 AND/OR gates in addition to its NOT gates. Therefore the sketch cannot by itself be used to prove that a circuit containing a NOT must have at least 16 gates.

The public row metadata gives template `table2-nine-vertex-pairs-140`, hash `0498fdaaee0746f127a0d4e6b2bacf3ec97f268a481a1dd12de301b2ede7bd96`; it does not name the recursion program or its leaf certificate. I did not locate that program or an exact certificate for this graph in the pinned checkout. This is a limit of the source audit, not a claim that no such artifact exists elsewhere.

## Checked interfaces and their costs

At local upstream commit `57164c3618362178843e2ea37bd01613f4037ae2`:

| Source | Relevant interface | Cost measured |
|---|---|---|
| `lean/PEqualNP/Defs/MetaComplexity.lean` | `HasCircuitSize n f s` quantifies a `FanInTwo` circuit with `C.size ≤ s` | Every circuit gate, including NOT |
| `lean/PEqualNP/MetaComplexity/Helpers/Elim.lean` | `PEqualNP.MetaComplexity.Helpers.gate_elim`: a dependent input fixed to a nonconstant cofactor sends size `s+1` to `s` | Total gate count |
| `lean/PEqualNP/MetaComplexity/Helpers/ReadersExport.lean` | `Readers.fanout_step_3_4`: under dependency, nonconstant-cofactor and no-funnel premises, some restriction satisfies `s′+3≤s` or `s′+4≤s` | Total gate count |
| `lean/PEqualNP/MetaComplexity/L107.lean` | Public exact export of the preceding 3-or-4 rule | Total gate count |
| `lean/PEqualNP/MetaComplexity/Helpers/PadOr.lean` | `PadOr.pad_down` / `pad_or`: adjoining a fresh OR variable costs exactly one | Total gate count |
| `notes/note-1-edge-function-exact-size.md` | Project explanation of its graph elimination basis | Explicitly says all gates, NOT included |

Source base: https://github.com/open-goat/pequalnp-proofs/tree/57164c3618362178843e2ea37bd01613f4037ae2

## Separate non-NOT bound does not automatically transfer

`lean/PEqualNP/Outside/L_meta_4725.lean` genuinely proves a stronger cost statement for the **full Petersen graph**: `15 + NotBracket.notCount C ≤ C.size`. Its internal `petersen_binary_lower` bounds `CircuitProof.nonNotCount C.gates` by 15. This uses a graph-specific lower bound of six branching wires, `least_petersen_six_branches`, and a specific finite twin-class deletion certificate. The public theorem is about ten-input Petersen, not this nine-input target.

The generic branch accounting here is of the form `n - 1 + required branches`. A vertex cover of size five exists for the current graph, so singleton twin-class deletions along that cover already supply a sequence of at most five deletions. The same deletion-obstruction test cannot be repurposed to demand the seven branches that would give non-NOT count 15 at n=9. A new argument would be needed.

## Exact small graph checks

Edges are `04,05,15,26,36,07,27,47,18,38,48,68`. Exhaustive enumeration of four-vertex cycles finds no C4. Its two triangles are `047` and `368`. Enumerating all vertex subsets gives cover number five, with witness `{0,1,6,7,8}`. These are ordinary finite Python checks, not Lean certificates.

An all-AND-safe monotone representation could be handled by the earlier C4-free clean-circuit OR/cover counting route, giving the expected 12+5−1=16. This is conditional on semantic safety of every AND; the audit does not supply a normalizer for arbitrary dirty AND circuits. It also does not eliminate circuits with NOT gates.

## Scope

No new proof of either twin, no 15-gate circuit, and no proof that 15 AND/OR gates are necessary in the presence of free negations was produced. The existing 15-gate synthesis job belongs to the separate worker and is not evidence for this audit.
