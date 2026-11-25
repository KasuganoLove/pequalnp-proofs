# L-meta-2733: current status and reusable Heawood results

Read-only audit, 2026-11-25. Public live-status responses were served at **09:11:40 UTC**; the public desk snapshot was updated at **09:10:16.320 UTC**. No lease action, solver, Lean build, or remote mutation was performed.

## Exact task polarity

The current statement of 2733 is byte-for-byte `¬ (` followed by the current statement of 2732 and `)`. This was checked as a string equality against the fresh public desk data.

2732 asks for two canonical first gates followed by a Monotone2 suffix of at most 24 gates, computing the 14-input Heawood edge function on every assignment. Thus 2733 requires excluding all such 26-gate circuits. One input falsifying one proposed circuit would not prove this universal nonexistence assertion. The generic sketch's wording about an explicit counterexample is not an adequate proof recipe for this existential positive statement.

2733 lists only `PEqualNP.Defs` as a permitted project import; its row has no `reductions: true` field. Existing outside proofs can inform or supply inlined material, but cannot simply be imported in an official 2733 submission.

## Current public status

| Task | Role | Current status |
|---|---|---|
| 2733 | Held negative twin | Posted, one anonymous public holder, no PR |
| 2732 | Canonical 26-gate existence | Posted, three holders, no PR, three live reductions |
| 582 | Unrestricted 26-gate existence | Posted, three holders, no PR, three live reductions |
| 971 | Every Heawood Monotone2 circuit has at least 27 gates | Posted, one holder, no PR, three live reductions |
| 2734 | Prepend the two free input gates | Checked |

Status URLs:

- <https://pequalnp.com/desk/step?gap=L-meta-2733>
- <https://pequalnp.com/desk/step?gap=L-meta-2732>
- <https://pequalnp.com/desk/step?gap=L-meta-582>
- <https://pequalnp.com/desk/step?gap=L-meta-971>
- <https://data.pequalnp.com/data/desk/gaps.json>

No checked or withdrawn record for 2732, 2733, 582, or 971 appears in this snapshot. The current public holder counts do not identify individual accounts; ownership of the working lease comes from the parent's separate authenticated allocation, not these anonymous responses.

## Reuse map and exact remaining gaps

All 14 source files listed in `source-checks.json` are present locally and byte-identical to the current desk's checked-file SHA256. Local checkout provenance is commit `57164c3618362178843e2ea37bd01613f4037ae2`; newer public status was checked independently. This bounded audit found no completed full 27-gate bound or 26-gate witness to reuse immediately.

| Checked result | What it actually supplies | What it does not supply |
|---|---|---|
| L2734 | Converts a suffix of size s with the two extra gate values into a Monotone2 circuit of size ≤s+2 on the original inputs | Any lower bound |
| L1981 | Size-nonincreasing ReadsBack normalization | Elimination of nested AND gates |
| L1983 | Exact Heawood size ≥27 under ReadsBack and absence of an AND-to-AND `InCone` relation | The nested-AND case |
| L1983 internal `pairCleanBound` | For C4-free graphs, a vertex cover T with edge-count + card(T) ≤ circuit-size +1, assuming every AND is sound on zero/singleton/pair inputs | Automatic internal cleanliness from output correctness |
| L2274 | First-gate normalization to edge-AND residual, same-side OR, or two cross-side OR representatives | The lower bounds on those residuals |
| L2648/2650/2652/2654 | The normalizations, symmetry and erasures supporting L2274 | A universal 27-gate conclusion |
| L634 | Exact Heawood AndCount minimum 7, with a different vertex labeling | Total gate count ≥27 without a further OR bound and model bridge |
| L4187 | At least seven suffix AND gates in the free-OR(0,1) case under its boundary promise | The missing 26-gate suffix total bound |
| L1483 | A full unrestricted 20-gate lower bound, for another Heawood labeling | The needed 27-gate bound |
| L3529 | 21 minimal true and 37 maximal false rows suffice as the finite boundary | A circuit-size certificate |
| L3537 | Canonicality of 65 two-gate wiring representatives | Nonexistence of completions |
| L3539 | Packed-column circuit simulation and extension from boundary agreement to all inputs | A successful or exhaustive bounded search |

The three checked reductions of 971 expose these still-open mathematical obligations:

- `R_meta_971_1`: L1981 and L1983 are checked; **L1985**, the nested-AND lower bound, is open. The same child can appear through a later cut of another parent; its current sketch mentions L2706. Its exact statement still is the nested-AND case read from the original cut.
- `R_meta_971_2`: L2274 is checked; **L2276** requires the 25-gate edge-deleted residual bound, **L2278** the 26-gate same-side free-OR suffix bound, and **L2280** the 26-gate cross-side free-OR suffix bound. All remain open.
- `R_meta_971_3`: **L2706** and **L2708**, respectively the irredundant final-OR and final-AND two-signal bounds, remain open.

The positive-side packed search **L3541** is also still posted: it asks for a 24-gate suffix after one of 65 canonical two-gate prefixes, producing the exact 58-bit target. L3537 and L3539 are checked helpers around that open witness search.

If a complete L971 proof becomes available, L2734 makes the implication to 2733 short: a hypothetical suffix of at most 24 gates extends to a correct circuit of at most 26 gates, contradicting the 27-gate bound. Currently, that missing complete bound is the substantive obstacle. A clean-case specialization can be useful research, but cannot settle 2733 because no cleanliness assumption appears in its statement.

## Recent PR evidence

Exact task-title search found no 2733 PR. Positive-twin title searches found reductions, not a witness:

- <https://github.com/open-goat/pequalnp-proofs/pull/5176> — extremal-row reduction; its actual ≤26 circuit search was unsuccessful.
- <https://github.com/open-goat/pequalnp-proofs/pull/5979> — 65-prefix/58-bit reduction; the witness remains an explicit hypothesis.
- <https://github.com/open-goat/pequalnp-proofs/pull/12249> — guarded 22-gate middle-circuit reduction. Closed unmerged at 04:48:18 UTC. The official [intake comment](https://github.com/open-goat/pequalnp-proofs/pull/12249#issuecomment-7153178845) says its reduction passed, but was not recorded because its author already held five open reductions. It is not a proof of the remaining search hypothesis.
- <https://github.com/open-goat/pequalnp-proofs/pull/6879> and <https://github.com/open-goat/pequalnp-proofs/pull/7187> — open reductions of sibling 2876 to packed synthesis/reachability. Both retain the witness as an unproved premise; they do not demonstrate a 26-gate circuit.

The three live 2732 cuts are `R_meta_2732_3`, `R_meta_2732_427`, and `R_meta_2732_773`. The three live 582 cuts are `R_meta_582_317`, `R_meta_582_704`, and `R_meta_582_773`. Their current artifact hashes and states are saved in `selected-status.json`.

## Archive scope

The curated subset contains this report, current selected public rows, exact relevant child statements, PR metadata, source hashes, and HTTP retrieval records. The full 2.99 MB desk download and broad local statement-extraction intermediate are left outside the curated subset. No bounded search failure is promoted to a lower bound, and this report does not claim the problem has been solved.
