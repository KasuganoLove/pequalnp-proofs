# L-meta-10696: bounded source and status audit

Read-only audit under the parent's live allocation, 2026-11-25. No solver, Lean compilation, lease action, PR, or remote modification was performed here.

## Exact task

For the seven-input edge function on `02,13,04,24,05,25,45,06,16,26,36,46`, every fan-in-at-most-two AND/OR/NOT circuit with at most one NOT must have an AND/OR replacement of no greater total length. Zero-NOT circuits are included in the premise and can be returned unchanged. Inputs, output, missing reads, and short gate input lists have the ordinary `Circuit` semantics. Only `PEqualNP.Defs` is an allowed project import for the official task.

The exact negative twin is **L-meta-10697**. The 12:39:08.329 official desk snapshot lists both as open with zero PRs. Exact task-ID GitHub PR searches were empty. These observations are timestamped and do not promise that the state stays unchanged.

## Existing proof routes found

Seven of the eight six-vertex replacement cases mentioned by the sketch were located: `9511,9520,9526,9532,9539,9543,9553`. Their public source graphs have nine or ten edges. Deleting one of the true-twin vertices0,2,4 from the current graph leaves six vertices and eight edges, so none of these seven graphs is isomorphic to that particular minor. They also cannot directly be the seven-vertex task graph. The eighth sketch case was not identified in this bounded audit.

The fetched proofs generally use an exact lower bound for a fixed graph together with an explicit monotone upper circuit. In particular, the final wrappers do not furnish a generic theorem for eliminating a NOT or cloning a true-twin vertex.

`L_meta_9539` is a useful compact reference for a possible future certified search. Its `Signed.compile` converts arbitrary allowed circuits to a signed live-wire search while counting AND/OR gates and treating NOTs as free. `Signed.bound` proves `7 < binaryCost gs` only for its particular six-input, nine-edge function, using a fixed1400-bit sample encoding and `search 7 rows = false`. Combined with a nine-gate monotone circuit, the presence of any NOT forces enough total gates for that replacement; a NOT-free circuit is returned unchanged. The proof ignores the at-most-one-NOT hypothesis, but its numeric certificate is graph-specific. Transferring it to10696 would require a new sample map and a newly checked search rejection. No such transfer was attempted.

The exact reference source is locally available as `L_meta_9539.reference.lean`, SHA256 `f0ea1c9ca867450a030a85e2152c13be57db5b8f1f7ed96c891c06afe3edd876`, matching the current official checked row. It attributes the method through L9136, L9146 by partymejker, L8633 by k-sandhu, and the earlier signed-search sources L8463/L1449. It is a reference copy, not our new theorem, and is omitted from the compact archive unless a later proof actually depends on it.

The older generic helpers `MetaComplexity/Helpers/OneNotSplit.lean` and `OneNotPiece.lean` split the list around its sole NOT, establish monotonicity of the prefix, and replace/delete that gate on the region where its input has a fixed truth value. These are conditional regional facts. They do not globally justify replacing the NOT by one constant while preserving the target on every input. They also are not among this task's allowed project imports; any needed proof content would need a legitimate self-contained adaptation.

## Outcome and limits

No ready proof or counterexample for10696/10697 was found. No generic true-twin-cloning size lemma was identified. The parent's mathematical workers are responsible for any new construction or lower bound; this audit does not assert their currently proposed upper circuits are optimal.

Primary sources: https://data.pequalnp.com/data/desk/gaps.json and the exact repository file URLs in `reference-summary.json`. GitHub search is a bounded discovery tool, not proof that an unlocated result does not exist.
