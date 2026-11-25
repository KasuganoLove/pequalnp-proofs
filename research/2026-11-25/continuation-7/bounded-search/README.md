# L-meta-1884: bounded structured refutation search

## Result

No counterexample was found. A 180-second local search produced an 18-gate suffix with **11 incorrect assignments out of 1,024**: five false positives and six false negatives. The candidate is saved as `best-18.json` only as a reproducible near miss. It is not a solution, and search failure is not evidence of a proved lower bound.

All 40 constructed 20-gate baseline circuits passed an independent scalar check on every one of the 1,024 assignments (40,960 baseline rows). The best 18-gate candidate was checked independently on all 1,024 rows too.

## Exact task and search scope

The task asks whether every AND/OR/NOT suffix with at most 18 gates fails to compute the Petersen edge function when given ten permuted or repeated original inputs and one free unary function of x0. For a possible refutation, this search fixes the ten inputs in their original order and the free input to `NOT x0`. Input wires 0 through 9 are x0 through x9; wire 10 is `NOT x0`; suffix gate j produces wire 11+j.

The target edges, matching the task statement exactly, are:

```
01 12 23 34 40 05 16 27 38 49 57 79 96 68 85
```

There are 948 positive assignments and 76 negative assignments. Every fitness evaluation includes all 1,024 assignments. No sample-only acceptance is used.

The packed gate encoding is `[operation,a,b]`, where 0=AND, 1=OR, and 2=NOT of operand a. The b field is ignored for NOT and can be omitted when translating it to a Lean gate. Search gates always read earlier wires. The gate family explored is binary AND/OR and unary NOT; it does not enumerate every possible constant/forward-reference syntax allowed by the full `FanInTwo` definition. A full solution of the original universal statement is not claimed.

## Structured starting circuits

The generator exhaustively checks the 1,024 vertex subsets: the graph has maximum independent-set size four, with five independent sets of that size, and hence minimum cover size six. For each of the five complementary six-vertex covers, exactly three graph edges have both endpoints in the cover. Their eight assignments to star centers give 40 baselines.

Each star computes its center AND the OR of its assigned neighbors. Combining the six stars costs exactly 20 gates: nine neighbor OR gates, six AND gates, and five final OR gates. Each baseline is checked against the complete truth table.

For every baseline, the generator considers each pair of gate positions and each of four ways to bypass the deleted gates to their operands: 40×C(20,2)×4 = 30,400 candidates. The best 16 distinct candidates for each baseline are retained, giving 640 starting states. The best starting states have 18 mismatches.

## Search budget and outcome

The C++ search first exhausts 30,240 one-field edits around one representative for each baseline. It then performs mutation and simulated annealing with a fixed random seed `188420261125`, varying the false-positive penalty and restarting from structured seeds or the best state.

* Wall-time budget: 180 seconds.
* Packed complete-truth-table evaluations: 1,672,386,896.
* Restarts: 69,679.
* Accepted moves: 778,269,890.
* Exact witnesses: zero.
* Best suffix: 18 gates, five false positives and six false negatives.

The final best candidate uses neither a suffix NOT gate nor the free `NOT x0` wire, although the search allowed both. Its quadratic expansion replaces the true edge {2,3} with the nonedge {2,5}; other edges agree with the target. This is only a description of the saved candidate.

False-positive assignment masks: `36, 52, 100, 116, 548`.

False-negative assignment masks: `12, 13, 76, 77, 524, 525`.

The independent verifier uses ordinary Python booleans and an explicitly written target formula. It neither imports the seed generator nor shares the packed 64-bit evaluation implementation. Results appear in `independent-verification.json`. No Lean proof or strict-checker acceptance is claimed for this search.

## Existing checked cuts inspected

The local upstream source was pinned at `57164c3618362178843e2ea37bd01613f4037ae2`.

* [R_meta_651_1](https://github.com/open-goat/pequalnp-proofs/blob/57164c3618362178843e2ea37bd01613f4037ae2/lean/PEqualNP/Outside/R_meta_651_1.lean) has L-meta-1884 as the unary first-gate branch, alongside the adjacent-pair, nonadjacent-OR, and nonadjacent-AND branches.
* [R_meta_1884_773](https://github.com/open-goat/pequalnp-proofs/blob/57164c3618362178843e2ea37bd01613f4037ae2/lean/PEqualNP/Outside/R_meta_1884_773.lean) separates relabeling, normalization of the free unary signal to `NOT x0`, and the remaining identity-input/free-NOT lower bound. Its hypotheses remain requirements of the cut; the reduction itself is not a proof of that final lower bound.
* [R_meta_1884_1](https://github.com/open-goat/pequalnp-proofs/blob/57164c3618362178843e2ea37bd01613f4037ae2/lean/PEqualNP/Outside/R_meta_1884_1.lean) separates an ordinary Petersen 18-gate lower bound, a nine-input Petersen-minus-vertex 15-gate lower bound, and a remaining restricted-use branch for the free negated input.
* [R_meta_1884_412](https://github.com/open-goat/pequalnp-proofs/blob/57164c3618362178843e2ea37bd01613f4037ae2/lean/PEqualNP/Outside/R_meta_1884_412.lean) uses a pivotal-input property and a remaining circuit obstruction expressed through monotonicity, automorphism invariance, and rigidity.

The task sketch reports a known 20-gate circuit and earlier ten-minute undecided synthesis runs for first-gate cases. The work here supplies explicitly verified 20-gate baselines and uses a different, bounded local search. It does not establish that no 19-gate circuit exists.

## Reproduction

Run from this directory:

```sh
python3 make_seeds.py
g++ -O3 -march=native -std=c++17 local_search.cpp -o local_search
./local_search 180 > local-search.log 2>&1
python3 verify_candidates.py
```

The random seed is fixed. Since stopping uses elapsed time, the exact evaluation count and final candidate can vary with hardware and compiler. `make_seeds.py` regenerates `seeds.json` and `seeds.txt`; these larger derived files and the compiled executable are intentionally omitted from the curated archive.

No lease actions, remote writes, SAT runs, or follow-up searches were performed by this subtask.
