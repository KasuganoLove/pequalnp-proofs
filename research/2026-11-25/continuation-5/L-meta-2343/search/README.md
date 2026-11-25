# L-meta-2343: bounded structured circuit search

## Outcome and exact sample set

**No counterexample was found, and this search does not prove the lower bound.**
Two explicit 63-gate suffix constructions pass the exact statement's samples.
The saved 62-gate near misses each reject all negative samples but miss one
required positive sample.

The statement has **52 incident point-line positives and 234 quadrangle
negatives: 286 rows in total**. The number 234 counts only the negative rows.
Incidence is `p-l mod 13 ∈ {0,1,3,9}`. A negative row activates four points with
no three on a line, and the three lines disjoint from those points.

The circuit receives 26 original bits plus one free input computing an OR of a
list of at most two original indices. The suffix is `Monotone2`, and each input
to suffix gate `j` is strictly below `27+j`. A counterexample must use at most
62 suffix gates and pass **all 286 rows**.

## Independent verification

`verify_candidates.py` does not import the search generator or use stored
bit-vector signatures. It enumerates all 8,192 point subsets, filters the exact
quadrangle condition, and evaluates every circuit row with scalar Boolean
operations. It also checks gate types, indices, the free OR, and recorded size.
The verification command exited 0.

| Saved candidate | Free OR | Suffix gates | Missed positives | Accepted negatives | Result |
|---|---|---:|---|---:|---|
| `baseline_0.json` | inputs 13 and 17 | 63 | None | 0 | Passes all 286 rows; meets the claimed bound |
| `baseline_1.json` | inputs 0 and 1 | 63 | None | 0 | Passes all 286 rows; meets the claimed bound |
| `best-62.json` | inputs 13 and 17 | 62 | Point 0, line 12 | 0 | Not a counterexample |
| `multioutput-best-suffix.json` | inputs 3 and 9 | 62 | Point 1, line 0 | 0 | Not a counterexample |

Exact evaluation results are in `independent-verification.json` and the matching
log. No candidate was converted into a Lean proof or submitted.

## Search 1: local changes to a star-cover circuit

The full star cover has 64 gates: 39 neighborhood OR gates, 13 AND gates, and
12 final OR gates. Giving one genuine leaf OR as the free input leaves a
63-gate suffix. Deleting a second leaf OR and redirecting its readers to one
of its operands gives a 62-gate near miss.

`local_synthesis.py` constructs 100 such seeds from both point-star and
line-star covers. Every seed misses one incidence and has no false positives.
`local_synthesis.cpp` first exhausts every one-field edit of these seeds: one
operation or one operand index changes while the other fields remain fixed.
It then performs bounded local simulated annealing with one or occasionally
two field changes at a time. Every evaluation uses all 286 sample bits.

- Budget: 120 seconds after seed loading, including the one-field pass.
- Fixed random seed: `234320261125`.
- One-field candidates tested: 725,400; no witness in this neighborhood.
- Reported total evaluations: 431,380,651.
- Accepted annealing moves: 150,198,512; restarts: 35,885.
- Best result: one missed positive, zero false positives.

The evaluations include repeated candidates. They are not a count of distinct
circuits and are not an exhaustive search of all 62-gate circuits. This search
used same-side free-OR seeds, not all seven possible prefix types.

## Search 2: shared approximate line-neighborhood outputs

The second template separates point processing from the final line gates.
It seeks a 38-gate network on the 13 point bits, producing 13 outputs `H_l`.
Each output must be true on the four singleton points incident to line `l`
and false on every quadrangle disjoint from `l`. It also explicitly rejects
the nine nonincident singletons. There are 54 disjoint quadrangles per line,
so this gives 67 constrained rows per output, 871 constraints altogether,
on a common set of 247 point assignments.

Such a network, if found, would yield a 63-gate full separator by adding
`line_l AND H_l` for each line and joining those 13 terms with 12 OR gates.
The first point gate is constrained to remain a raw OR, so it could be supplied
for free: 37 remaining point gates + 13 ANDs + 12 ORs = 62 suffix gates.
Higher-degree terms on point inputs outside the constrained samples are allowed.

`multioutput_synthesis.cpp` starts from 52 one-deletion versions of the
39-gate exact OR network. The output for each line is selected from all
available wires by its sample score.

- Budget: 120 seconds after seed construction.
- Fixed random seed: `38234320261125`.
- Reported evaluations: 9,307,519.
- Accepted moves: 3,133,643; restarts: 1,328.
- Best weighted score: 4, representing one missing required singleton.

The saved point-only network is in `multioutput-best.json`. The independent
checker translates it into the actual 27-input suffix, records that suffix in
`multioutput-best-suffix.json`, and checks the original 286 rows. It remains a
near miss, not a witness. This template is a restricted search family.

## Existing reductions and a precise cut caveat

The following map was checked against the actual theorem statements and the
desk snapshot updated at 2026-11-25 04:20:08.808 UTC. Exact child statements and
source URLs are recorded in `child-map.json`.

| Existing reduction | Finished child | Remaining child |
|---|---|---|
| [R-meta-2343-1](https://github.com/open-goat/pequalnp-proofs/blob/main/lean/PEqualNP/Outside/R_meta_2343_1.lean) | L-meta-3801: normalization to seven prefix types | L-meta-3803: bounds for those types |
| [R-meta-2343-509](https://github.com/open-goat/pequalnp-proofs/blob/main/lean/PEqualNP/Outside/R_meta_2343_509.lean) | L-meta-4676: normalization to twelve affine representatives | L-meta-4678: bounds for those representatives |
| [R-meta-2343-811](https://github.com/open-goat/pequalnp-proofs/blob/main/lean/PEqualNP/Outside/R_meta_2343_811.lean) | Neither child was checked in that snapshot | L-meta-5755: a direct AND-to-AND input exists; L-meta-5757: no such direct input exists |

The last cut's comment describes a “two-level” case, but its formal second
condition only excludes a **direct** AND-produced input to an AND. It still
allows an AND-to-OR-to-AND path. The case-split theorem is valid; applying a
no-AND-ancestor or two-level counting theorem to that child would require an
additional normalization argument.

Further open descendants L-meta-6041 and L-meta-6043 isolate same-side free
pairs and mixed flag/nonflag free pairs, respectively. No new normalization
claim or reduction was submitted here. The task sketch's referenced heavy
search notes were absent from the checkout; the known full-size SAT control was
not repeated.

## Reproduction and curated files

Run in a directory containing these files, with Python 3 and a C++17 compiler:

```sh
python3 local_synthesis.py
g++ -O3 -std=c++17 local_synthesis.cpp -o local_synthesis
./local_synthesis 120 > local_synthesis.log
g++ -O3 -std=c++17 multioutput_synthesis.cpp -o multioutput_synthesis
./multioutput_synthesis 120 > multioutput_synthesis.log
python3 verify_candidates.py > independent-verification.log
```

The deterministic seeds and sampling rules are fixed. Runtime budgets mean
iteration counts and final paths can vary with machine speed. To inspect the
saved runs without repeating either search, run only the last verification
command.

The curated archive contains sources, logs, sample data, small baseline and
near-miss circuits, this README, `search-summary.json`, `child-map.json`, and
`manifest.json`. It excludes compiled binaries and the larger regenerated
`seeds.json` and `search-input.txt`. No lease identifiers or private account
data are included. No unsuccessful computation here is a proof of absence.
