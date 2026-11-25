# One bounded63-gate constructive attempt for L-meta-2718

The parent authorized one300-second, single-thread stochastic search while holding the L-meta-2718 lease. Its purpose is to find a concrete circuit meeting the posted partial promise. A valid witness could support the negated-twin route together with accepted sibling2716 and the plane's duality. This directory does not itself contain that logical refutation or an official submission.

## Exact problem

The26 raw inputs are points0…12 and lines13…25 of the order-three plane. Incidence means `p = l + d mod13` for `d` in `{0,1,3,9}`.

`prepare.py` enumerates exactly:

-52 incident-pair positive inputs;
-236 degenerate maximal negative inputs, selected by the posted maximality and degeneracy predicate.

These288 required rows occupy five64-bit words. The other468 maximal negatives are not required by the task and are deliberately not added as constraints. Finding no circuit on these288 rows does not prove a lower bound.

## Search and baseline

`search63.cpp` is a five-word adaptation of the frozen `continuation-11/L-meta-2732/search26/search26.cpp`, itself adapted from the earlier archived `local_search.cpp`. Operations are AND and OR only; every read is an earlier wire. Candidate circuits have63 gates. Raw-wire outputs and repeated gate inputs are permitted by the representation.

The seed generator builds104 known64-gate circuits: both point-star and line-star decompositions,13 center rotations, and four OR association/order variants. It bypasses each of the64 gates to either operand, leaving13,312 distinct63-gate seeds.

The run first examines selected one-field neighborhoods, then uses randomized changes with annealed acceptance and restarts. Evaluation counts include repeated states and are not exhaustive circuit counts. No SAT, exhaustive circuit enumeration, or proof of impossibility is performed.

`run_search.py` imposes a1GiB address-space limit and launches a single300-second process. The source has a time check and responds to termination signals; the runner has a315-second outer timeout.

## Independent finite-predicate verification

`verify.py` independently loops over all8192 point subsets and evaluates the task's literal quantified maximality and degeneracy conditions. It evaluates each selected negative input and all52 incident positive inputs. It also computes both syntactic additive side-degrees using the public sum-at-AND/max-at-OR convention.

Before the search, this verifier accepted the known64-gate baseline: zero positive or negative errors, point degree1 and line degree1. The64-gate baseline exceeds the63-gate budget and is not a task witness.

After the search, the runner invokes this verifier on any found candidate and on the best saved circuit. A successful finite check would still require Lean formalization, the exact negated-twin argument, and official validation.

## Reproduction

```
python prepare.py
python verify.py known-64.json
g++ -O3 -march=native -std=c++17 search63.cpp -o search63
python run_search.py
```

The random seed is fixed in the C++ source. A wall-clock-limited heuristic is not expected to reproduce the identical number of iterations on different machines. `process-result.json` binds the run to the source hash, timestamps, budget, and exit code. `run-summary.json` records the observed search outcome.

The executable, generated seeds, process ID, and compiled Python cache are reproducible intermediates; publication can omit them. Source scripts, problem and baseline, best-circuit verification, logs, and result records preserve the substantive evidence.

## Observed result

The run completed with exit0 from2026-11-25T10:08:45.892938+00:00 to2026-11-25T10:13:46.013150+00:00, using300.120 wall seconds. It performed1,154,454,451 repeated-state evaluations and9,611 restarts. **No candidate was found.** No repeat run was launched.

The independent literal verifier examined all8192 point subsets for the saved best63-gate circuit. It rejected all236 required negative inputs, but failed the incident positive pair(point0,line4), mask131073. Its point-side and line-side syntactic degrees are both1. It is therefore invalid for the posted premise and proves neither2718 nor its negation.
