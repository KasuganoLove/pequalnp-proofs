# L-meta-650: one bounded five-point synthesis attempt

## Outcome and scope

The single authorized CaDiCaL run returned **UNKNOWN** after 300 seconds. It found no 23-gate circuit and produced no UNSAT verdict or certificate. Consequently this directory contains no 63-gate witness for L-meta-650 and no proof of its negation. No official proof submission follows from these files.

The run began at `2026-11-25T10:53:38.296817+00:00` and ended at `2026-11-25T10:58:38.362299+00:00`. The outer wall duration was 300.065 seconds. The process exited 0 after its solver time limit, without hitting the 315-second outer timeout. The log records 2,606,648 conflicts, 14,468,731 decisions, and 161.66 MB maximum RSS. The enforced address-space limit was 1 GiB. This was one run, with no repeat.

All verification results here are ordinary computation. The Lean exporter evaluates the project's existing CNF definitions; it is not a Lean proof of circuit existence or nonexistence. No new theorem was submitted to the strict checker.

## Exact local problem

The full task has 13 point inputs, 13 line inputs, and 52 incidence edges. Its exact labels are read from `../../statement.txt`; the relation is `(point + lineIndex) % 13 ∈ {0,1,3,9}`. The selected points are `{0,1,4,5,7}`. Points `{0,4,5,7}` lie on line 22, while point 1 does not. All 13 line inputs are retained.

The local raw-to-full mapping is:

```text
[0,1,4,5,7,13,14,15,16,17,18,19,20,21,22,23,24,25]
```

This gives 18 essential raw inputs and 20 edges. After removing the eight pendant line inputs, the core is four internally disjoint paths of length three between two endpoints. The search includes the entire 18-variable function, including its leaves; it does not assume that an arbitrary smaller core circuit permits cheap leaf restoration.

`prepare.py` enumerates all 32 subsets of the five point inputs. For each subset it takes every avoiding line, then checks maximality by whether the selected lines cover every omitted point. There are exactly 31 maximal false inputs. Together with the 20 minimal positive edge inputs these give 51 rows. For a monotone circuit, correctness on this complete boundary implies correctness on every local input.

`baseline-24.json` is the usual five-star implementation: four gates per degree-four star and four OR gates to join the five outputs. Independent exhaustive evaluation checked all 262,144 local assignments, with zero false positives and zero false negatives. Its 24 gates exceed the search budget.

## Why one local saving would suffice

`assemble.py` maps the local raw inputs into the exact task labels, shifts the local gate wires from `18+j` to `26+j`, then adds the eight remaining point stars. Each added star uses four gates and one OR gate to join the accumulator. The extension therefore costs exactly 40 gates:

- A 23-gate local witness would yield a 63-gate full circuit.
- The existing 24-gate baseline yields a 64-gate full circuit.

The baseline assembly was checked against all 52 positive rows and all 704 maximal negative rows of the full graph. To obtain those negatives, the program examined all 8,192 point subsets and checked maximality explicitly. A separate C++ evaluator then exhausted all 67,108,864 full assignments and found no errors. This validates the label mapping, wire shifts, and assembly on the baseline. The 64-gate result is still over budget and is not a witness for the task.

## Exact encoding and variable renaming

`ExportFivePointCNF.lean` calls the unmodified project definition

```lean
PEqualNP.Defs.LratEncoding.enc2 18 23 label rows
```

The exported formula has 479,425 clauses. Its largest variable number is 49,815,341 because the project encoding allocates blocks using `2^18`, even though only 51 rows are present.

`densify.py` gives each used variable a fresh consecutive number. It preserves every literal sign and every clause in order; a separate inverse pass compares every renamed clause against its original. The resulting formula has 5,033 variables and the same 479,425 clauses. This is only a bijective renaming, with no added constraints or omitted clauses.

| Artifact | SHA-256 |
|---|---|
| Sparse formula | `2bbdd7682aac9a454ae22ff0be9dfe4b19432345e6ec4a8083369e579d87eeba` |
| Dense formula | `46777d9ab73af2e37d6b0a5b7a30d329058163b354098a1eb1c358294762c489` |

The sparse and dense CNFs can be regenerated and need not be included in a public archive. `encoding.json` records their hashes and the checked renaming properties. `dense-to-sparse.json` is the inverse variable map.

## Reproduction

Use the project's pinned Lean environment and the source/definition hashes in `provenance.json`. Preserve the directory layout so that `../../statement.txt` remains the original L-meta-650 statement. The following commands describe reproduction; they are not evidence of an additional solver run.

```sh
export PNP650_DIR=/absolute/path/to/L-meta-650/independent/five-point-sat
export PNP650_LEAN=/absolute/path/to/pequalnp-proofs/lean
python "$PNP650_DIR/prepare.py"
cd "$PNP650_LEAN"
lake env lean -j1 --run "$PNP650_DIR/ExportFivePointCNF.lean" "$PNP650_DIR/five-point-23-sparse.cnf"
python "$PNP650_DIR/densify.py"
export PNP650_CADICAL=/absolute/path/to/the/pinned/cadical
python "$PNP650_DIR/run_sat.py"
```

The archived runner retains the original solver path as its default. After the recorded run, only the optional `PNP650_CADICAL` path override was added for portability; arguments, limits, and outcome handling are unchanged. Running it again overwrites `cadical.log` and `sat-result.json`, so preserve the original evidence first.

The completed baseline validation can be reproduced separately without solving:

```sh
python "$PNP650_DIR/verify18.py" baseline-24.json
python "$PNP650_DIR/assemble.py" baseline-24.json
c++ -O3 -std=c++17 "$PNP650_DIR/verify_all.cpp" -o "$PNP650_DIR/verify_all"
"$PNP650_DIR/verify_all" "$PNP650_DIR/full650-baseline-24.txt"
```

If a future, separately authorized run finds a model, `decode_model.py` checks every CNF clause before decoding it. `verify18.py` then checks every local assignment, and `assemble.py` plus `verify_all.cpp` check the full assembled function. Those model-dependent checks were **not run** here because no model exists. A successful computational witness would still require the project proof and official acceptance workflow.

## Provenance and publication

The encoder is the upstream `PEqualNP.Defs.LratEncoding.enc2` from the Apache-2.0 pequalnp-proofs repository. This work adds the exact geometric instance, exporter, reversible variable renaming, bounded runner, decoder, and independent evaluators. CaDiCaL is the executable bundled with the project's Lean 4.36.0 toolchain. Existing certificates and proofs are not claimed as new work.

The curated manifest includes source, small JSON evidence, and the solver log. It omits the generated CNFs, executable, process-ID file, and caches. No lease credentials or authenticated session data are needed to reproduce this attempt.
