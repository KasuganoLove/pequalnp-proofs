# L-meta-9219: exact 10-gate representation search

## Result

The single authorized 300-second CaDiCaL run returned **UNKNOWN**. It found no circuit and produced no UNSAT verdict or certificate. No witness verification, Lean proof, or official submission resulted from this run.

The run was from `2026-11-25T11:18:05.629901+00:00` to `2026-11-25T11:23:05.671742+00:00`, with 300.042 seconds wall time, exit code 0, 3,367,306 conflicts, 5,503,895 decisions, and 60.56 MB maximum RSS. The enforced address-space limit was 1 GiB; the solver's 300-second limit ended the run before the outer 315-second timeout. This directory records one run only.

## Exact task semantics

The target is the public statement in `../statement.txt`:

```lean
PEqualNP.Represents.RepSizeAtMost
  (fun u v : Fin 5 => (7586366 : ℕ).testBit (5 * u.val + v.val)) 10
```

Raw inputs 0 through 4 represent the left vertex, and inputs 5 through 9 represent the right vertex. Only the 25 assignments with exactly one true input in each half are constrained. This is not a request to compute the full Boolean graph edge function on all 1,024 assignments.

The matrix is:

```text
0 1 1 1 1
1 0 0 0 1
0 0 0 0 1
1 1 1 0 0
1 1 1 0 0
```

There are 13 positive entries and 12 negative entries. `prepare.py` derives each row mask as `(1 << u) | (1 << (5 + v))` and its label directly from bit `5*u+v` of 7586366. `problem.json` records the exact labels, masks, and statement hash.

## Encoding

`ExportCNF.lean` evaluates the unmodified upstream definition `PEqualNP.Defs.LratEncoding.enc2 10 10 label rows`. It produced 34,301 clauses with largest variable number 89,871. The exporter is an ordinary Lean program, not a proof of existence or nonexistence.

`densify.py` bijectively renumbers all actually used variables. A separate inverse pass verifies every clause and literal, preserving signs and order. The solver formula has 1,121 variables and the same 34,301 clauses.

| Formula | SHA-256 |
|---|---|
| Sparse official encoding | `d3bb9591c4dd88db1579961981bb7e90d0485b9bf61fd30f8bacaf7d5722ce70` |
| Dense solver formula | `8973f76caf97006a0ceab4d58b807c09d16fe24d5620a323ad671fb5e89d9d8d` |

The encoder allows constant-true padding as in the project normal form. Such a slot would be decoded as an empty AND gate and counted toward the budget. Forward/default-false sources follow the same encoding conventions.

## Model checking pipeline

`decode_verify.py` is prepared for a future SAT result. It first checks every CNF clause against the solver's assignment, then decodes an operation and two sources for each slot and the selected output. It independently evaluates all 25 `oneEach` assignments against the literal 7586366 bit expression and writes `candidate-10.json` and `verification.json` only after every entry agrees.

No SAT model exists for the recorded run, so this model-dependent checker was not executed and there is no candidate file. Any future computational witness would still need a Lean proof and the official submission workflow.

## Reproduction

Use the project's pinned Lean 4.36.0 environment and the dependencies recorded in `provenance.json`. Preserve `../statement.txt` relative to this directory. These are reproduction instructions, not evidence of a second solver run:

```sh
export PNP9219_DIR=/absolute/path/to/L-meta-9219/sat
export PNP9219_LEAN=/absolute/path/to/pequalnp-proofs/lean
python "$PNP9219_DIR/prepare.py"
cd "$PNP9219_LEAN"
lake env lean -j1 --run "$PNP9219_DIR/ExportCNF.lean" "$PNP9219_DIR/representation-10-sparse.cnf"
python "$PNP9219_DIR/densify.py"
export PNP9219_CADICAL=/absolute/path/to/the/pinned/cadical
python "$PNP9219_DIR/run_sat.py"
```

The runner overwrites `cadical.log` and `sat-result.json`; preserve the original evidence before an independently authorized repetition. The generated CNFs, inverse map, and process-ID file are omitted from the curated manifest because the supplied source regenerates them.

The CNF definitions belong to the upstream Apache-2.0 pequalnp-proofs repository. The instance builder, exporter wrapper, renaming check, bounded runner, and model verifier were prepared for this task, adapting the previously archived L-meta-650 tooling. No upstream proof or solver is claimed as new work.
