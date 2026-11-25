# L-meta-4201: exact fixed-OR model for C6

## Result and scope

The six-cycle edge function has **no four-OR implementation in the finite encoding described below**, according to CaDiCaL2.1.2. The solver returned `UNSATISFIABLE` / exit20 in0.21 seconds, with8127 conflicts. No bound on the number of AND gates was imposed.

A positive calibration with the standard five-OR implementation returned SAT / exit10. Its decoded circuit has eight total gates (five OR and three AND), and two independent scalar evaluations checked all64 inputs: first the selected conjunction representation, then the expanded fan-in-two gate list.

This is **solver evidence, not a Lean-certified UNSAT theorem**. The model-completeness argument below is mathematical documentation, not a checked Lean bridge. No DRAT/LRAT certificate was produced or independently verified. The result blocks this proposed small C6 replacement route; it is not a proof of the105-edge projective-plane lower bound in L-meta-4201.

## Why the task needs an OR-count model

L-meta-4201 asks for at least104 OR gates for a specific42-input projective-plane incidence graph. It has no total-gate bound. A search limited to a small total gate count would not exhaust the relevant candidate circuits.

The proposed refutation route was to replace six separate edge terms forming an embedded C6 by a circuit using at most four OR gates. Combining it with the other99 edge terms would use at most `4+99=103` OR gates. This bounded experiment checks whether that C6 component can exist; no full projective-plane synthesis was attempted.

## Finite representation without an AND bound

The graph is the cycle with edges01,12,23,34,45,50. There are six raw inputs and64 assignments.

For each of k ordered OR gates:

1. Each operand is an arbitrary conjunction of a selected subset of raw inputs, outputs of earlier OR gates, and a false signal.
2. The two operands are ORed.
3. After the k OR gates, the final output is another arbitrary conjunction of selected raw inputs and OR outputs, with false also available.

The empty conjunction is true. A conjunction containing false is false. The source selection bits are shared across every input row. Thus the solver chooses a single circuit structure, not a different circuit for each row. A lexicographic ordering of the two selection vectors breaks only the symmetry of swapping the operands of an OR.

Any finite monotone AND/OR circuit can be represented this way after ordering its OR gates and recursively flattening each intervening AND computation. AND is associative and idempotent, so repeated uses become a subset. Missing/future wire references have the model's default false value and are represented by the false signal. Empty AND gates give true. An empty or unary OR can be represented by a binary OR with false. An output behind the final AND layer is flattened in the same manner.

Conversely, each selected conjunction expands to binary AND gates with no OR cost. Empty conjunctions use an empty-input AND gate; false can use an AND reading a safely out-of-range wire, which evaluates false under the task's `Monotone2` semantics. Consequently there is no hidden total-gate limit. Circuits with fewer than k OR gates can be padded by unused OR gates, so UNSAT for the representation at k=4 also concerns the at-most-four case.

## Encoding details and calibration

For each selected source q with row value v, a port is true exactly when every selected source is true. A Tseitin variable represents `q AND NOT v` for a variable-valued source; the port is equivalent to the negation of the OR of these violations. Raw input values are constants per row. Each OR output is constrained equivalent to the disjunction of its two port values, and the final port is constrained to the target graph truth value on all64 rows.

| Instance | Variables | Clauses | Solver result |
|---|---:|---:|---|
| C6 with4 OR gates, arbitrary conjunction ports | 1973 | 8016 | UNSAT,0.21s |
| Fixed standard C6 circuit with5 OR gates | 2776 | 11321 | SAT,<0.01s |

The calibration computes three stars centered at0,2,4:

`x0(x1 OR x5) OR x2(x1 OR x3) OR x4(x3 OR x5)`.

Its three neighbor ORs and two combining ORs account for five OR gates. The saved `c6-k5-calibration-circuit.json` contains the extracted eight-gate circuit and verified conjunction choices.

## Reproduction

The existing Lean toolchain supplied the solver; no packages were installed.

```sh
python3 c6_model.py --k 4
/workspace/scratch/65f339da29fe/pnp-tools/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical -t 120 -w c6-k4.solution c6-k4.cnf > c6-k4.log 2>&1
python3 c6_model.py --k 5 --calibrate
/workspace/scratch/65f339da29fe/pnp-tools/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical -t 10 -w c6-k5-calibration.solution c6-k5-calibration.cnf > c6-k5-calibration.log 2>&1
python3 c6_model.py --decode c6-k5-calibration
```

The two-minute limit applies to the main four-OR search; it terminated immediately. The calibration used a fixed known circuit to test the encoding and extraction, rather than conducting another unconstrained search.

All generated CNFs, variable maps, solver logs, solution-status files, the extracted calibration, and SHA256 manifest are saved. No larger search, lease action, remote mutation, or Lean compilation was performed by this subtask.
