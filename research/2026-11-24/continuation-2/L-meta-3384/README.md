# L-meta-3384: OR-reader count under two-wire replacement

## Exact scope

The assigned conclusion counts OR gates whose input list contains raw input 2.
For the permitted AND/OR/NOT operations, `g.op.eval [true,false]` is true
exactly for OR. It is not the count of all gates reading input 2.

The seven-input target has edges 01, 12, 04, 15, 26, 35, 46, 36. It is the
theta graph with endpoints 1 and 6 and paths 1-2-6, 1-0-4-6, and 1-5-3-6.
The task assumes an eleven-gate circuit for this function, together with a
second circuit obtained by replacing selected occurrences of at most two
wire indices by true. The second circuit must compute F OR x0 OR x3.
The goal is at least two OR readers of input 2.

## Calibration circuits

`Pnp3384Calibration.lean` passed local Lean checking with exit 0 and no
errors or warnings. Its finite semantic claims use kernel `decide` on all
128 inputs. It contains:

- An eleven-gate source circuit, with star centres 0, 1, 3, and 6, for which
  replacing the neighbour-OR wires of stars 0 and 3 by true gives exactly
  F OR x0 OR x3. It has exactly two OR readers of input 2. This shows that
  the proposed bound, if proved, is attained and that the hypotheses are
  consistent.
- Another eleven-gate circuit, with star centres 0, 2, 5, and 6, computes
  F with zero OR readers of input 2. It does not come with the required
  replacement property and is not a counterexample to the assigned theorem.

## Monotone computation

`theta_source.py` is copied from the existing continuation study's
`L-meta-1922/theta1922.py`. It embeds the seven inputs into positions
1,2,3,5,6,7,8 of nine-bit truth tables; the unused two bits do not affect the
function. Forward enumeration and backward filtering yield 131 signal
functions occurring in optimal eleven-gate monotone live programs.

The viable source-state counts for remaining budgets 11 down to 0 are:

```text
1, 15, 89, 265, 484, 625, 576, 418, 236, 107, 46, 1
```

`search_viable_pair.py` tracks a source truth table and a modified truth table
for each live signal. It also tracks the globally selected source signals
that can be replaced by true, and the number of OR gates reading input 2.
Each occurrence may independently keep its original input or replace it.
It retains only source transitions from the recorded viable DAG and only
modified states that separate all opposite-output sample pairs in the
necessary direction. For the modified target, the sample pairs use its
minimal positive and maximal negative inputs.

With the OR-reader count restricted to at most one, successive coupled
state counts after each gate are:

```text
60, 693, 1902, 2212, 1501, 779, 380, 114, 0, 0, 0
```

No counterexample survives this computational model. The second search
finished in approximately 0.64 seconds after the source tables existed.
The source forward enumeration took approximately 24 seconds; the backward
filtering is additional work.

This is **not a Lean proof of L-meta-3384**. The finite model uses binary
monotone operations and proper, distinct source signal functions. It needs
a checked normalization argument from the exact circuit representation,
and it does not cover the NOT gates allowed by `FanInTwo`. Its search
tables have not been converted into a Lean kernel certificate.

## General counterexample search

`search_pair.py` encodes eleven topologically ordered gates, both truth
tables, the two selected wire indices, and the OR-reader bound in Z3.
It searches binary distinct-input AND/OR gates, optionally unary NOT.
It excludes duplicate and constant source signals, and puts the output at
the final gate. These restrictions make it a diagnostic search, not a
complete proof for the original Lean model.

Observed results with `z3-solver==5.4.1.0`:

- Monotone model, 60-second limit: `unknown`, timeout.
- AND/OR/NOT model, 120-second limit: `unknown`, timeout.

Neither result is UNSAT. No concrete counterexample was found.

## Reproduce

From this directory:

```sh
python3 theta_source.py --signals --out-dir theta
python3 search_viable_pair.py
python3 search_pair.py --timeout 60000
python3 search_pair.py --timeout 120000 --not-gates
```

The last two commands require the optional Z3 Python package. The first two
use only the Python standard library. The independent circuit check is:

```sh
python3 verify_calibrations.py Pnp3384Calibration.lean
```

From the repository `lean/` directory, use the pinned toolchain and run:

```sh
LEAN_NUM_THREADS=1 lake env lean -j1 ../research/2026-11-24/continuation-2/L-meta-3384/Pnp3384Calibration.lean
```

The single-thread setting was needed for this session's Lake environment.
The proof file imports `Mathlib.Data.Fintype.Pi` and `PEqualNP.Defs`.

## Remaining proof obligation

The useful next step is a formally checked description or enumeration of
all optimal eleven-gate circuits for this theta graph, preserving the
two-wire replacement relationship and the exact OR-reader count. A
normalization that only preserves the original Boolean function is
insufficient: it may change what replacing internal wires by true does.

No complete proof or reduction for L-meta-3384 has been submitted.
