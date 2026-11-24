# L-meta-1405: bounded formula synthesis, no completed proof

This directory records a search for a monotone formula of depth at most six for
the five-cycle edge function after replacing every vertex input by a majority
of three independent Boolean inputs. No formula witness or Lean proof was
obtained. The original assignment remains unresolved by this work.

## Target and relation to the Lean task

Number the inputs from 0 to 14. For `i = 0, ..., 4`, let

`M[i] = majority(z[i], z[i+5], z[i+10])`.

The target is

`F = (M[0] && M[1]) || (M[1] && M[2]) || (M[2] && M[3]) ||
     (M[3] && M[4]) || (M[4] && M[0])`.

The live task is stated abstractly for any family `T(k)` containing every input
at level zero, closed under promotion to the next level, and closed under binary
AND and OR from level `k` to level `k+1`. It asks for this exact `F` to belong to
`T(6)`. An explicit binary formula of depth six would prove that statement by
applying the closure hypotheses. This archive contains only search programs and
their observations; it contains no official proof file and no proof submission.

## Encoding

The complete depth-six binary tree has 64 leaves and 63 internal gates. Every
leaf chooses one of the 15 positive input variables, and every internal node
chooses binary AND or binary OR. Repeating an operand pads a shallower formula to
this full tree, so padding does not lose shallower formulas.

Only the monotone boundary assignments are needed to specify the target:

* 45 minimal true assignments: choose one of the five edges and one of the three
  input pairs that make each endpoint majority true.
* 135 maximal false assignments: choose one of the five maximal independent
  vertex pairs, set all inputs of those two majorities to true, and choose one
  true input in each of the other three majority gadgets.

A monotone function matching both boundaries matches every Boolean assignment.
The scripts nevertheless independently evaluate any returned formula on all
32,768 assignments before writing `witness.json`.

The CNF has one-hot leaf choices and standard gate-value constraints for each
boundary assignment. Gate-child commutativity is normalized by ordering the
minimum input variable in the two child subtrees. The symmetry-enhanced search
also normalizes the first occurrence order of the three copies in each majority
gadget. Its second leaf restriction uses the reflection symmetry of the cycle.
These symmetry rules are search code, not Lean-proved lemmas.

## Recorded results and their limits

`synthesis-sym.log` records the direct C5 depth-six search. It stopped at its
600-second wallclock budget with `sat: null`, after 2,730,625 conflicts. This is
UNKNOWN, not UNSAT. It found neither a formula nor a lower-bound certificate.

`synthesis-split.log` records the final bounded attempt to synthesize the two
depth-five children separately. For an OR root, both children must reject all
maximal false assignments and their positive coverage must together cover all
45 minimal true assignments; one child therefore covers at least 23. For an AND
root, both children must accept all minimal true assignments and their false
coverage must together cover all 135 maximal false assignments; one child
therefore rejects at least 68. The program allocates 210 seconds per root mode.
An inconclusive second-child run excludes its coverage pattern only as a search
heuristic, so exhausting the resulting heuristic search would not itself prove
nonexistence. Both root modes returned UNKNOWN before producing a first-child candidate. The program finished normally after 420.05 seconds without a witness. The final log and `STATUS.json` record the complete observed outcome.

### Four-vertex path calibration

One attempted sufficient construction split the five-cycle into a two-edge
star and a three-edge path. A depth-five formula for the path of four majority
gadgets, combined with the known depth-five star, would yield the requested
depth-six C5 formula. This sufficient shortcut did not supply a construction.

`path4_synthesize_sym.py` asks for depth five for

`P4 = (M[0] && M[1]) || (M[1] && M[2]) || (M[2] && M[3])`,

using 12 inputs grouped as `i, i+4, i+8`. It has 27 minimal true and 27 maximal
false assignments. Its CNF has 3,817 variables and 35,281 clauses. CaDiCaL returned
UNSAT in 147.56 seconds, after 1,147,087 conflicts. No proof trace was generated,
and this result has not been checked in Lean. It is an observation about this
encoding and solver run, not a formally verified lower bound. Even a certified
P4 depth-five lower bound would not settle the original C5 depth-six question.

`calibrate_known.py` constructs the known depth-six formula

`(M[1] && (M[0] || M[2])) || (M[2] && M[3])`.

It checks all 4,096 truth assignments and verifies a corresponding assignment
against every clause of the depth-six version of the P4 encoding: 7,689
variables and 70,897 clauses. `known-path4-calibration.json` records the passing
result. This checks a positive calibration case; it does not certify the UNSAT
run, the symmetry reductions, or the original task.

## Reproduction

Use Python 3 and install dependencies into this directory:

```sh
python -m pip install --target deps -r requirements.txt
python calibrate_known.py
python path4_synthesize_sym.py > path4-synthesis-sym-new.log
python synthesize_sym.py > synthesis-sym-new.log
python synthesize_split.py > synthesis-split-new.log
```

The solver backend is `cadical195` from the pinned `python-sat` package. The
search programs use finite conflict budgets and check elapsed wallclock between
calls. A single solver batch can slightly exceed the requested time. Elapsed
times and search schedules depend on the machine; timeout observations need
not reproduce at exactly the same conflict count.

`synthesize.py` provides the common C5 encoding prefix used by
`synthesize_split.py`; it can also run the baseline search. Its original timer
tail was replaced after discovering that this PySAT/CaDiCaL combination does
not support asynchronous interruption. The corrected tail uses the same
conflict-budget loop as `synthesize_sym.py`; its full baseline search was not
rerun. The split search imports only the unchanged encoding prefix. Initial
manually interrupted runs are excluded from the deliverable results.

The reproduction commands do not run Lean, alter a repository checkout, contact
the task platform, or submit anything. This work was performed against project
checkout `89b96c0f464824a164434fb460926400b9943047` on 2026-11-24. Private lease
material is excluded from this directory and must not be added to the archive.
