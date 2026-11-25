# L-meta-10487: signed binary-gate search and literal replay

These are completed ordinary C++ computations supporting the proof attempt for
positive twin **L-meta-10486**. Neither executable is a Lean certificate. At the
time this checkpoint was frozen, the parent agent was adapting the existing
Lean checker; the task remained live and no official verdict is asserted here.

## Exact problem

`problem.json` records the fifteen edges of the graph on seven raw variables.
The target is the disjunction of its edge monomials. All 128 assignments are
used: 114 are positive and 14 are negative. Thus separation can equivalently
be tested on all 1,596 positive/negative pairs. There is no sampling of the
Boolean domain.

Both programs search for a computation with at most **10 binary AND/OR gates**
while allowing **arbitrarily many free NOT operations**. This is broader than
the public at-most-one-NOT premise. The graph, not that premise, determines the
search instance. The source allows a complement of a stored signal without
charging a binary gate.

## Recorded results

| Implementation | Recorded outcome | Search time | Visited nodes | Separation tests |
| --- | --- | ---: | ---: | ---: |
| `probe.cpp` | `EXHAUSTED_NO_MODEL` | 2.54147 s | 636,510 | 22,619,227 |
| `literal-probe.cpp` | `EXHAUSTED_NO_MODEL` | 31.4768 s | 6,420,705 | 449,694,588 |

The optimized run started at `2026-11-25T13:00:37.265192+00:00`, finished at
`13:00:39.888552+00:00`, and exited 0 under a 1 GiB address-space cap.
`run.json` preserves that exact process record; `result.json` preserves the
program output. The literal replay also exited normally before its 60-second
internal deadline and reported peak RSS 1,536 KiB. Its output and progress are
in `literal-result.json` and `literal-progress.log`. An exact UTC process
record was not separately captured for the literal run.

`EXHAUSTED_NO_MODEL` means the implementation completed its finite search.
It is stronger than a timeout report, but it is **not an independently checked
UNSAT certificate or a kernel theorem**. The two implementations agree.

## Relationship to the existing Lean search

The generic signed live-wire method comes from checked upstream
`L_meta_9539.lean`. Its own header attributes the adaptation to L9136, L9146 by
partymejker, L8633 by k-sandhu, and the earlier L8463/L1449 framework, under the
repository's Apache-2.0 license. This checkpoint does not claim the generic
method as new work. The fresh work is the seven-variable instance, the two
ordinary implementations, and the validation data.

The optimized program stores truth functions as 128-bit integers, canonicalizes
them modulo complement, sorts live frontiers, and memoizes fully failed states.
It skips constant results and results already available modulo complement.
All seven raw variables are independently checked essential; therefore every
proper raw-input sublist fails separation. An independent source review and
truth-table audit are preserved in `independent-review.md` and
`independent-data-audit.json`. The review explicitly identifies the extra
normalization lemmas that would be needed to justify this optimized engine
inside Lean.

The literal replay avoids those extra formal obligations. It has no
memoization, complement canonicalization, sorting, constant skipping, or
duplicate skipping. It follows the L9539 ordered pairs, four operations, and
four operand-retention cases. Its acceptance test is a singleton containing
the target or its complement. It tests every raw-input sublist; only the full
sublist passes separation. The numeric traversal of those sublists differs
from `List.sublists`, but the one recursive root is the same.

The literal program represents functions on the 128 distinct assignments
instead of materializing 3,192 duplicated sample bits. Each assignment occurs
in the complete positive/negative pairing, so equality and separation have
the same truth value in both representations. This observation and the
ordinary replay support feasibility; they do not replace the Lean proofs of
the compiler and search completeness. C++ running time is not a bound on the
Lean evaluation time.

## Intended formal consequence

If the Lean checker establishes rejection for this exact instance, its
generic completeness theorem yields at least 11 binary AND/OR operations in
any circuit computing the target, with NOT operations free. A circuit having
a NOT consequently has at least 12 total gates and can be replaced by the
separately verified 12-gate monotone control. A circuit without NOT is already
monotone. This is the route to positive twin 10486; **the formal consequence
is conditional in this checkpoint**.

## Reproduce without overwriting the recorded outputs

From this directory, with a C++20 compiler supporting `__uint128_t`:

```sh
mkdir -p reproduction
c++ -std=c++20 -O3 probe.cpp -o reproduction/probe
c++ -std=c++20 -O3 literal-probe.cpp -o reproduction/literal-probe
(ulimit -v 1048576; ./reproduction/probe 10487 10 60) > reproduction/result.json 2> reproduction/stderr.log
(ulimit -v 1048576; ./reproduction/literal-probe) > reproduction/literal-result.json 2> reproduction/literal-progress.log
```

`run.py` is also retained as a process wrapper. It was extended after the
initial 10487 run to select a task/budget and report peak RSS; it still invokes
the same frozen optimized engine for 10487. Its other supported graph,
10696, timed out in a separate authorized run and is documented in that task's
own checkpoint. Running the wrapper in place overwrites its selected task's
recorded output, so the reproduction commands above use a separate directory.

The curated manifest includes source, small exact problem data, recorded
results, and independent reviews. It excludes compiled binaries and does not
include a Lean or LRAT proof certificate.
