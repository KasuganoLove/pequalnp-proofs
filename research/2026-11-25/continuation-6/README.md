# Continuation 6 — checked preprocessing for L-meta-5126

Date: 2026-11-25, Asia/Singapore (UTC+8).

This checkpoint records completed research for L-meta-5126. **The full task is
still unproved here.** No task refutation or official checker acceptance is
claimed. Five research files passed ordinary Lean compilation; one of those
is explicitly a partial symbolic-profile development.

## Exact question

For a bipartite graph with no four-cycle, an `IsLeastAO` circuit computes its
edge function using exactly-two-input AND/OR gates. An AND gate is called
`junk` when it is true on some input where the graph edge function is false.

The task assumes that no such least circuit has exactly one junk gate. It asks
whether a least circuit can have exactly two junk gates when both are false on
every singleton input. The complete posted Lean statement is in `statement.txt`.
Upstream `L_meta_3760` already proves the supplied one-junk premise; this does
not itself settle the two-junk conclusion.

## 1. Normalization now preserves the needed input condition

`lean/Pnp5126TopForm.lean` extends the construction of upstream L-meta-1501.
The original result gives a same-size least circuit in `TopForm`, preserving
the number of junk gates. Its public conclusion did not explicitly preserve
the singleton-off condition needed here.

The new `exists_top_form_preserving_tests` proves a more general invariant:
for any selected family of graph-negative inputs, rejection of those inputs
by every AND gate is preserved by the normalization. The proof uses the
existing `V2_gateval` equality on negative inputs, retains the operation of
every surviving gate, and notes that the new final gate is OR.

`exists_top_form_preserving_unit_off` specializes the family to singleton
inputs. `normalize_two_junk` handles the empty-graph boundary as well: if the
graph has no edges, a zero-gate false circuit computes its function, so a least
circuit cannot have a positive number of junk gates. Consequently the exact
two-junk hypothesis yields a same-size least TopForm circuit with exactly two
junk gates, still both false on all singleton inputs.

This normalization result does not need bipartiteness, the four-cycle
condition, or the one-junk premise. It does not remove either junk gate.

## 2. Negative witnesses need only two or three variables

`lean/Pnp5126OwnershipWitness.lean` proves three structural results for any
`IsAO2` circuit with exactly two junk gates, ordered as `g < t`:

| Checked theorem | Conclusion |
|---|---|
| `two_junk_off_witness` | Every junk gate has a graph-negative witness with exactly two or three active variables. |
| `two_junk_first_pair` | The earlier junk gate has a graph-negative witness with exactly two active variables. |
| `second_pair_or_shared_triple` | The later gate has its own negative pair witness, or an independent triple makes both junk gates fire. |

These results require neither leastness nor TopForm, and neither bipartiteness
nor the absence of four-cycles. On a graph-negative input all clean AND gates
are false. Before the first junk gate, a true wire therefore has a singleton
witness through OR gates. Before the second, a true wire has either a singleton
witness or the same fixed pair witness for the first gate. Reusing that pair
limits the combined witness to three variables. Singleton-off excludes support
sizes zero and one.

`lean/Pnp5126Shape.lean` composes the normalization and witnesses. It gives a
same-size least TopForm representative with an earlier pair witness and the
later pair/shared-triple alternative. Its `top_form_suffices` also proves that
an exclusion established in TopForm would suffice for the original model.
The remaining configurations are not proved impossible.

## 3. A kernel-checked scope counterexample

The task sketch informally suggests that both singleton-off junk gates must
be products of two pure OR factors. `lean/Pnp5126Sanity.lean` verifies why that
step needs an additional leastness or non-nesting argument.

With four variables `a,b,c,d`, let the graph have edges `ac` and `ad`, and set

\[
H=(a\lor b)\land(c\lor d),\qquad
J=H\land(a\lor c)=ac\lor ad\lor bc.
\]

The six-gate circuit outputs `a AND J`, exactly `ac OR ad`. Lean's kernel checks
all of the following:

- the graph is bipartite and has no four-cycle;
- the circuit is `IsAO2`, correct on every input, and in `TopForm`;
- every gate is in the output cone;
- exactly `H` and `J` are junk, and both are false on every singleton;
- `H` lies in the strict input cone of `J`;
- `J` cannot be written as `OR(A) AND OR(B)` for disjoint variable sets `A,B`;
- a two-gate competitor computes the same graph function, so the six-gate
  circuit is **not least**.

All finite Lean checks use `decide +kernel`. This example **does not refute
L-meta-5126**. It shows precisely that correctness, TopForm and singleton-off
alone do not establish the sketch's rectangle claim.

The independent Python audit also contains a second nonminimum model in which
two junk gates have empty individual `wmax` sets but filter each other's
errors. It prevents the unsupported inference that an empty `wmax` makes a
junk gate useless while another junk gate is present. That second example has
Python validation only; it is not claimed as a Lean theorem here.

## 4. Checked partial symbolic profiles

`lean/Pnp5126OwnershipProfile.lean` defines a fixed raw-input support plus a
Boolean flag for the earlier junk gate. OR gates join these profiles. Its
`profile_correct` proves the exact semantics on graph-negative inputs before
the second junk gate; `flag_before` prevents the selected atom from appearing
before its gate.

The already-launched ordinary compilation finished with exit 0, with two
unused-variable warnings. The development stops there. It does **not** contain
the packaged two-gate semantic-form theorem, the disjointness conclusion, or
the proposed universal inclusion of the later gate's negative signature in the
earlier gate's signature. No `.olean` was generated for this partial module.

## Existing results and remaining gap

The coverage audit found no complete argument for the remaining two-junk
configurations:

- L3760 closes the one-junk premise only.
- L5138 handles a particular pair of 2-by-2 configurations with an explicit
  path, private input OR wires, a shared downstream AND, restrictions on direct
  readers, and deletion-essential edges. Those premises are not established by
  the general 5126 hypotheses.
- L5391 supplies a deletion-and-repair inequality for a nested pair. Leastness
  still requires a sufficiently strong lost-edge bound to yield a contradiction.
  Replacing two junk gates by zero at the same size does not contradict a
  hypothesis excluding exactly one junk gate.
- The advertised internal ten-case split was not found in the public checkout;
  exhaustive coverage of its branches has not been verified here.

`structural-audit/` preserves the bounded upstream comparison and both finite
models. It includes the correction that newly added L6037 deletes an **OR**
gate, not an AND gate.

## Validation, provenance and handoff

`validation.json` records source hashes, observed individual compiler exits,
and the distinction between complete research lemmas and the partial profile
development. `logs/` contains the actual retained compiler output. The TopForm
and Shape commands returned exit 0 with empty output in the execution tool;
they do not have invented compiler-log files. No aggregate rebuild or new
proof compilation was started after the lease-stop notification.

The environment is the project's pinned Lean 4.36.0 and Mathlib dependency.
All proof bodies use no admissions or new axioms. This checkpoint did not run
the official strict single-file checker or a new full dependency-axiom audit.
The modules are research artifacts, not a completed official submission.

At 05:07:37 UTC the desk successfully renewed the lease until 05:27:37 UTC.
At 05:16:39 UTC it instead returned HTTP 410 with `no such live lease: it
expired or was released`. Work on that lease stopped. The successful renewal
responses retained the same lease identifier; the cause of the early loss is
not established. No private lease identifiers are included in this archive.

After the default allocator returned another already-held task, an independent
allocation using the documented `another=1` option supplied L-meta-1884. That
is separate work. The earlier 2343 checkpoint remains frozen in commit
`1806125da38080a0df1624f245c850837b6093ba`.

Attribution: TopForm normalization reuses upstream L1501's construction and
induction. Wire semantics in the witness development reuse the prior 1031/2343
research with attribution to L2668 and L1499 / PR3112. The added preservation
invariant, small-support witnesses, their compositions, and the explicitly
qualified scope checks are the work of this continuation.
