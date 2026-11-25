# Continuation 5 — L-meta-2343 finite-sample constraints

Date: 2026-11-25 (Asia/Singapore, UTC+8).

This checkpoint continues work in `KasuganoLove/pequalnp-proofs`. It contains
formal research completed while working on L-meta-2343, a bounded circuit search, and a
read-only audit of the previous tasks. It does **not** solve L-meta-2343 or P vs NP.

## The exact task

The task gives a monotone, fan-in-at-most-two circuit 27 initial wires. The first
26 wires are 13 point bits and 13 line bits of the order-three projective plane.
The last initial wire is a free OR of at most two indices in the 26-bit input;
an out-of-range index reads false. Incidence is `p - l ∈ {0,1,3,9}` modulo 13.

The circuit must accept all 52 incident point-line pairs and reject all 234
quadrangle inputs. A quadrangle activates its four point bits and the three
line bits for lines missing all four points. There are **286 test inputs**.
The required conclusion is **at least 63 counted gates after the free OR**.
The unmodified posted statement is in `L-meta-2343/statement.txt`.

## Formal progress

### Sample-preserving erasure and minimal normal form

`Pnp2343Pruning.lean` supplies an actual gate deletion, using the project's
`CircuitMoves.eraseGate` machinery through its bypass construction. A gate can
be replaced by an earlier wire if the replacement is true whenever the gate is
true on positive samples, and if the gate is true whenever the replacement is
true on negative samples. The operation removes exactly one gate, preserves
both sample labels, and preserves the earlier-wire condition.

Consequently, a least separator can be chosen with exactly two distinct,
earlier inputs at every gate. At any AND gate, the two operand signatures on
the negative samples are incomparable. At any OR gate, the two operand
signatures on the positive samples are incomparable. The minimum is taken
among circuits on the **same 27 input wires and the same fixed free-OR samples**.

`Pnp2343PruningProductive.lean` proves that every gate in a least sample
separator fires on some positive sample. In particular, if an AND gate directly
reads two initial wires, those wires must occur together in a positive sample.
This is productivity; it does not assert that the gate owns a new graph edge.

### A conditional 63-gate bound

`Pnp2343QuadClean.lean` covers every nonedge pair of raw variables, including
repeated endpoints, by a quadrangle negative. The finite witness tables are
reused with attribution from upstream L-meta-5272. This connects the negative
family to the finite AND tests from the previous 1031 research.

`Pnp2343CleanCost.lean` then composes those tests with upstream L-meta-4101's
existing graph-counting result. Its budget is

\[
|E|+|T|\leq |C|+1,\qquad |E|\geq52,\quad |T|\geq13,
\]

so an ordinary 26-input circuit satisfying the additional AND condition needs
at least 64 gates. This reuses the existing counting result and plane geometry.

`Pnp2343FreeOr.lean` charges the free OR as one ordinary gate and proves the
exact input and wire-index bridge. It permits empty, singleton, repeated, and
out-of-range free-OR indices. It concludes **63 gates under the extra hypothesis
that every AND gate rejects every quadrangle negative**.

The original task only says that the circuit's output rejects the negatives.
An internal AND can fire on a negative and be filtered later. Thus the extra
condition remains a real mathematical gap.

### Necessary shape of any counterexample

`Pnp2343CounterexampleShape.small_normal_shape` combines the preceding results.
If a counterexample with fewer than 63 gates exists, there is a no-larger least
binary separator with an AND gate whose operands realize the following profiles
on **three distinct quadrangle negatives**:

| Negative sample | Left operand | Right operand |
|---|---|---|
| `Q11` | true | true |
| `Q10` | true | false |
| `Q01` | false | true |

The conjunction fires on `Q11` and must be filtered later because the output
rejects all three inputs. The other two samples prevent either operand from
replacing the conjunction. This is a proved restriction on counterexamples,
not a proof that all counterexamples are impossible.

`Pnp2343SignatureRanks.lean` gives strict local set and cardinality constraints.
Writing `N(w)` and `P(w)` for the negative and positive samples firing on wire
`w`, respectively, a minimum separator satisfies

\[
\begin{aligned}
g=a\land b&\implies |N(g)|+1\leq\min(|N(a)|,|N(b)|),\\
g=a\lor b&\implies \max(|P(a)|,|P(b)|)+1\leq |P(g)|.
\end{aligned}
\]

The module also proves the corresponding strict set inclusions. These bounds
are local: intervening gates of the other operation and shared subcircuits
prevent an immediate sum into the desired total gate bound.

## Search and existing reductions

The `L-meta-2343/search/` directory records bounded searches, their exact
programs and inputs, and an independent checker. The search starts from known
star-cover circuits and tests local repairs of 62-gate suffix near misses.
Failure to find a witness in these neighborhoods is not a lower-bound proof.
See its README and machine-readable summary for final budgets and results.

The three live reductions of L-meta-2343 are already occupied. Their branches
normalize the free OR to seven projective representatives, normalize to twelve
affine representatives, or split on a **direct** AND-to-AND input. Absence of a
direct AND-to-AND input still permits an AND-to-OR-to-AND path; it is not the same
as the previously solved condition of no AND ancestor of an AND.

## Verification and reuse

See `L-meta-2343/validation.json` for the final frozen hashes and ordinary Lean
compiler exit codes, and `L-meta-2343/logs/` for their output. Compilation uses
the project's pinned Lean 4.36.0 and Mathlib revision. The modules deliberately
reuse upstream theorems and are research modules, not a single-file official
submission. No official strict-checker acceptance or upstream PR is claimed
for this checkpoint.

To reproduce after preparing the pinned project's normal Lean/Mathlib cache:

```bash
python research/2026-11-25/continuation-5/L-meta-2343/reproduce.py \
  /absolute/path/to/pequalnp-proofs/lean \
  --logs /absolute/path/to/reproduction-logs
```

The script checks the toolchain, manifest, all 85 `Defs` source modules, and the
reused L4101 source against `dependencies.json`. It copies the archived research
modules into the checkout's `lean/` directory, refusing to overwrite different
existing files, and compiles them in dependency order. If needed, it first
builds the imported L4101 module. It also runs a research-only axiom audit of
the main theorems. The complete project cache must already be available; the
script does not change dependency versions or install packages.

The previous `Pnp1031OwnershipFinite.lean` is copied unchanged for reproducible
imports. The erasure and normalization infrastructure explicitly credits its
upstream sources. New contributions here are the finite-sample erasure
criterion, its consequences and exact task compositions; the existing
quadrangle tables, vertex-cover bound, and clean-circuit count are not claimed
as new results.

The `upstream-audit/` directory gives timestamped observations of 1031, 1772,
7019 and newly merged counting lemmas. In particular, another author's PR for
7019 is distinct from our previously checked but unsubmitted source. The audit
does not infer authorship beyond the public evidence.

## Remaining step

The unresolved case consists of circuits with internal AND gates that fire on
quadrangle negatives and are subsequently filtered. A complete proof must
bound the savings from this behavior, or a refutation must exhibit a circuit
passing all 286 inputs with fewer than 63 counted gates. The local signature
constraints cannot simply be summed through arbitrary mixtures of AND and OR,
especially in the presence of shared gates.

Use the frozen shape theorem, productivity theorem, and signature constraints
to restrict further synthesis or a charging argument. Do not rerun the same
unrestricted SAT/local searches, assume output rejection implies internal
rejection, or submit a fourth live reduction.

## Handoff state

The final ordinary build completed successfully before the desk rejected a
renewal of the old 2343 lease at 04:53:40 UTC (12:53:40 Singapore time), with
HTTP 410. Work on that lease stopped. The subsequent public step response still
said `leased`, so no claim that 2343 was solved follows from that response.
The next normal allocation supplied L-meta-5126; that is a separate active task,
and this checkpoint is frozen independently of its outcome.
