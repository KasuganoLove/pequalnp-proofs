# L-meta-2592: bounded structural audit

Frozen when root stopped this task at 2026-11-25 12:10 UTC. No new theorem,
circuit witness, solver run, Lean build, or public submission was produced by
this subagent. Root owns the lease and its closure.

## Exact target and existing complete reductions

The task excludes a FanInTwo circuit of at most 19 gates computing the full
ten-variable Petersen edge function while containing at least one NOT gate.
The NOT can be dead or redundant. Forward and missing wire reads default to
false; NOT uses only its first listed operand. Neither strict earlier reads
nor essentiality of the NOT is part of the public hypothesis.

The checked theorem L-meta-4725 gives

    15 + NotBracket.notCount C <= C.size.

It therefore excludes five or more NOT gates at this size and leaves the
one-through-four-NOT case. R_meta_2592_271 isolates exactly that residual as
L-meta-4727. The checked L-meta-8295 cuts at the **last** NOT, allowing the
prefix to contain earlier NOTs; its monotone suffix has the whole prefix wire
list and the complement of the prefix output as inputs. Its quantitative
separator residual L-meta-8297 remains necessary. L-meta-7389 normalizes
reads and the output; if the normalization removes every NOT, it only
guarantees a strict size saving, not the unrestricted monotone lower bound.

The remote-status agent's fresh checks at approximately 11:54 UTC found
4727, 8297, and 7391 open. The signed/marked compiler residuals 6062 and
7229 were also still open in its 11:48 desk snapshot. PR9316 proves the
reduction R_meta_4727_17, not its hard child. The remote agent separately
confirmed the canonical free-NOT residual L-meta-2598 remained open.
See ../status-audit/curated/ for source provenance and exact status evidence.

## A stronger cofactor inequality, with its precise limit

The source of checked L-meta-5367 contains a generic constant-propagation
compiler `PEqualNP.Outside.L_meta_5367.R.cind`. Under x0=false, the extra
free input !x0 becomes true. Every gate actively reading raw wire 0 or extra
wire 10 can then be eliminated. For NOT, active inputs are `inputs.take 1`;
for AND/OR, all listed inputs are active. The resulting circuit computes
the nine-variable vertex-deleted Petersen graph.

The original wrapper uses the lower bound 15 for that deleted graph. The
independently checked L-meta-2446 internal theorem `directSplit`, together
with its two discharged root premises, proves the stronger unrestricted
FanInTwo lower bound 16. Its graph deletes Petersen vertex 9; the explicit
`R.lft`/`R.iso` map in L5367 identifies the vertex-0 cofactor with that same
nine-variable graph. Consequently the existing compiler argument supports
the mathematical strengthening

    16 + activeReaderCount(0,10) <= suffix.size.

This was a source-level deduction, **not a new Lean theorem or a new checker
run**. A suffix of size at most 18 consequently has at most two active
readers of these two inputs. This lands exactly in the still-open
one-or-two-reader residual L-meta-5088; it does not prove L-meta-2598 or the
present task. Other/internal NOT placements need additional arguments.

## Scope checks that prevent invalid shortcuts

* `NotPremium.oneNotSize` requires at most one **essential** NOT, whereas
  the public task only assumes a syntactic NOT and permits several.
* The `OneNotPiece` lemmas replace the NOT by constants on its input's two
  level sets. The resulting circuits are only correct on those domains;
  the lemmas do not produce an equally small globally correct monotone
  circuit automatically.
* `FewNotPlan` and its family bounds concern specified multioutput OR
  families. The single Petersen edge function does not meet those family
  hypotheses merely by being monotone.
* The global NOT-removal theorem in `MetaComplexity/L113.lean` requires
  girth at least 9 and separation of degree-at-least-3 vertices. Petersen
  has 5-cycles and adjacent degree-3 vertices. The analogous girth-7
  `EdgeFnFinal` theorem also does not apply.
* For a last-NOT source h and a monotone suffix, h<=F lets one substitute
  true for !h, while F<=h lets one substitute false. Either substitution
  preserves F by monotonicity and the indicated pointwise comparison.
  An arbitrary source h need satisfy neither comparison. There is no
  proof here that the 19-gate bound forces such comparability.

The project-workspace agent separately excluded two particular constructive
architectures (a smaller replacement for the canonical star-preparation
block, and an explicit four-gate Shannon mux). Those results are not a
classification of all allowed circuits and are documented by that agent.

## Provenance

This is an audit and a conditional reuse observation based on existing
repository results, not an original completed lower-bound proof. The main
sources are L4725, L5367, L2446, L7389, L8295, the OneNot helper modules,
Defs/NotPremium.lean, and Defs/MergeCost.lean. L2446's own attribution credits
nine-input certificates adapted from 0xshuzo PR12203 and live-wire/smaller
graph proofs from L1667/L1674/L1677, including PressF10 and zakpgrove.
Repository code is Apache-2.0. No copied third-party proof is included here.
