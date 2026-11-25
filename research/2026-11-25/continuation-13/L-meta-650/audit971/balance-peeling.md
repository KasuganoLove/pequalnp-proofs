# R8793_291 balance：last-AND论证的准确适用范围

Status: the strengthened c=0,o=1 subcase is now ordinary-Lean checked in `formal/Pnp650SingleMixer.lean`; the c=1,o=0 composition remains a mathematical source audit. **Neither proves L-meta-650, its negative twin972, or the whole8793 residual.** No search, strict checker or remote action was run for this audit.

## 1. Exact ledger

Write `t=|tops\centreless|`, `c=|centreless|`, `j=|junk|`, `o=|orN\lam|`, `u=|Ustar|`. The `count` premise of R8793_291 is

    52 + t + 2c + j + o ≤ size + u + 1.

Its missing `balance` premise, under leastness, TopForm, j≥2 and size≤63, is

    13 + u ≤ t + 2c + j + o.

Set e=2c+j+o. The checked cover estimate gives52≤4t+u. Together with size≤63 this implies

    4e + 4 ≤ 5u.

Neither this arithmetic nor j≥2 supplies balance by itself.

## 2. An already available exclusion: c=o=0

`L_meta_5228_aux.LocalBefore.earlier_exception` (969) is generic in n,G,C. A noncentreless top that fires on an uncovered edge produces an earlier gate in `orN\lam`. `LocalMixCore.top_needs_mixing` (1202) even returns a mixing gate. The generic trace of a positive edge to a top is already available (for example the proof framework of L1766).

Consequently,

    Ustar.Nonempty ⇒ centreless.Nonempty OR (orN\lam).Nonempty.

For the current residual, j≥2 and the displayed arithmetic giveu>0. Thus c+o≥1, so e≥3 andu≥4. This excludes the tempting numerical tupleu=3,t=13,c=0,j=2,o=0. The implication does not by itself prove the full balance.

## 3. Ordinary-Lean checked subcase: c=0,o=1 forces u≤1

This composition uses generic APIs from L5228 and works for any bipartite C4-free target. The strengthened conclusionu≤1 requires no maximum-degree bound. The precise checked theorem keeps top-cross adjacency and positive-edge-to-top trace as explicit premises.

Letm be the unique exceptional OR. Sinceu>0 andc=0, the mixing lemma shows thatm is a mixer; mixing is a subset of `orN\lam`, so it is the unique mixer. LetR=`orIn(n+m)`. `LocalSingleMix.routed_single` (1446), applied to a top accepting each uncovered edge, provides:

* R is nonempty;
* m is true on each uncovered edge pair;
* all R variables are false on that pair;
* one endpointw of that edge is a guard: everyr∈R is adjacent tow by a **covered** edge, and for every assignmenty, m(y)∧y(w) impliesF(y).

Fixr∈R. Orient each uncovered edge as `{w,v}`, withw its chosen guard. All guards have the color opposite tor; all leavesv have r's color andv≠r.

Suppose two edges have distinct guardsw0,w1. The leavesv0,v1 are distinct: otherwisew0,w1 would have the two common neighborsr andv0. Alsow0 is not adjacent tov1, since it andw1 already share neighborr. Thus the two edges are disjoint andy=`pairInput w0 v1` is a graph-negative assignment.

Use just these two positive edge-pair inputs as the tests for `LocalMixerTransfer.prefix_transfer` (1931):

* No raw input is true on both disjoint pairs, so the raw-pin condition is vacuous.
* Any nonempty clauseA contained in the neighborhood of some vertex of the covered graph is monochromatic. If it hits both test pairs, it contains both guards or both leaves. Therefore it is true ony.

All remaining premises of `prefix_transfer` are exactly the current unique-exception, c=0, top-cross-adjacency and positive-edge premises. Its conclusion supplies the `lift` argument to `LocalMixerTransfer.mixer_truth` (1961). Since the mixer is true on both test pairs and R is absent on both, this yieldsm(y)=true. The guardw0 then forcesF(y)=true, contradicting the chosen nonedge.

Hence every uncovered edge has the same chosen guardw. If two distinct edgesw–a andw–b remained, take the negative singleton inputy={w}. A covered-neighborhood clause hitting both positive pairs either containsw, or contains botha,b. In the latter case, C4-freeness forces its neighborhood center tow; that contradicts the fact thatw–a andw–b are uncovered. Thus the same prefix-transfer and mixer-truth APIs force the mixer true ony, and its guardw forces the graph function true on a singleton: impossible. Thereforeu≤1. This contradicts the current residual'su≥4. There is no assumption of unique junk, private preparation, no nesting, or a tree instead of a DAG: shared prefix computation is handled by the checked transfer API.

`formal/Pnp650SingleMixer.lean` now proves this complete generic conclusion by ordinary Lean; the new-module log is empty and the axiom audit uses only the standard three axioms. This is local validation, not an official strict-check verdict.

## 4. Complete mathematical subcase: c=1,o=0 forces u≤1

Letz be the unique centreless top. `LocalCentreTransfer.centreless_transfer` (2024) has the same raw-pin and covered-neighborhood-clause conditions and concludesF(y)=true. It accepts a list of uncovered edge pairs and does not assume exactly two junk gates.

If two uncovered edges are disjoint, bipartiteness and C4-freeness provide a cross pairy that is a nonedge. The two test pairs have no common raw pin. Any monochromatic clause hitting both pairs hits that cross pair, exactly as above. The transfer theorem contradictsF(y)=false.

If two uncovered edges share centerv and have distinct leavesa,b, usey=`single v`. Every common raw pin isv, so its condition holds. A covered-neighborhood clause hitting both test pairs either containsv (and is true ony) or contains botha,b. The second case is impossible: a common neighborc ofa,b must equalv by C4-freeness, but the two edgesv–a andv–b are uncovered, whereas every adjacency in the clause premise is covered. Thus the clause condition holds, and transfer contradicts the negative singleton input.

Every two distinct simple-graph edges are either disjoint or share one vertex; henceu≤1. This again contradicts the residual'su≥4. This second composition has not been assembled in Lean.

The suggested generalizationo=0⇒u≤c is not asserted. The current `centreless_transfer` API uses uniqueness inside its prefix induction to exclude earlier clean ORs, as well as to route edge acceptance. TopForm may permit a new cone-restricted proof, but that extra proof has not been supplied here.

## 5. What these cases leave open

The completed mathematical compositions above imply that a hypothetical≤63 least TopForm counterexample must satisfy at least one of:

    c≥2;  or c=1 ando≥1;  or c=0 ando≥2.

This is a strengthening of the residual structure, not the missing global balance. The current task is full650 (or its negated twin), so these restricted cases are not a full submission and are not a new official reduction request.

## 6. Why the simple last-AND peeling does not solve the many-junk case

The last **dirty** AND is not the last AND: later clean top ANDs remain, so its suffix is not OR-only. The earliest dirty AND has pure-OR operands in TopForm, but it can be shared by many later dirty gates. The existing L8725 `replace_gate_by_wire` (6956) assumes`junk={g}` and uses an exhaustive unique-junk ownership theorem; that assumption cannot be dropped.

A prior already-recorded sanity example shows the issue even for a matching:

    H=(a∨b)(c∨d), J=(a∨c)(b∨d), HJ=ad∨bc.

H andJ are individually dirty and off on singleton inputs; their conjunction is clean. Bypassing either dirty gate by either operand introduces a false positive. The seven-gate circuit is not least (three gates suffice), so it is neither a counterexample to8793 nor evidence that leastness can be ignored. It shows that local bypasses are insufficient and a global cost-preserving replacement must account for shared uses.

The prior evidence is in `continuation-5/L-meta-5126/research5126/check_examples.py` and `examples-results.json`, model`two_empty_wmax_gates_filter_each_other`. It was not rerun here.

## 7. Explicit correction preserved

An early exploratory sketch asserted thatu=4,t=12,c=0 would forceo≥4 because the four uncovered-star edges would require four distinct mixing ORs. **That assertion is withdrawn.** A noncentreless top may fire on an uncovered edge via dirty signals in both operands, even if neither endpoint lies in its raw sides. L1766 explicitly permits this type-II witness. Two mixing ORs at one top can potentially service several such edges; its preparation and sharing costs need a separate proof. None of the conclusions in Sections2–4 uses the withdrawn assertion.
