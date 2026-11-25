# L-meta-9834: geometry and a bounded four-line construction attempt

## Outcome and scope

No 112-gate witness was found. The one authorized SAT attempt ended **UNKNOWN** at its 300-second wall limit. It produced neither a model nor an UNSAT verdict. No new Lean theorem or strict-check certificate is claimed by this checkpoint.

The public task allows arbitrary counted AND, OR and NOT gates with fan-in at most two. The attempted local construction used at most one NOT. Failure to find that local construction does not exclude a general 112-gate circuit, or even a 15-gate local circuit.

The exact statement has SHA-256 `8a0d68d1957ee455226ea3a9e10cd5bc0af5dae34c0001a9994f49cb0e39b699`. All graph data are parsed from that statement, rather than inferred from the task title.

## Established finite facts

`audit.py` verifies a bipartite graph with 21 left vertices, 19 right vertices and 95 edges. All right degrees are five; the left degree distribution is one vertex of degree three, eight of degree four and twelve of degree five. The graph has no four-cycle and has 816 six-cycles. An explicit 19-edge matching and the 19 right vertices certify vertex-cover number 19.

The graph extends to a cyclic 21-by-21 incidence graph using the difference set `{3,5,15,18,19}` modulo 21. The script checks that every nonzero difference occurs exactly once. The task deletes original right vertices 40 and 41; their point sets are `{0,1,4,14,16}` and `{1,2,5,15,17}`.

The ordinary right-star construction has 113 gates: 19 AND gates and 94 OR gates. Its output is checked symbolically as a monotone DNF antichain and has exactly the 95 edge monomials. This verifies the full Boolean function without enumerating all `2^40` assignments. It does not meet the task's 112-gate bound.

## Four-line construction tested

The selected right vertices are 21, 25, 27 and 37. The latter three meet at point 1; their intersections with line 21 are points 6, 3 and 18. Their private-point bundles are, respectively,

| Line | Private points |
|---|---|
| 21 | 2, 16 |
| 25 | 7, 10, 20 |
| 27 | 8, 9, 12 |
| 37 | 11, 13, 19 |

Preparing these four OR signals costs seven gates. The local twelve inputs are point 1, the four selected line variables, points 6/3/18, and the four bundle signals. The resulting local graph has thirteen edges. `../four-line-gadget/prepare.py` checks its exact expansion to the twenty original edges on the selected lines.

The local star construction uses sixteen gates and is checked on all 4,096 assignments. Replacing it with a fifteen-gate circuit would give a full 112-gate circuit: seven bundle gates, fifteen local gates, 75 gates for the remaining fifteen line-stars and fifteen final OR gates. The same splice with the verified sixteen-gate local control produces a symbolically verified 113-gate global control.

The four-line core has three length-three paths between its two degree-three endpoints. That feature distinguishes it from the three-line gadgets excluded by elementary cycle/tree restrictions.

## Search record

`../four-line-gadget/synthesize15.py` encodes fifteen legal earlier-wire gates on all 4,096 assignments. It includes AND, OR, unary NOT and counted constants (empty AND/OR), and restricts the number of NOT gates to at most one. It uses one-hot operation and operand selectors, commutative operand ordering, syntactic raw-input occurrence and nonoutput-gate-read constraints. Copies can be represented by repeated operands. The output is the last gate.

The generated CNF has 184,965 variables and 3,821,817 clauses, occupying 78,463,920 bytes. Its SHA-256 is `74b54146ba4f768d4df34a2f774f6d737f61a8052aaeed30ef9d4a707839b5c7`.

CaDiCaL ran once from **2026-11-25 14:43:37.671739 UTC** to **14:48:37.708775 UTC**. It used 300.037 seconds wall time and 298.814 seconds CPU; peak resident memory was 789,688 KiB. The wrapper enforced a 2 GiB virtual-memory limit and terminated the solver at the 300-second wall limit. Final status: **UNKNOWN**, exit code -15, with no model and no UNSAT certificate. The exact metadata and solver transcript are retained in `result.json` and `solver.log`.

The source comment describing the one-NOT restriction was corrected after the run to distinguish the search restriction from the public task. No executable statement changed.

## Related mathematical observations

Three nonconcurrent selected lines reduce, after fixing their private points false, to a six-cycle. Three concurrent lines reduce, after retaining one private point on each line, to a subdivided three-star. Existing checked results provide an unrestricted eight-gate lower bound for those six- and seven-variable cores. Charging one deleted gate for each essential variable fixed false blocks the direct one-gate saving in those three-line star blocks. These observations are research arguments, not a new formal proof in this checkpoint, and they do not address arbitrary global circuits.

The existing six-cycle reference can be taken from the public conjunction in `L_meta_927.lean`, verified against the official checked source by the independent status audit. Its SHA-256 is `b3be42c285a9430ec0c4349dc2599bc682b63643793caf38a0f42468eb9772f8`. The more general internal `L_meta_314_aux.cycleTheorem` also applies; that checked source has SHA-256 `dc04788f3141909f778a10adc318e90a4abd6303a964d5878e33b70c0d3de538`. The tree observation uses the existing library route through `PEqualNP/MetaComplexity/L113.lean` and `L204.lean`; it has not been instantiated in Lean here.

## Reproduction and provenance

From the task directory, the finite controls can be regenerated with:

```bash
python3 ownership-geometry/audit.py
python3 four-line-gadget/prepare.py
```

The original bounded search command was:

```bash
python3 four-line-gadget/synthesize15.py --solver /path/to/cadical --seconds 300
```

Running that command performs a new search and overwrites its generated files. It is documented for reproducibility, not a report that a second attempt was run.

The encoder was adapted from this project's earlier `L-meta-10487/constructive/synthesize11.py`, with a new graph, twelve inputs, fifteen gates, all 4,096 assignments and a 2 GiB limit. The geometry parser, exact symbolic control and four-line splice were written for this task. The curated manifest includes the small sources, public statement, exact problem, controls and logs. It excludes the regenerable CNF and selector-heavy `encoding.json`; `encoding-summary.json` retains their size and hash. This checkpoint is research evidence and is not an official submission.
