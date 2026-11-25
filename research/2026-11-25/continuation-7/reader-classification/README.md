# L-meta-1884 / 2598: precise scope of the unique-reader lemma

## Conclusion

The new checked research theorem `Pnp1884UniqueRead.primitive_join_forces_another_reader` excludes a uniquely read nonzero variable from a binary AND/OR gate whose other input is another primitive input. It does **not** close the remaining 18-gate lower bound. The checked upstream bound `L_meta_5367` counts a different object: active gates reading either x0 or its free negation. Under the 18-gate cap it leaves at most three such gates, and it does not itself imply that any nonzero variable is uniquely read.

This directory provides a bounded finite classification of a possible computed partner depending on at most two original variables, and two explicit larger circuits showing why the surviving forms cannot be rejected by the reader cap alone. No new Lean compilation, SAT search, or circuit synthesis was performed for this classification.

## Distinguish the two counts

| Quantity | Definition and consequence |
|---|---|
| Syntactic readers of nonzero v | Gates whose input lists contain v. The original unique-reader theorem uses this count. A NOT gate's ignored second input still counts syntactically. |
| Active readers of v | AND/OR use their actual input lists; NOT uses only the first input. A separate checked bridge is needed to replace syntactic-reader hypotheses by active-reader hypotheses. |
| Special active-reader count r | Gates with at least one active input in `{0,10}`. These are x0 and free `NOT x0`. A gate reading both counts once, not twice. |

For a correct canonical circuit, L5367 gives `15+r ≤ size`. Thus a hypothetical size≤18 circuit has r≤3. Zero readers cannot compute a function that depends on x0 (the existing R2598_314 proof handles this). Consequently the remaining cases are r=1,2,3. None of these cases supplies a unique reader of a nonzero variable without further reasoning.

If one of these r special gates joins x0 or `NOT x0` with a primitive nonzero variable v, the new primitive-join theorem forces a second reader of v. That second reader need not be another special reader: it can be one of the other gates. Therefore the implication cannot be converted into r≥4 by simple counting.

## Necessary condition at a unique nonzero reader

Assume v is nonzero, its influence enters through a single binary gate, and the gate is

`x_v AND h(y)` or `x_v OR h(y)`,

where the earlier partner h depends only on original variables other than v. For the usual unique-reader hypothesis, earlier computations are independent of v. The final output is not the raw wire v, as established in the checked research file.

Call y *v-pivotal* when the target is false at x_v=0 and true at x_v=1. If h(y)=false for an AND, both gate outputs are false; if h(y)=true for an OR, both gate outputs are true. In either situation the sole gate carrying v cannot distinguish the two target values. Hence on every v-pivotal assignment:

* an AND gate's partner must equal true;
* an OR gate's partner must equal false.

This collision argument does not assume monotonicity of the rest of the circuit. It also does not establish a size bound.

## Exhaustive projection table

The script checks v=1,…,9. Each v has exactly 40 pivotal assignments. For each of the nine other original variables, both Boolean values occur among these assignments. For each unordered pair j,k distinct from v:

* if `{j,k}` is a Petersen edge, the projection is exactly `00,10,01`;
* if `{j,k}` is not an edge, the projection is all four assignments.

The finite two-pin pivotal premise is already present in upstream task **L-meta-6081**, from the first hypothesis of [R_meta_1884_412](https://github.com/open-goat/pequalnp-proofs/blob/57164c3618362178843e2ea37bd01613f4037ae2/lean/PEqualNP/Outside/R_meta_1884_412.lean). This is an independent finite verification of that existing premise, not a claim to have discovered a new missing child or submitted its proof. The useful derived result here is the classification of **arbitrary Boolean partner functions**, not merely the three allowed gate operators.

| Partner support | Gate combining x_v with h | All possible h under the pivotal condition |
|---|---|---|
| At most one other raw variable | AND | Constant true |
| At most one other raw variable | OR | Constant false |
| Nonedge pair `{j,k}` | AND | Constant true |
| Nonedge pair `{j,k}` | OR | Constant false |
| Edge pair `{j,k}` | AND | Constant true or `NOT(x_j AND x_k)` |
| Edge pair `{j,k}` | OR | Constant false or `x_j AND x_k` |

Constants in the table make the joining gate a copy of x_v. The local collision theorem alone does not forbid copy gates in an arbitrary correct circuit. Excluding them in a least circuit requires a size-preserving semantic bypass and a strict gate-count decrease, not a new truth-table assertion.

The table exhausts 81 one-variable projections and 324 two-variable projections: 108 edge pairs and 216 nonedge pairs. All 16 two-variable Boolean functions are tested for each AND/OR condition, giving 10,368 checks. Bit index `b0+2*b1` stores h(b0,b1): masks 0,7,8,15 denote false, NAND, AND, true respectively. A concrete pivotal assignment is saved for every reachable projected value.

**The free wire `NOT x0` is not independent of x0.** Support is measured in original variables x0,…,x9. A partner involving the free wire is a Boolean function of original x0 and any other original variables it uses. The finite table handles x0 this way. Also, the unique-variable collision argument here is applied only to v≠0, because flipping x0 simultaneously changes two initial wires.

## Concrete remaining gate cases

For a nonzero variable with one active entry point, the current results leave these cases:

1. A NOT of v. The primitive binary-join exclusion does not apply.
2. A unary AND/OR or repeated-input gate, which acts as a copy; a minimum-circuit argument must remove it physically.
3. A binary AND/OR with a computed earlier partner. If that partner has support at most two, the table above leaves the two nonconstant edge forms, plus copies. A partner with three or more original variables is outside this finite classification.
4. Missing/future operand wires evaluate to false. An AND with such an operand cannot carry the unique dependence on v; an OR with it is a copy. This is a semantic classification, not an unproved normalization of every candidate.

The new primitive-join theorem removes the distinct primitive-partner cases. It does not by itself eliminate computed partners, prove their supports are small, or show a uniquely read nonzero variable exists in an 18-gate candidate.

## Two larger circuits realizing the surviving edge forms

Take v=1, E=x2 AND x3, N=x0 OR x2 OR x6, and F0 equal to the Petersen edge function with all edges incident to vertex1 removed. Since E is an edge of F0, `E ≤ F0`. The full target is `F0 OR (x1 AND N)`.

Both identities below compute that target:

* `F0 OR ((x1 AND NOT E) AND N)`;
* `F0 OR ((x1 OR E) AND (N OR E))`.

Implement F0 by its 12 edge ANDs and 11 ORs, reuse its E wire, and implement N by two ORs. Each construction has 29 gates. In the first, x1 has a unique AND reader with the two-variable NAND partner. In the second, x1 has a unique OR reader with the two-variable AND partner.

The independent scalar checker validates all 1,024 assignments for each construction. Both have exactly three active gates reading wire0 or10: two edge gates in F0 and the first OR constructing N. They do not use the free negated input. This shows the reader cap and the local partner conditions are compatible with a correct larger circuit. **Neither construction satisfies the 18-gate budget**, so neither refutes L-meta-1884 or2598.

The missing step remains a quantitative argument ruling out these computed-partner/shared-subcircuit patterns at size≤18, or a different structural theorem covering them.

## Reproduce and validation limits

```sh
python3 check_projection.py
```

Outputs:

* `projection-table.json`: all projections, witness masks, and permitted arbitrary partner truth tables.
* `residual-examples.json`: both exact29-gate circuit lists.
* `summary.json`: counts and independent1024-row checks.

These are finite Python checks. They have not been packaged as official Lean submission files or passed through the strict project checker. No new global size claim is made.
