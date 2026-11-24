# L-meta-1673 research record

The target is a 16-gate lower bound for the edge function of the Petersen graph with one vertex removed, on nine input bits. The first gate computes `x₀ ∨ x₁`. The remaining gates may be AND, OR, or NOT with at most two inputs. The work below gives kernel proofs for two lower bounds and one search branch. For the complete target it gives a finite computation, with independent evaluation of every candidate state by Lean code. A single-file kernel proof of the complete target remains open.

## Kernel-checked results

- `KernelBounds.lean` imports `PEqualNP.Defs`. Its `fifteen` theorem proves the 15-gate lower bound with any first gate. For the prescribed OR first gate, `seededOnly` shows that a circuit of size at most 15 would yield a computation of at most 14 further gates in which all nine raw inputs and the OR wire are live.
- The same file proves `eliminatedSoft`. If the function of any gate is `xᵢ ∧ xⱼ`, for distinct indices and with at least one endpoint among vertices 4, 6, and 7, the circuit has at least 16 gates. This covers 21 unordered pairs. The gate can compute that function indirectly. The proof supplies that function as an extra input, skips the gate that produced it, and applies the 13-gate lower bound for the graph with the relevant degree-two vertex removed.
- `KernelBranch.lean` imports the upstream module `PEqualNP.Outside.L_meta_1667` for the verified finite search framework. Its `concretePrefix` theorem rules out a live computation with at most 13 further gates when the initial live set contains all nine raw inputs, `s = x₀ ∨ x₁`, and `s ∧ x₂`. Its five certificate levels contain 1, 19, 158, 309, and 147 states, totaling 634. The assumption that all eleven wires are live matters.

## Full finite search

`enumerate_states.py` reads the nine truth tables, target, 768 pairs of sample assignments, and 126 established restriction bounds from the upstream `L_meta_1667.lean`. It starts from the nine input signals and their OR seed. At each step it enumerates NOT or the two binary operations, and the possibilities for which operands remain live. It checks sample separation and restriction bounds, merges states with identical live signal sets, and records the surviving obligations. It writes eight plain-text tables.

`CheckForest1673.lean` reads those tables from the bottom level up. It reconstructs each gate from its recorded operands using `decodeBank`, rebuilds the actual restriction rules using `buildRule`, and invokes the public `testAll` checker on the state. The lookup retains every candidate with a given hash. The checker compares the full signal sets. All 145,643 states passed this execution. The data tables and the `--run` execution do not by themselves yield a closed Lean theorem.

| Remaining gates | States | Distinct children |
| ---: | ---: | ---: |
| 14 | 1 | 80 |
| 13 | 80 | 2,664 |
| 12 | 2,664 | 32,704 |
| 11 | 32,704 | 73,709 |
| 10 | 73,709 | 34,621 |
| 9 | 34,621 | 1,862 |
| 8 | 1,862 | 2 |
| 7 | 2 | 0 |

## Reproduce

Use Python 3.10 or later and the project's pinned Lean 4.36.0 toolchain. The Mathlib revision is `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. The base checkout used for this run was `4a630795464767fd126af2108f5b9bc483fa56ee`. The Git blob of the upstream module `lean/PEqualNP/Outside/L_meta_1667.lean` is `fc4ba1121de31fdfa08b135ece199d4d4a9852e8`.

From this directory, set `repo` to the root of the proof repository. The following shell commands keep generated tables under that repository's `codex_tmp` directory.

```bash
study="$(pwd)"
repo="/absolute/path/to/pequalnp-proofs"
tables="$repo/codex_tmp/l-meta-1673-tables"
python "$study/enumerate_states.py" "$repo" "$tables"
cd "$repo/lean"
lake exe cache get Mathlib
lake build +PEqualNP.Defs +PEqualNP.Outside.L_meta_1667
lake env lean "$study/KernelBounds.lean"
lake env lean "$study/KernelBranch.lean"
lake env lean --run "$study/CheckForest1673.lean" "$tables" 7 14
```

The enumerator ends with two cap-7 states and zero children. The Lean checker ends with `finished cap 14, all 1 verified`. These commands regenerate the tables locally. Their combined size in this run was 4,947,103 bytes.
