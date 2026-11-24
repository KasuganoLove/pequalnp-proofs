# L-meta-1922 computational record

The nine-input graph has 12 edges. Its edge function is true when the selected vertices contain an edge. A tenth input supplies the OR of vertices 0 and 4. The posted task asks for a lower bound of 15 further gates in a monotone circuit, given its behavior on 24 inputs.

## Lean proofs

[PetersenRows.lean](../PetersenRows.lean) shows that those 24 inputs determine the monotone function on all 512 rows. [PetersenSecondAnd.lean](../PetersenSecondAnd.lean) rules out 28 states following an AND between the supplied wire and one of the seven other inputs. The latter uses the certificate machinery from [our L-meta-2289 proof](https://github.com/KasuganoLove/pequalnp-proofs/blob/1c6c0284346c35cf6898194bf0dea2fa74fcf7ad/lean/PEqualNP/Outside/L_meta_2289.lean).

[PetersenThirteenSignals.lean](PetersenThirteenSignals.lean) proves that a circuit of at most 14 gates computing the function cannot produce any of 13 specific signals on any wire. Six are the ANDs of the endpoints of the cycle 01, 12, 23, 38, 85, 50. The other seven are the AND of the supplied OR with any raw input outside vertices 0 and 4. The local project checker replayed 3,897 declarations and accepted this theorem against the [exact statement](thirteen-child-printed.txt). It is a self-contained research proof of one child of a prospective reduction. The desk had all three reduction slots filled.

## Finite search

`search.py` uses 512-bit truth tables. At each effective AND or OR it considers whether each operand remains available for later use. For a live state to determine the answer through monotone gates, every minimum positive row and maximum negative row must be distinguished in the correct direction by a live wire. There are 144 such ordered pairs. The search also uses the 126 subcube bounds stored in the upstream L-meta-1667 certificate. It merges identical sets of wire functions. The case in which the extra OR is unused is covered by the raw-input lower bound in the same upstream file.

With the supplied wire in use, the successive numbers of surviving states were 1, 37, 740, 6,338, 12,998, 6,738, 282 and 0. Run from the study directory with Python 3. The argument is the path to a checkout containing the upstream L-meta-1667 file.

```sh
python search.py /path/to/pequalnp-proofs
```

## Restriction to seven vertices

Setting inputs 0 and 4 to false gives a seven-vertex graph with three internally disjoint paths between vertices 2 and 8. Their lengths are 2, 3 and 3. The checked lower bound for this restricted graph is 11. The two fixed input wires and their supplied OR all become constant. An original computation using all three and at most 14 gates must use its eleven remaining effective gates optimally on the restricted graph.

`theta1922.py` performs forward reachability and backward filtering on the seven-vertex graph. It finds 15 possible first-gate functions and 131 distinct wire functions across all optimal monotone computations, counting the seven inputs. Using the resulting states and the 13 marked signals reduces the successive search counts to 1, 21, 191, 655, 474, 125, 5 and 0.

```sh
python theta1922.py --signals --out-dir /path/to/pequalnp-proofs/codex_tmp/theta1922
python search.py /path/to/pequalnp-proofs --marked --theta-states --theta-dir /path/to/pequalnp-proofs/codex_tmp/theta1922
```

The frontier counts and the seven-vertex classification are reproducible computations. The complete 15-gate lower bound still needs a Lean proof connecting and checking the full search.
