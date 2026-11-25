# Symmetric spaces on the permanent level through the all-ones matrix

Let $J$ be the all-ones matrix. The GCT 232 probe asks whether a three-dimensional complex linear space $L$ of symmetric $4\times4$ matrices can satisfy $\operatorname{per}(J+A)=24$ for every $A\in L$. The files here prove restrictions on such a space. The general dimension question remains open in this work.

| Result | Lean source |
|---|---|
| In every dimension, the polynomial $\operatorname{per}(J+z uu^{\mathsf T})$ has degree equal to the number $k$ of nonzero coordinates of $u$. Its leading coefficient is $(n-k)!\,k!(\prod_{u_i\ne0}u_i)^2$. Consequently a symmetric constant-level space has no nonzero matrix of ordinary rank one. | [RankOne.lean](RankOne.lean) |
| In dimension four, if there is a fixed nonzero $u$ such that each $A\in L$ is $uv^{\mathsf T}+vu^{\mathsf T}$ for some $v$, then $\dim L\le2$. The proof uses the first two coefficients of the translated permanent and a bilinear form over the complex numbers. | [CommonFactor.lean](CommonFactor.lean), [Coefficients.lean](Coefficients.lean), [Nondegenerate.lean](Nondegenerate.lean) |
| The plane supported on one row and matching column with three off-diagonal entries $p,q,-p-q$ is maximal under inclusion. For any level space of dimension at least three, deleting any row and its matching column leaves an image of dimension at least two. | [StarMaximal.lean](StarMaximal.lean) |
| Any level direction with four equal diagonal entries has zero diagonal, zero off-diagonal sum and zero hafnian. If every direction of $L$ has equal diagonal entries, then $\dim L\le2$. | [WitnessEqualDiagonal.lean](WitnessEqualDiagonal.lean), [WitnessZeroDiagonal.lean](WitnessZeroDiagonal.lean) |

The rank-one proof uses this repository's permanent expansion and rank-one minor identities. The four-dimensional coordinate proofs use the checked 24-term expansion of the permanent. [Minc expansion](../../lean/PEqualNP/Gct/Helpers/MincExpansion.lean) · [Rank-one minors](../../lean/PEqualNP/Gct/Helpers/RankOne.lean) · [Four-dimensional expansion](../../lean/PEqualNP/Outside/L_gct_220.lean)

## Rebuild

The sources were checked against upstream commit `2e36ec909a11a78d5c3b1ba2506a57ed79fc3021` using Lean 4.36.0 and Mathlib commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. With the repository toolchain and dependency cache installed, run from the repository root.

```bash
repo=$(pwd)
cd lean
lake build +Mathlib +PEqualNP.Gct.Helpers.MincExpansion +PEqualNP.Gct.Helpers.RankOne +PEqualNP.Outside.L_gct_220
out="$repo/lean/.lake/build/research-gct232"
mkdir -p "$out"
lake env bash -c '
  set -eu
  src=$1
  out=$2
  export LEAN_PATH="$out:$LEAN_PATH"
  for mod in Coefficients Nondegenerate RankOne CommonFactor StarMaximal WitnessEqualDiagonal WitnessZeroDiagonal
  do
    lean -j 1 -R "$src" -o "$out/$mod.olean" "$src/$mod.lean"
  done
' _ "$repo/research/gct232" "$out"
```

Each of the seven compiled modules passed local native kernel replay. A separate empty-environment replay covered all 39 public theorem roots and their proof dependencies. The per-theorem axiom audit contained only `propext`, `Classical.choice` and `Quot.sound`.
