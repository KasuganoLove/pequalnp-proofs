# L-gct-232: partial rigidity of a symmetric star space

## Scope and status

The assigned theorem excludes every three-dimensional complex linear space of symmetric 4-by-4 matrices T for which permanent(J+T) is identically 24. Here J is the all-ones matrix. Symmetric means transpose-symmetric, not conjugate-symmetric.

The full assigned theorem remains unproved. The following argument only rules out extending one particular two-dimensional space. No classification showing that an arbitrary three-dimensional candidate contains this space has been established.

The cited scout paths `barriers/l037/STATE.md` and `plan/README.md` were absent from the public source checkout at commit `048b39bb2c5b2c21da06d44218d16366086a68d9`.

## The known two-dimensional family

Let A have entries A01=A10=1 and A03=A30=-1, with all others zero. Let B have entries B02=B20=1 and B03=B30=-1, with all others zero. Every xA+yB is symmetric and permanent(J+xA+yB)=24. This is also a specialization of upstream `L_gct_222.lean`.

Write a possible third symmetric direction as

\[
C=\begin{pmatrix}a&b&c&d\\b&e&f&g\\c&f&h&i\\d&g&i&j\end{pmatrix}.
\]

Assume permanent(J+xA+yB+zC)=24 for all complex x,y,z. The coefficient linear in z is the quadratic polynomial

\[
\begin{aligned}
D(x,y)={}&6(a+2b+2c+2d+e+2f+2g+h+2i+j)\\
&-4(e+f-i-j)x-4(f-g+h-j)y\\
&+(e-2g+j)x^2+2(f-g-i+j)xy+(h-2i+j)y^2.
\end{aligned}
\]

All six coefficients must vanish. Their exact linear solution is

\[
e=f=g=h=i=j=r,\qquad a=-2(b+c+d)-9r.
\]

Let s=b+c+d. After this substitution, the remaining coefficients of z²,z³,z⁴ are

\[
Q=2(s^2-6sr-63r^2),\quad K=4r(s^2-6sr-39r^2),\quad H=2r^2(s-9r)(s+3r).
\]

The polynomial identity K−2rQ=96r³ gives r=0, because Q=K=0 and the field is the complex numbers. Then Q=2s²=0 gives s=0, and a=0. Consequently C=bA+cB. There is no independent third direction extending this specific family.

## Reproduction and validation

`gct232_symbolic.py` expands all 24 permanent terms over exact rational polynomial coefficients, checks the six linear constraints and their solution, verifies Q,K,H, and verifies K−2rQ=96r³. It exited 0. It needs Python and SymPy; no floating-point arithmetic is used by that script.

`Gct232StarScratch.lean` is the associated locally checked Lean proof of this partial result. The final command `LEAN_NUM_THREADS=1 lake env lean -j1 ../research/2026-11-24/continuation-2/L-gct-232/Gct232StarScratch.lean`, run from the project `lean/` directory with its pinned toolchain, exited 0 with no warnings or output on 2026-11-24. The main checked lemma is `Gct232StarScratch.star_extension_rigidity`. This is ordinary Lean compilation, not an official task-checker acceptance. The separate non-star block example is checked by the exact SymPy script, not by this Lean file.

Preliminary invocations were interrupted while diagnosing execution stalls. Single-thread execution resolved the observed stalls; wrapping the concrete nested vectors in `Matrix.of` resolved the Lean 4.36 rewrite-transparency issue. The final source uses only focused Mathlib submodules.

## What is still missing

We have not proved that an arbitrary three-dimensional candidate contains the displayed star space. Proving such containment, establishing a different valid normal form, or excluding all other candidates would be a substantive new global argument. The partial rigidity result does not justify the assigned theorem by itself.

Even two-dimensional level spaces are not all stars. Put the symmetric 2-by-2 block with entries `(sqrt(2)-1, 1; 1, -sqrt(2)-1)` in positions 0,1 to form U, and in positions 2,3 to form V, with all remaining entries zero. Each block has zero sum of entries and zero permanent. Exact expansion gives permanent(J+xU+yV)=24. This family has nonzero diagonal entries, whereas the displayed star spaces have zero diagonal. This is not a three-dimensional counterexample, but it rules out a blanket claim that every level space is of star form. The symbolic script checks this example too.

The Lean permanent-expansion helper was adapted from upstream `lean/PEqualNP/Outside/L_gct_222.lean`, under the repository's Apache 2.0 license. Its project imports cannot be used directly in an official file unless allowed by the task; the proof file copies the helper and uses only the necessary Mathlib submodules.

Run the exact symbolic calculation from this archived task directory with `python3 gct232_symbolic.py` (SymPy 1.14.0 was used).
