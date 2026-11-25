# Exact finite cover-augmentation calculation for L-meta-2384

`cover_augmentation.py` exhausts all 65,536 edge-deletion sets U of the exact
eleven-vertex, sixteen-edge graph in the posted statement. It computes

`a(U) = min over minimum covers K of G-U of min |A| such that K union A covers G`.

The public conclusion's finite part is equivalent to `r >= |U| + a(U)`.
The script first computes maximum independent sets for every induced vertex
set. For each potential K it finds the exact extension cost, then performs a
subset-min convolution over uncovered original edges, prioritizing minimum
|K| before extension cost. Every returned cover and addition is checked
directly against the original edge list. This is ordinary Python evidence,
not a Lean certificate and not a circuit lower bound.

Results:

- The original graph has cover number 7.
- In 65,519 deletion sets, `a(U) = 7 - tau(G-U)`.
- In exactly 17 deletion sets, `a(U) = 8 - tau(G-U)`.
- Those 17 masks exactly match the already-published R_meta_2384_1 list; this
  independently verifies existing finite classification and is not claimed
  as a new classification. The remote source audit also found its ordinary
  case covered by checked L_meta_4129.

The graph-only implication from `|U| <= r < 2|U|` is false. For example, take
`U={(0,9),(0,10)}` and r=2. The residual graph has minimum cover size6, but at
least one additional vertex is necessary to cover G, while r-|U|=0. This does
not refute the public theorem: it does not supply a least top-form circuit
realizing that U and r.

The first exceptional mask36608 deletes edges48,4-10,58,59,89. Its residual
cover number is5, but the best extension requires3 vertices, rather than the
cover-number drop2. Thus a circuit argument establishing only
`r >= |U|+7-tau(G-U)` would leave these17 cases unresolved.

Run `python3 cover_augmentation.py` to reproduce the profiles and witnesses.
The complete65,536 witness rows are deterministically constructed; their
compact JSON hash is recorded in results.json without storing the redundant
full table. No circuit assumptions, leases, solver jobs, or Lean jobs are
part of this calculation.
