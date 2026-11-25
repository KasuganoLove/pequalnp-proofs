# Independent read-only Rank14 encoder review

Reviewed on 2026-11-25. Source: `../ownership-analysis/rank-sat/encode.py`, SHA256 `06c232f46a38fd9f011da04e028f7ad194e1bb6ce4c619ff280c13e0ae1b498e`.

This is a source-level semantic review, with no solver rerun and no Lean certificate.

* Exactly-one deletion-round clauses assign each row and column either one round 1–14 or survival (round 0). The prefix variables are equivalent to deletion in a positive round at most their index.
* Two rows selected in the same round must agree on every column not deleted strictly earlier. The column-side clauses are symmetric. This matches `Twins A R X C Y` on the sets before the current simultaneous deletion. In particular, selecting an opposite-side label in the same round does not improperly excuse a discrepancy.
* The round-1 shortcut excludes a row/column pair precisely when it has at least one differing opposite-side label; no opposite-side label could yet have been deleted.
* A terminal `Bic` violation is exactly two retained rows with a common true column and another retained column where their values differ. The four positive deletion-prefix literals forbid all four labels surviving. Unordered row pairs cover both orientations of the three-true/one-false rectangle.
* Empty deletion sets, empty residual sides, and labels surviving all rounds are allowed, as in the recursive predicate. No extra symmetry restriction appears in the source.

No encoding mismatch was found by this review. This does not change the job's result: the single bounded run ended UNKNOWN with no deletion schedule, no UNSAT certificate, and no proof of the circuit lower bound. The finite Rank obstruction is a sufficient lower-bound route from PR13556's generic theorem; failure to find a Rank schedule is not itself a checked obstruction.

Generic Rank/Bic source: https://github.com/open-goat/pequalnp-proofs/blob/2729f5c656ee99b60af92b92f1c6a45d549b431a/lean/PEqualNP/Outside/L_meta_9484.lean
