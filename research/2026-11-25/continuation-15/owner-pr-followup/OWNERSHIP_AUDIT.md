# Immutable ordinary audit of official PR14022

**Result: the exact PR source passes the pinned ordinary Lean build, the
project source/import guard, and an exact posted-statement type check.**
No source defect was found. This audit did not run the strict checker and
does not assert an official ACCEPTED verdict.

## Identity

* Official PR:14022; head `bc59c2be036e28415543dcb42dd8da78d4439163`.
* Source: `L_meta_10221.lean`,109,453 UTF-8 bytes.
* Git blob: `1f0d7cf983743bb6e5f588a28908f2d0682d4389`.
* SHA256: `9f4dcb5a1635683d7bc7ff3e4d05f307ba8b7aa8f1ff538901f726b32239f3bc`.

The initially saved transport copy contained one additional terminal
newline. Removing exactly that byte restored the expected remote Git blob.
The source and local audit copy were then built again at those exact bytes.
No proof code was modified. The earlier transport-copy build also passed;
its separate log is not the authoritative immutable build record.

## Verification

The local checkout was `57164c3618362178843e2ea37bd01613f4037ae2`.
A single-thread ordinary build of the byte-identical
`Pnp10221OwnerAudit.lean` returned exit0. Its only messages were inherited
tactic-style and `push_neg` deprecation warnings. The existing project
source guard returned exit0 with all three imports allowed by the current
gap: Mathlib.Tactic, PEqualNP.Defs, and PEqualNP.Defs.Represents.

`Pnp10221OwnerTypeCheck.lean` imports that built audit module and supplies
the source theorem as a proof of the **exact public statement** extracted
from the saved current gap row. It passed, exit0. The accompanying ordinary
axiom audit returned only:

    propext, Classical.choice, Quot.sound

The target is precisely that no AND/OR circuit of at most10 gates represents
the5x5 mask15768118 on the25 oneEach inputs. No stronger full-input Boolean
function claim is being made.

## Independent finite-data and reuse check

`ownership-audit.py` independently decoded all25 bits of15768118. OO is
exactly the12 positive positions; ZZ is exactly the13 negative positions.
They are disjoint, contain no duplicates, and exhaust0 through24. All10
raw-input bit signatures match their literal oneEach values. The script
also supplies witnesses for all ten input-necessity premises.

The reference is tb-16's checked L-meta-9195, PR13373, merge
`9025f81315571fe9b237f2fd3aed4f123b1e8757`, source SHA256
`b358ad57b53243df24c1908382c59f29819715761f8eacec38d032b0826aea20`.
After normalizing the namespace, target mask, OO/ZZ lists, the additional
allowed import, and the added attribution comments, the entire remaining
source is identical. There is **no change to the generic lower-bound or
finite-checker argument**. The specialization is mask7387710→15768118 and
the two complete sample lists. Attribution to tb-16/L9195 is present in the
submitted header; the repository license is Apache-2.0.

## Evidence

The machine-readable summary is `ownership-check-result.json`. The
authoritative ordinary-build log is `ordinary-lean.log`; source-guard
output is `format-guard.log`; exact-type and axiom output is
`exact-type-axioms.log`. Independent data results are in
`independent-audit.json`, with the normalized source comparison in
`generic-source.diff`.

No remote file, PR, comment, lease, or task allocation was modified during
this audit. The official verdict remains a separate check by the project.
