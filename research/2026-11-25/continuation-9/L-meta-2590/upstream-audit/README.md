# L-meta-2590: fresh upstream and child audit

Read-only audit on 2026-11-25, using the public desk snapshot updated at
07:37:55.363 UTC and public DAG head generated at 07:41:06.473 UTC.
No allocations, lease operations, PRs, comments, or canonical-checkout changes.
The only local writes are this research audit and downloaded public sources.

## Conclusion

No completed child set or ready unconditional Petersen 20-gate lower bound was
found in this bounded audit. All eight immediate children of the three live
2590 reductions remain posted, with no pending PR in the fresh desk record.
2590 itself remains conjectural and has pr_open=0. Its statement is the full
Petersen monotone lower bound: a Monotone2 circuit of size≤19 cannot compute the
15-edge function on all 1,024 inputs. The restriction to Monotone2 is essential;
the sibling2592 handles circuits containing NOT gates.

## Three cuts

| Cut | Merged upstream PR | Immediate children, all still open |
|---|---|---|
| R-meta-2590-1 | https://github.com/open-goat/pequalnp-proofs/pull/4786 | 5685: free first AND; 5687: free first OR |
| R-meta-2590-491 | https://github.com/open-goat/pequalnp-proofs/pull/8191 | 7889: input-zero guard compression; 7891: AND-guard row exclusion; 7893: OR-guard row exclusion |
| R-meta-2590-932 | https://github.com/open-goat/pequalnp-proofs/pull/7763 | 7103: semantic edge-OR first; 7105: nonedge-OR first; 7107: edge-AND first |

Cut1 moves the first gate into an additional free input and reduces to failure
on 15 edge pairs and 15 maximal independent-set assignments. Each suffix has
at most18 gates; arbitrary at-most-two original wire indices are quantified.

Cut491 assumes a hypothetical19-gate circuit can be represented by an AO2
circuit B of16–18 gates after replacing x0 by x0 AND h or x0 OR h, with h read
from B on x0=false and an explicit no-late-read-of-zero condition. The other
two children rule out the resulting 30-row behavior, together with necessary
pivotal guard values. None of the three hypotheses is currently proved.

Cut932 works with fresh semantic signal lists. The three cases successively
exclude nonedge raw ANDs, then raw edge ORs, then all raw ORs. These are genuine
remaining lower-bound obligations, not consequences of simple freshness alone.

All three downloaded/cached reduction sources match the exact content hashes
in the fresh public reduction artifact records. Exact child statements and
hashes are recorded in child-status.json and the eight L-meta-*.json files.

## New checked sources useful to the ongoing work

Sources below were downloaded from pinned upstream commit
351fecac1b6c1fba40b6e45be9bf0058aa141b8a. Every downloaded byte hash matches the
current public checked-file record. The canonical repository was not updated.

| Source | Checked scope | Practical use and limit |
|---|---|---|
| L_meta_2446.lean | Petersen-minus-one-vertex,9 inputs: every first-OR representative (0,1),(0,2),(0,3),(0,4),(0,6),(4,6) requires at least16 gates, even in FanInTwo | Useful for restriction/case proofs; does not by itself force a full Petersen circuit to lose4 gates under a restriction |
| L_meta_1675.lean | The (0,3) first-OR instance of the same≥16 bound | Included for the particular case/provenance;2446 subsumes the final assertion |
| L_meta_2923.lean |9-input Petersen-minus-vertex with free first x0 AND x3 and selected second-AND input pairs: suffix size≥14 | Useful only after matching the exact free-gate and second-input hypotheses |
| L_meta_1880.lean | Girth≥5 graph, least AO circuit in TopForm, at least2 junk gates with pairwise no cone nesting: exists a universal linear residual bound | Not an exact finite Petersen20 bound and not a clean-normalization theorem |

2446 is524,239 bytes, close to the official512KiB limit. Since2590 permits only
PEqualNP.Defs as a project import, embedding this certificate together with
additional helpers may require dependency pruning or a smaller certificate.
A GitHub compare of the old local base57164c… to351fec… reports1,024 new commits,
but its file list is capped at300. Therefore that list was not treated as an
exhaustive proof inventory. Current public child/checked records and relevant
individual source hashes were checked independently.

## A misleading closed PR

https://github.com/open-goat/pequalnp-proofs/pull/12169 is titled L-meta-2590 but
adds R_meta_2590_933, not a complete proof. Its official comment says the checker
accepted the reduction but did not record it because its author already had
five open reductions:
https://github.com/open-goat/pequalnp-proofs/pull/12169#issuecomment-7153648084

The source splits ORcount≤103 from ORcount≥104 while the total circuit size is
already≤19. Thus the latter branch is impossible and the former retains the
whole original lower-bound problem. It adds no useful premise for this task.

## Literature sanity check

Jukna's primary paper “Disproving the Single Level Conjecture”:
https://eccc.weizmann.ac.il/report/2005/021/revision/1/download/

It disproves constant-factor single-level simulation for general quadratic
monotone functions. Its regular/constant-degree result concerns asymptotic
unbounded-fanin complexity, not an exact bounded-fanin Petersen20 theorem.
This does not refute a special C4-free or Petersen cleanup lemma; it does mean
quadratic output alone is not a justification for flattening arbitrary ANDs.
The local clean-case route must keep its explicit cleanliness premise until a
separate preservation/existence theorem is proved.

## Curated checkpoint

The curated/ directory contains this README, selected-desk.json,
child-status.json, the three reductions, four checked reusable source files,
and eight exact child records. It excludes the full public desk, raw website
JavaScript, the capped comparison response and unrelated downloaded source.
No compiled binaries or private lease data are included.
