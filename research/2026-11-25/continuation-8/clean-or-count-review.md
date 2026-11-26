# Read-only scope review: clean OR count

Reviewed source SHA256: `171665a973dec6ebe230ad3daca21d98a8065ef73f412f87028b32c7f1a202fd`.

No hypothesis or conclusion scope defect was found in the reviewed endpoint
and the supporting edge-witness/count chain. This review does not replace the
separate Lean compilation and final official dependency/axiom checks.

- `clean_top_or_bound` assumes full equality with `graphFun G ∅`, exact binary
  backward-reading AND/OR gates, NoFourCycle, TopForm, and all ANDs BelowF.
  It assumes neither total-gate minimality nor OR-count minimality.
- The full function equality supplies rejection of every singleton and nonedge
  pair, and acceptance of every graph edge pair. These tests are derived
  consequences, not a substitution of finite-sample correctness for the input
  equality premise.
- The firing trace follows a true wire backwards through OR gates to a raw
  input or a true AND. A raw input in the output OR support contradicts the
  corresponding singleton-negative test.
- At a witnessed AND, TopForm together with the explicit all-AND cleanliness
  premise excludes another AND in either operand's OR closure. Thus both
  operands have raw-variable witnesses. Their supports are disjoint by the
  imported singleton/nonedge structural lemma, so an edge-pair input supplies
  the two distinct endpoints on opposite sides.
- The counting core uses two disjoint sets of actual OR indices. Its conclusion
  is the number of ordered graph edges at most the OR count plus one. No AND
  count is charged or silently bounded.
- `or_indices_eq_countP` converts the finite set cardinality to precisely the
  public GateOp.casesOn OR predicate, not total gate count.
- No theorem here asserts that arbitrary dirty circuits have clean equivalents.
  The separate normalization/minimization modules must preserve an explicit
  initial all-AND-clean premise, as the exact8323 composition plans to do.

The source attributes the core counting construction to upstream L_meta_2235
and its component lemmas, and the wire/cone semantics to L_meta_1501.
