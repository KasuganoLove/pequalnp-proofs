# Read-only review of the 10487 signed probe

**Finding:** no mathematically unsound pruning was found. The result is useful computational evidence for a binary-gate lower bound of11 with arbitrary free NOTs. It is not yet a Lean theorem or checked certificate. The C++ optimizations are not automatically covered by importing L9539's unchanged completeness theorem.

No solver or Lean job was rerun for this review. A small independent128-row calculation checked the exact graph and reported masks. `independent-data-audit.json` fixes the reviewed source SHA and records114 positive assignments,14 negative assignments,1596 opposite-label pairs, and witnesses that all seven inputs are essential.

## Relation to the existing proved framework

In `L_meta_9539.reference.lean`, `build` is defined at15–19, `live` at21–25, and `compress` is proved at28–59. Compression keeps only needed signals and requires each paid result to be fresh. `live_card` at62–74 gives `|s|≤remaining+1`; `first_live` at93–105 removes budget-only skips. The compiler at476–515 counts non-NOT gates and allows constants or either polarity of an available signal at zero cost through `holds` at341–342. `gate_reach` handles empty/unary gates and default-false reads.

The completeness route therefore uses a compressed live frontier; it does not assume every intermediate wire of an arbitrary circuit is semantically essential. Retaining an operand in the search corresponds to a later use of that wire. Early success when the goal occurs in a larger frontier is permissive and cannot cause false rejection.

## Pruning and representation audit

1. **Complement classes.** `canonical(x)=min(x,~x)` identifies exactly a truth table and its free complement. For signed operands with AND/OR, the four result classes represented by `a&b`, `a|b`, `a&~b`, `b&~a` are exhaustive by De Morgan. Input swapping preserves this four-class set. Canonicalizing the result changes only polarity.

2. **Sorted sets.** Creation order and wire names do not affect continuations on a truth-table frontier. The vector stays duplicate-free: raw classes are distinct, and generated classes already present are rejected. Sorting is consequently a set/permutation quotient, not an extra circuit restriction.

3. **Existing-result skip.** A gate producing a class already available adds no function; later consumers can use that representative with free polarity. In the abstract build relation the step becomes a budget skip, after which compression supplies the appropriate earlier retention choices. This is a global compressed-build argument, not permission to erase arbitrary current list entries at zero cost.

4. **Constant skip.** Canonical zero represents both constants, which are already allowed by `holds` without a frontier entry. A gate using a constant simplifies to a constant or signed copy. A class-based compiler can therefore classify a constant result as existing rather than insert it. L9539's current reachability proof can retain redundant constant insertions, so an optimized Lean checker would still need this normalization bridge. A literal unoptimized Lean rejection avoids that extra obligation.

5. **Budget accounting.** With m live classes and b binary gates remaining, m≤b+1 is the proved live-cardinality bound. Combining two classes while retaining k of those operands gives m−1+k classes and b−1 gates remaining. Feasibility is exactly k≤b+1−m, the C++ `popcount(keep)≤extra` test. All four keep sets satisfying this bound are tried. The child's extra becomes the parent's extra minus k, matching L9539 `dispatch`. A one-signal state cannot generate a new nonconstant class by binary operations and free complements.

6. **Separation.** For each negative row n, `matching` intersects the positive rows with the equal-bit class of each frontier signal. A surviving positive row has the same complete signal vector as n, so no continuation can distinguish them. This is exactly the1596-pair form of `cuts ws == -1`, and is invariant under complementing signals.

7. **All initial inputs.** L9539 searches initial sublists; C++ begins with all seven raw classes. The program verifies every raw input essential. Omitting one input leaves a differing-label assignment pair with all other raw bits equal. Thus no proper initial sublist can pass separation. This simplification is task-specific and requires the essentiality facts.

8. **Memoization.** The key includes both the remaining budget and every128-bit class in the sorted vector. Hash collisions are resolved by exact equality. Only fully failed states are inserted; timeout propagates before inserting ancestors. Reaching the cache-capacity limit merely stops new insertions and repeats work. Depth decreases at each transition, so there is no in-progress cyclic-state dependency.

## Data and implementation details

All shifts are0–127 on unsigned128-bit values; `~` complements exactly the full assignment domain. Global masks are zero-initialized for the one process invocation. The16-slot depth counter is in range for budget10. The reported run completed in about2.54 seconds, without timeout, so `EXHAUSTED_NO_MODEL` differs from the earlier SAT UNKNOWN.

The positive mask is `fffffffefffffffefffefffefffeeca0`; its canonical complement is `0000000100000001000100010001135f`. A literal L9539 paired encoding has1596 pairs and3192 bits. Its existing sample equation is `F = ~~~goal`: positive samples belong in the low1596 bits and negative samples in the high half, unless the equation is adjusted consistently.

## Remaining formal step

A literal adaptation of `search_complete` and a kernel-checked rejection would establish the lower bound independently of C++. Alternatively, a faster canonical/memoized Lean engine needs the additional bridges above. The C++ state count is not a runtime bound for the unoptimized Lean engine.

If `10 < binaryCost gates` is formally established for the exact target, any circuit containing a NOT has total size at least12 and can be replaced by the already verified12-gate monotone circuit. A circuit with no NOT is returned unchanged. This proves positive twin10486 and does not need the at-most-one-NOT premise. At this review stage that lower bound is not formalized, so neither twin is declared solved.

Attribution: L9539, Apache-2.0, credits L9136, L9146 by partymejker, L8633 by k-sandhu, and the earlier L8463/L1449 signed-search framework. This review does not claim those generic proofs as new work.
