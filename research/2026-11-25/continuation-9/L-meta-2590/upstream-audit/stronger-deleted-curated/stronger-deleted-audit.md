# L2446 internally proves the unconditional deleted-Petersen bound

Read-only audit, 2026-11-25. No Lean source was changed or compiled, and no lease,
submission, or other remote mutation was performed. This audit finishes work
already in progress when the parent reported its L2590 heartbeat returned 410.

## Verified conclusion

The following closed term already occurs in an officially checked source file:

```lean
PEqualNP.Outside.L_meta_2446.directSplit
  PEqualNP.Outside.L_meta_2446.monoRoot
  PEqualNP.Outside.L_meta_2446.signedRoot
```

Its type is:

```lean
¬ PEqualNP.MetaComplexity.HasCircuitSize 9
    PEqualNP.Outside.L_meta_2446.edge 15
```

`directSplit` has exactly the two root-impossibility hypotheses. `monoRoot`
and `signedRoot` are closed theorems discharging them. The public theorem at the
end of L2446 introduces `p hp C legal wire computes`, then invokes the term above.
Its proof does not use `p`, `hp`, or `wire`. Thus the internal result is stronger
than L2446's public first-OR statement: every allowed circuit for this nine-input
function has at least 16 gates, independently of its first gate.

This was established by reading the checked declaration bodies and their types;
no new independent kernel run was performed during this audit.

## Precise model

`HasCircuitSize n f s` means an existential circuit with `FanInTwo C`, `C.size ≤ s`,
and equality with `f` on **every** input of type `Fin n → Bool`. The basis is
AND, OR, and NOT, with each gate's listed arity at most two. It is not an arbitrary
two-input Boolean-gate basis. NOT uses its first input and ignores further listed
inputs. Empty AND/NOT gates compute true, and empty OR gates compute false.
Unary gates, repeated reads, and missing/forward reads are not ruled out by
`FanInTwo`; the sequential evaluator reads missing wires as false. There is no
`ReadsBack`, distinct-operand, first-gate, or monotonicity premise. Every listed
gate is counted, including constants and NOTs; raw inputs are free.

Consequently, the result also covers `Monotone2` circuits, by the inclusion of
the AND/OR basis in AND/OR/NOT. The conclusion is a bound on the entire
nine-input circuit, not on a suffix equipped with an extra free first signal.

The two root certificates cover the no-NOT case with 15 binary-operation steps,
and the case with at least one NOT with at most 14 non-NOT steps. `twoRoots`
bridges the concrete circuit to these cases. No first-OR condition enters that
bridge.

## Exact graph and task mapping

`L_meta_2446.edge` has the following ordered list of twelve terms:

```text
(0,1), (1,2), (2,3), (3,4), (4,0),
(0,5), (1,6), (2,7), (3,8), (5,7), (6,8), (8,5).
```

This is exactly the L2590 Petersen target with input 9 set to false, preserving
the original labels 0 through 8. The removed terms are `(4,9)`, `(7,9)`, and
`(9,6)`. The retained term order and orientation also match, so this particular
deletion requires no nontrivial permutation. Other deleted vertices require an
automorphism/relabeling argument, which was not constructed in this audit.

| Public task | Relationship to the internal result |
|---|---|
| L-meta-4033 | Exact same `¬ HasCircuitSize 9 (literal edge function) 15`; unfolding `edge` gives the displayed public target. |
| L-meta-3817 | Same function and bound, written `∀ C, FanInTwo C → C.size ≤ 15 → ∃ x, C.eval (List.ofFn x) ≠ edge x`. This follows by classical quantifier negation. |
| L-meta-2590 | Ten-input lower bound ≥20. The nine-input ≥16 result is useful for restriction, but still needs a justified deletion of at least four gates from a hypothetical circuit of size at most 19. |

The exact term-by-term comparison is recorded in `l2446-exact-match.json`.
Public statement SHA256 values from the 07:54:41 desk snapshot are:

- L3817: `ae9b705b99b45f9f94a415d84aa08f64ef5eae46f9a2d870c3be99de3b70a3f7`.
- L4033: `f9ae7d7917cf8eb72bf9aa50c8809a40504d463fa8c12f835b5045b6e832f0ff`.

## Official provenance and current status

The source was downloaded at upstream commit
`351fecac1b6c1fba40b6e45be9bf0058aa141b8a`:

- [Pinned L2446 source](https://github.com/open-goat/pequalnp-proofs/blob/351fecac1b6c1fba40b6e45be9bf0058aa141b8a/lean/PEqualNP/Outside/L_meta_2446.lean).
- [Public immutable L2446 record](https://data.pequalnp.com/data/lemma/L-meta-2446.37839bc8dcfc.json).
- [Merged PR #12680](https://github.com/open-goat/pequalnp-proofs/pull/12680), contributor `titoreinaldo`, merged 2026-11-25T06:48:46.056Z according to the public artifact record.
- [Official checker run](https://github.com/open-goat/pequalnp-proofs/actions/runs/45559995613), public runner ID `run-062291`, status `checked`.

Source SHA256:
`605dd7edce03d051f286b53b076f95a008d7aa544ff27a7ebf87d9bf1c192071`.
The source has 524,239 bytes, only 49 bytes below 512 KiB. A new official standalone
file would need careful dependency pruning if additional circuit-restriction
machinery is included. Merely replacing the public wrapper by the stronger
conclusion would shorten the source.

The source's original attribution must be retained: its nine-input certificates
are adapted from `0xshuzo`, project PR12203; its live-wire and smaller-graph
proofs are attributed to L1667, L1674, and L1677 contributors, including
`PressF10` and `zakpgrove`. A bounded attempt to read PR12203 metadata returned
HTTP403, so this audit makes no independent claim about that PR's status.

The fresh [public desk data](https://data.pequalnp.com/data/desk/gaps.json),
updated **2026-11-25T07:54:41.222Z**, reports:

| Task | Public state in this snapshot |
|---|---|
| L2446 | Checked, source hash as above. |
| L3817 | Posted, depth 2, no open PR, three live reductions. |
| L4033 | Posted, depth 2, four listed open PRs: #8645, #8668, #8774, #8890. |
| L2590 | Posted, depth 1, no open PR, three live reductions; no checked or withdrawn record. |

The contemporaneous read-only [2590 step response](https://pequalnp.com/desk/step?gap=L-meta-2590)
reports one holder, with `since` 2026-11-25T07:47:42.241Z. This is public task
metadata only; it does not establish that the parent's expired lease remains
valid or identify the holder. No private lease record was accessed.

## Bounded search for a stronger deleted-graph result

A scan of the 1,836 local `L_meta_*.lean` public source files at the existing
checkout found no final nine-input deleted-Petersen theorem giving a bound
of 17 or higher. A broad syntactic candidate list contained 127 entries, mostly
conditional bounds of 16 and smaller suffix bounds. The one apparent final
≥27 match was L1983 on a different, fourteen-input graph. This is a bounded
source audit, not a claim that all newly published upstream declarations have
been exhaustively searched. No unproved stronger bound is assumed.

The checked nine-input sources L1675 and L2923, already saved in the first audit,
do not improve the unrestricted bound established by L2446. L2923 concerns a
specific pair of free AND signals followed by a suffix, so its numbers cannot
be read as a 17-gate lower bound for an unrestricted circuit.

## Review of the parallel clean-case result

A read-only review of `Pnp2590Graph.lean` and the then-current
`Pnp2590CleanBound.lean` found the intended scope preserved. The graph target
matches the held task. The cover construction requires an explicitly clean
TopForm circuit. Normalization preserves size and the OR budget, so the
20-total-gate and 14-OR-gate bounds transfer to initially clean `Monotone2`
circuits. The six-AND bound is asserted only for the normalized TopForm circuit,
which is necessary because that minimization does not preserve the original
AND count. The small-circuit corollary gives an AND true on some negative input;
it does not assert that this input is a singleton or a nonedge pair.

No general dirty-AND cover bound was identified in this bounded review. The
clean-case theorem does not complete unrestricted L2590.

## Reproducibility

`defs-verification.json` records fresh downloads of `MetaComplexity.lean` and
`CircuitLowerBounds.lean` at commit351fec and confirms that both byte-match the
local definitions read during this audit. `stronger-deleted-status.json` preserves
the exact relevant task records and checked hash without any lease data.
The original checked source is already in the sibling `curated/` archive.
