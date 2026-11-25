# Verified research stage: PG(2,4) and Petersen circuit bounds

This public review package records completed Lean work and the precise remaining obligations. It is prepared for review in `KasuganoLove/pequalnp-proofs`. It is not an official accepted upstream proof of L-meta-4201 or L-meta-2590, and it does not settle P versus NP.

## Results and validation

| Result | What is proved | Validation reached |
| --- | --- | --- |
| **L-meta-8323** | A correct, initially clean Monotone2 circuit for the specified 42-input projective-plane incidence function requires at least **104 OR gates**. | Exact public statement; standalone Defs-only source; local project checker **ACCEPTED (check)**, exit 0, 2,344 constants rechecked. No upstream submission or acceptance for this proof. |
| **L-meta-8470** | Every nonempty incidence-rectangle cover has total weight at least **105**, with overlaps allowed. | Exact public statement; local project checker **ACCEPTED (check)**, exit 0, 1,676 constants rechecked. Another contributor's proof was already merged upstream, so no duplicate official PR was sent. |
| **Petersen clean case** | A correct, initially clean Monotone2 circuit for the fifteen-edge Petersen function requires at least **20 total gates** and **14 OR gates**. | Two ordinary Lean builds succeeded; six key declarations have only the standard allowed axioms. This conditional component has not received a standalone strict-checker verdict. |

The two strict-checker results above are local executions of the project's checker. They are not official project verdicts or credit records.

## Why the clean premise matters

A clean AND gate can be true only on inputs where the desired output is also true. The new normalization and minimization arguments preserve this property when it already holds. They do not create it for arbitrary circuits. This distinction is explicit in the theorem statements and in the review notes.

For the incidence problem, the remaining parent obligation is either to construct a clean replacement without increasing the OR count, or to extract an appropriately bounded rectangle cover from an arbitrary circuit. For Petersen, the completed proof forces any nineteen-gate counterexample to contain a dirty AND, but that remaining class has not been eliminated.

## Review entry points

- [Continuation 8: exact 8323 and 8470 proofs, strict logs and dependencies](continuation-8/README.md)
- [Standalone 8323 proof](continuation-8/strict-8323/L_meta_8323.lean) and [strict result](continuation-8/strict-8323/strict-result.json)
- [Standalone 8470 proof](continuation-8/strict-8470/L_meta_8470.lean) and [strict result](continuation-8/strict-8470/strict-result.json)
- [Continuation 9: Petersen clean-case proof, finite searches and upstream audit](continuation-9/README.md)
- [Petersen exact theorem scope and ordinary verification](continuation-9/L-meta-2590/clean-case/README.md)

The full proof and reproduction evidence are retained in the files, including historical unsuccessful checker runs and their later fixes. Source manifests distinguish the final accepted local files from earlier resource-limited attempts.

## Upstream submission state

The official repository is now `open-goat/pequalnp-proofs`. The completed 8323 child has no live lease held by this session. The parent 4201 lease was released with `missing_lemma`; the later 2590 lease returned HTTP 410, after which new proof work stopped. The documented allocator repeatedly returned no available task during packaging.

This review PR is therefore a concrete public handoff in the owner's fork. It is not registered with the official desk as a completed parent proof. A future upstream submission must satisfy the current desk assignment and the exact posted statement.

L-meta-8470 was already merged in [upstream PR #12699](https://github.com/open-goat/pequalnp-proofs/pull/12699) by `dantwiddy-max`; the independent proof in this archive claims no official priority or credit for that merge.

## Reproducibility

The pinned semantic environment is Lean **4.36.0**, Mathlib **fc4f59e577feb1a4956671bc04ac18aaaf8cd842**, and the project definitions/checker verified at upstream **259523a5b265318b84f9377f2feb965fd213f898**. Continuation 8 records the complete environment comparison. Its README gives the exact strict-checker commands; continuation 9 records ordinary component builds and the reproducible bounded-search commands.

Only research source, validation evidence and documentation are added. The proof checker's rules and the project definitions are not modified by this package.
