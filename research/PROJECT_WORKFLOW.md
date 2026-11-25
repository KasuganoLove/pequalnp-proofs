# P vs NP project: submission and completion standard

The owner explicitly clarified on2026-11-25: each completed stage must reach an official upstream PR. This replaces any earlier assistant interpretation that a review PR in the owner fork suffices.

- Official destination: `open-goat/pequalnp-proofs`.
- Working fork: `KasuganoLove/pequalnp-proofs`; the older `p-np-` repository is not needed for this workflow.
- A stage is complete when a valid proof or allowed reduction has been submitted upstream and the official checker has returned `ACCEPTED`. Report merge state separately. A submitted PR awaiting a verdict is pending, not accepted.
- Local Lean builds, local executions of the project checker, fork branches, archive commits and fork PRs are intermediate work. Do not report them as completed official contributions. In particular, fork PR#1 is an archive only and has been relabeled accordingly.
- Official submission is already authorized by the owner's project instructions; do not ask for repeated routine permission. Follow the actual current assignment, posted statement, and project submission rules. Do not invent task-selector parameters, exceptions, leases, or proof premises to obtain a submission.
- Distinguish full proofs, conditional subcases, exact symbolic certificates not yet formalized, solver evidence, and unsuccessful searches. Never present a resource fault or timeout as a mathematical verdict.
- If the legitimate task route or mathematical proof is blocked, state the exact blocker and keep the stage pending. Do not silently substitute a fork review PR for the required upstream result.

The latest continuation checkpoint is `research/2026-11-25/continuation-10/status.json`. Its stage_complete field is false.
