# ACTIVE_WORK — 2026-11-25, continuation-13 publication

## Goal

Continue `KasuganoLove/pequalnp-proofs` toward a valid proof PR to the official upstream `open-goat/pequalnp-proofs`, with the official checker verdict recorded separately. This checkpoint is research preservation only: no new upstream PR or ACCEPTED verdict has been obtained.

## Current task

L-meta-9219 is the currently allocated task. Its exact proposition is `PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (7586366 : ℕ).testBit (5 * u.val + v.val)) 10`. The lease was last confirmed renewed at 2026-11-25 11:23:56.550907 UTC (HTTP 200). The task requires a circuit on the 25 one-left/one-right inputs, not every Boolean assignment. A correct 11-gate ordinary-computation baseline has been found, but it exceeds the limit. The first bounded 300-second SAT search ended UNKNOWN, without a model or an UNSAT certificate. A constructive search is also being evaluated. An open PR #13399 for the exact negated twin L-meta-9224 is being audited; no validity or acceptance is assumed before checking it.

The local Chrome connection is working; the visible signed-in GitHub account was verified as KasuganoLove. Authentication is no longer the active blocker. Use a fresh one-file, one-commit branch for any actual proof submission and preserve the exact task proposition.

## Closed task and durable new results

L-meta-650 was returned at 2026-11-25 11:14:32.704521 UTC (HTTP 200, missing_lemma). It has no ongoing solver or Lean job. Do not resume it without a fresh allocation. New work is under `research/2026-11-25/continuation-13/`:

- A genuine ordinary-Lean sublemma proves `Ustar.card ≤ 1` under explicit bipartition, NoFourCycle, IsAO2, empty centreless set, unique exceptional OR, top-shape, and positive-trace premises. The file, required extracted helper, attribution, reproduction command, and axiom audit are included. This is not the full 650/972/8793 proposition and has not been submitted as one.
- A bounded 23-gate, 18-input local SAT attempt ended UNKNOWN. A 24-gate local baseline and assembled 64-gate whole-plane baseline were exhaustively verified by ordinary programs; both exceed the requested witness bounds.
- The PG(2,3) lower-bound residual still needs the many-junk argument, specifically the remaining ledger/balance steps. No claimed completion is inferred from checked sublemmas.

## Previously ready proof, now not open

L-meta-8323's exact strict-checker-passed proof remains preserved at branch `codex/prove-meta-8323-2026-11-25`, head `0873097889691e4d21f575dabed0c1cadd0bcb3a`. At 11:08:20 UTC the step endpoint returned NOT_OPEN. At the 11:09:49 UTC ledger snapshot it was absent from gaps, checked, and withdrawn; its current official source path returned 404. The reason is unknown. Do not claim it was accepted, refuted, or still eligible for submission. The draft proposal is blocked and has not been sent.

## Publication integrity

This update is based on verified research head `0d0ad82d8ebf74a431135bc5b995e654a9aae91b`, preserving its history with a compare-and-swap branch update. Private lease records and secrets, full task-desk dumps, binaries, and large regenerable SAT artifacts are excluded. Continuation-13 is an immutable historical checkpoint of task650; later task9219 state must be recorded in a subsequent checkpoint.
