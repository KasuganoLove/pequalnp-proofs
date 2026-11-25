# ACTIVE_WORK — 2026-11-25 continuation-14 publication

## Goal and current result

Continue the P-vs-NP formal-proof effort using KasuganoLove/pequalnp-proofs and official upstream open-goat/pequalnp-proofs. The user wants a valid public upstream proof PR for each completed phase, with the official verdict accurately recorded. This checkpoint is research preservation only: no new official proof PR or ACCEPTED has been obtained.

## Active allocated problem

L-meta-2592 was allocated at 11:49:57 UTC and last confirmed renewed at 11:52:19.346576 UTC, HTTP 200. It says that a FanInTwo circuit of at most 19 gates containing at least one NOT cannot compute the full Petersen edge function on 10 inputs. It is not the monotone sibling2590 and does not assume exactly one essential NOT. The three reduction slots are full. Checked tools give a binary-gate floor and legal-read/last-NOT normalization, but the remaining quantitative children are still open; older accepted reductions must not be reported as complete lower bounds. Parallel structural and constructive investigation is ongoing. Root owns renewals, checker runs, and any publication.

The latest separate ordinary allocation request at 11:52:37 UTC returned no free new task and retry_after_s=300. Respect the retry period; after a successful release, join.txt explicitly permits asking immediately for a new task.

## Closed work preserved in continuation-14

- L-meta-9219: released 11:32:58.305482 UTC, HTTP200, statement_seems_false. A 300-second SAT attempt was UNKNOWN and a 300-second heuristic found only a 24/25 near miss. Subsequently, an existing upstream negative proof was checked by ordinary Lean with only the standard three axioms. It was not our new contribution.
- L-meta-9267 / negative twin9269: released 11:38:50.354622 UTC, HTTP200, statement_seems_false. A direct specialization of the checked tb-16 proof9195 compiled in18.326s. Strict checking ended FAULT, verifier exit137, with no mathematical verdict. The exact noncomment code was already in earlier PR13475, and the live step endpoint instructed asking for another task. No duplicate was submitted. An independent11-gate baseline and all25-row checks are preserved. Full third-party source is represented by a small patch and hash-checked reconstruction instructions.
- L-meta-2600: released 11:47:58.309728 UTC, HTTP200, missing_lemma. Its weaker PG3 lower bound63 still needs a new multi-exception argument. Strengthened ledger arithmetic and small finite counterexamples expose the precise remaining assumptions. Current-status claims retain their observation timestamps.
- L-meta-9457: released 11:49:50.899045 UTC, HTTP200, other. Its negative twin9458 already had PR13548 and the step endpoint reported pr_open; no new proof search or compilation was started.

## Previously ready, currently blocked proof

The exact strict-checked8323 proof remains at codex/prove-meta-8323-2026-11-25, head0873097889691e4d21f575dabed0c1cadd0bcb3a. The latest recorded step observation was NOT_OPEN at11:08:20 UTC, with no known reason or official acceptance. Do not submit that historical file as though its task were still open.

## Environment and publication

Local Chrome is connected and its visible GitHub account was verified as KasuganoLove. It is available for an authorized valid upstream PR; authentication is not the current obstacle. Follow the Browser plugin for user-local Chrome. Prepare one file and one commit on a fresh branch based on official main, preserve the exact posted statement, renew the live lease, then submit and record the actual official verdict.

Research history is based on verified head4cda9ff9fa8fe74973e5f5f19bba0ed453a29351. Continuation-14 is a dated checkpoint of the closed problems, with no lease secrets, full desk dumps, generated binaries, or SAT CNFs. Do not confuse the research archive or fork-only branches with an official completed phase.
