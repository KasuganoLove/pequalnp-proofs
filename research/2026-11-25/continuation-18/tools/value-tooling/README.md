# Generic VALUE certificate tooling

Prepared 2026-11-25 while no VALUE task was assigned. The only solver input tested here is a self-chosen contradictory two-variable CNF, not an offered project task.

## Shortest available path

Use the existing CaDiCaL 2.1.2 binary. It writes text LRAT directly:

```sh
cadical --lrat --no-binary --unsat -t 300 formula.cnf proof.lrat
```

Exit **20** means UNSAT, **10** means SAT, and **0** means UNKNOWN/time limit. Only an UNSAT result with a complete certificate can enter the lower-bound path. Check the exit code; a partial proof file after a timeout is not a certificate.

No DRAT-to-LRAT conversion or additional installation is needed. The project generator accepts RUP additions with positive LRAT hints. It explicitly rejects negative RAT hints. If that rejection occurs, retain the evidence and choose a separately bounded supported solver configuration; never drop unsupported proof additions and claim success.

The available upstream generator is:

```
/workspace/scratch/65f339da29fe/pequalnp-upstream-b9ee4cd/notes/data/lrat-link/genrow.py
```

This file has Git blob `e3ae1049bf652a8d652ec3168751495ec538dee0`, identical to fresh upstream main as read during preparation. The older generator in the primary57164c checkout lacks the `--not` option. Use the newer one. Immutable source: https://github.com/open-goat/pequalnp-proofs/blob/b9ee4cd40b7d244de81c9c4d1403325dd7767c8b/notes/data/lrat-link/genrow.py

After the workspace agent exports the exact `LinkN.enc2` CNF, call the generator with structured process arguments, equivalent to:

```sh
python genrow.py formula.cnf proof.lrat generated-lower.lean Namespace N S ROWS FEXPR --not --seg 20000
python localize_generated_limits.py generated-lower.lean lower-local-limits.lean
```

Here `S` is the excluded gate budget, `ROWS` is the comma-separated exact row list, and `FEXPR` is the exact Boolean function expression in `x`. These parameters must match the CNF exporter. Use all truth-table rows for ordinary four-input exact circuit-size work unless the formal link explicitly justifies a different choice. The final `F` sent to the Lean checker is `enc2 N S (rowFun N fn) rows` itself; the CNF is not trusted as an arbitrary replacement for this formula.

The localizer removes the generator's two global limit options and places limits before each generated definition and theorem, including packed-list data and the certificate segments. This is required by outside-guard. It does not produce the complete VALUE file: the root still supplies the exact canonical final statement, a verified upper-bound circuit, the task-specific namespace/file name, allowed imports, attribution, format guard and full checker.

## Actual checker API

The current `PEqualNP.Library.LRAT.Checker` module does **not** expose a `checkPacked` identifier. Its API is:

```lean
check_sound F keys tokens accepted
checkW_sound F keys width words accepted
checkFirst_sound F keys width words boundary accepted
checkSeg_sound boundary width words nextBoundary accepted
checkLast_sound boundary width words accepted
```

The first two conclude `¬ FormulaSat F`; segment soundness lemmas thread satisfaction of the retained boundary clauses. `accepted` must be an actual proof that the corresponding Boolean check equals true, normally `by decide +kernel`. This uses the kernel, not `native_decide`.

The circuit link in namespace `PEqualNP.Library.LRAT.LinkN` is:

```lean
size_of_unsat2 n s f rows hrows unsat
```

It concludes `∀ t, HasCircuitSize n f t → s + 1 ≤ t`, including AND, OR and NOT gates and counting every gate. `hrows` proves each row index is below `2^n`. There is no silently free NOT in this model.

Source provenance and fresh main blob identities are recorded in `source-provenance.json`. The modules are public Apache-2.0 project sources; retain their attribution when adapting helpers. The workspace agent owns LinkN/LinkN2 dependency setup and exact enc2 export; this directory does not change canonical library files.

## Tiny end-to-end sanity sample

`sanity.cnf` excludes every assignment of two variables with four clauses. The bundled CaDiCaL returned UNSAT/exit20 in0.0047seconds and wrote three LRAT additions, seven RUP hints,37bytes. `sanity-run.json` records the exact binary hash and command. No external converter was used.

Regenerate the omitted CNF with `python make_sanity_cnf.py sanity.cnf`, then rerun the CaDiCaL command above. To reproduce certificate packing:

```sh
python lrat_to_kernel_smoke.py sanity.cnf sanity.lrat PnpValueLratSanity.lean
```

The small emitter parses and checks the RUP hint structure independently and produces both unpacked and packed kernel-checking theorems. It is a smoke-test helper; use upstream `genrow.py` for trimmed/segmented real circuit certificates. `PnpValueLratSanity.packing.json` records its exact tokens and packed word.

Both generated theorems passed ordinary single-thread Lean at14:55:28 UTC, exit0 in1.407seconds. `sanity-lean.json` and `sanity-lean.log` record the result; both theorems use only propext, Classical.choice and Quot.sound. This was a generic tool smoke test, not an official task submission or a strict-checker run. The solver result and Python parser did not substitute for that kernel check.
