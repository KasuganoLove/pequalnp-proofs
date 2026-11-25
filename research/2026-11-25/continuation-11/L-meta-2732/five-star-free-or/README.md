# Targeted five-star construction for the held positive task L-meta-2732

This is a bounded synthesis attempt, not a proof of the positive task or its negative twin. The parent agent held L-meta-2732 while this work was performed. The closed L-meta-2733 lease is not used.

## Construction target

The four hubs `a,b,e,f` of a subdivision of K4 have six subdivision variables `c,d,p,q,r,s`. The edges are

```
ad, bd, ec, fc, ap, ep, aq, fq, br, er, bs, fs.
```

The opposite original K4 edges have subdivision variables `c` and `d`. Raw input labels0…9 are `[a,b,e,f,c,d,p,q,r,s]`. Column10 is the **coupled** value `c OR d`; it is never treated as an independent input in the synthesis samples.

The target is a monotone suffix of at most14 gates computing this12-edge function from the11 supplied columns. Charging one prefix gate for `c OR d` makes a15-gate circuit exposing that signal. Three further gates then compute the five-star gadget:

1. OR the exposed signal with a pendant variable `l`.
2. AND that result with the fifth point `t`.
3. OR it with the subdivision-K4 output.

For the exact Heawood graph, map raw0…9 to `[0,3,2,4,13,7,8,10,12,11]`, take `t=1` and `l=9`, and retain the point5 and point6 stars. Their six gates and two final combination OR gates produce26 gates in total.

This is a sufficient construction strategy. Failure to find its14-gate suffix would not refute every18-gate five-star circuit or every26-gate Heawood circuit.

## Exact formula and independent validation

`problem.json` records the graph and all physical boundary samples. There are12 minimal positive edge rows and12 maximal independent negative rows. Monotonicity in the ten original variables implies that these boundary rows determine the graph function on all1024 original assignments; the supplied OR column is itself monotone in those variables.

`ExportFreeOrCNF.lean` directly calls the project's unmodified `PEqualNP.Defs.LratEncoding.enc2 11 14`. It emits74,123 clauses and a DIMACS maximum variable index244,733. Labels use the original ten bits. Only the24 physical augmented rows are included.

`run_sat.py` runs the bundled CaDiCaL executable with a300-second limit and a2GiB address-space cap. Its stdout and final result are saved locally. An UNKNOWN result is not an impossibility proof; an UNSAT solver result would still require a checked certificate and a formal completeness bridge before use in an official proof.

If a SAT model exists, `verify_model.py` checks every DIMACS clause, decodes selected operations and wires, exhausts all1024 original assignments, assembles the explicit26-gate Heawood circuit, and exhausts all16,384 Heawood inputs. This would still leave Lean validation and the public first-two-gate orbit normalization before official submission.

## Reproduction

From the original project's `lean` directory with its pinned toolchain environment:

```
lake env lean --run /absolute/path/to/ExportFreeOrCNF.lean /absolute/path/to/subdivision-k4-free-or-14.cnf
python /absolute/path/to/run_sat.py
python /absolute/path/to/verify_model.py
```

The runner's solver path identifies the executable used in this workspace; set it to the corresponding pinned CaDiCaL executable when relocating the directory. The verifier intentionally exits without producing witness files unless a SAT model is present.

## Existing lower-bound context

The existing checked source `L_meta_516` proves at least12 gates for the theta(3,3,3) graph, even with AND/OR/NOT. Together with ordinary essential-variable restriction, that blocks the isolated collinear four-star14-gate repair. The other four-point orbit is a subdivision of K4, whose14-gate possibility is refuted by existing `L_meta_3516` after the usual monotone normalization. No new Lean lower bound is claimed in this directory.

## Bounded attempt outcome

The run lasted from09:37:43.508 to09:42:43.553 UTC on2026-11-25 and returned **UNKNOWN** after300.045 wall seconds. CaDiCaL reported3,752,417 conflicts and108.28MB peak resident memory. There is no satisfying model, no UNSAT verdict, and no formal certificate. The witness verifier was prepared but not run because there was no model. No repeat solver run was launched.

The source exporter completed with exit0; `export-observed.json` records its observed stdout and source/Defs/CNF hashes. `result.json` and `cadical.log` preserve the bounded solver outcome. The exact CNF SHA256 is `c286a7abd561d1eb459190be6033fd8a188d0fd0f7c772e42946da29fe10d95a`.

## Compact checkpoint

The regenerable DIMACS CNF, Python bytecode, and original whole-directory manifest are omitted. The actual source/log/result files are unchanged; top-level STAGING.json retains the excluded CNF hash and top-level manifest.json covers this selected publication.
