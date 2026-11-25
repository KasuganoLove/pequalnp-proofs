# Heawood 26-gate diagnostic SAT run

This folder preserves the actual Lean exporter, exact 58 physical boundary rows, solver log, and bounded result. It is not a proof of L-meta-2732 or of its negative twin.

The exporter calls the project's unchanged `PEqualNP.Defs.LratEncoding.enc2 14 26`. The observed DIMACS header is 3,514,951 maximum variable index and 482,401 clauses. CaDiCaL 2.1.2, using default options and `-t 300`, ended with UNKNOWN after approximately 300.053 seconds. There is no satisfying model or checked unsatisfiability certificate.

The 23,569,804-byte CNF is omitted from this compact checkpoint; its SHA256 is `312044659a95802b61d8da32ea967451fcbc2257a2b27b97c97a390398fecdb0`. Regenerate it with the pinned project environment, from the checkout's `lean/` directory:

```bash
lake env lean --run /absolute/path/to/ExportHeawoodCNF.lean 26 /absolute/path/to/heawood-26.cnf
/path/to/cadical -t 300 /absolute/path/to/heawood-26.cnf
```

These are reproducibility instructions, not an automatic rerun request. A future search must have the applicable project task authorization. An UNSAT solver result alone would still require a checked certificate and a formally justified encoding bridge before being an official theorem.

