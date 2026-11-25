# L-meta-10083: cycle-family boundary and directed Rank test

This is research on the held negative task for k=15. No complete lower bound
or circuit with at most103 gates has been obtained here. All computations
described below are ordinary programs, not Lean or official checker results.
Root owns the lease, remote writes, and any official submission.

The single directed SAT run finished **UNKNOWN**, exit0, from
2026-11-25 12:16:12.646400 UTC to12:21:12.695270 UTC (300.049 seconds).
It made2,674,948 conflicts and4,049,353 decisions, with216.33MiB reported
peak resident memory. No model or complete UNSAT certificate was obtained,
and no second solver run was started. The648,373,859-byte compressed LRAT
trace is incomplete and is excluded from publication; its hash is recorded
in rank-sat/incomplete-trace.json. The Rank>=15 lemma remains unresolved.

## Exact family and verified104-gate control

Write the45 labels as A_i=i, B_i=15+i, C_i=30+i, with i modulo15. The
undirected graph is the union of the15 complete bipartite blocks

    {A_i,B_i} x {A_(i+1),C_i}.

The public representation task tests only one left raw input and one right
raw input at a time. Merge the two copies of each label using
z_v=left_v OR right_v. Each block is then

    (z_A_i OR z_B_i) AND (z_A_(i+1) OR z_C_i).

OR the15 block terms. The gate count is45 merge ORs +30 local ORs +15 ANDs
+14 output ORs =104. `baseline.py` generates every gate and checks the
literal public predicate on all2,025 oneEach inputs. There are120 positive
matrix entries and zero mismatches. The control is **one gate above** the
task cap, so it does not refute the negative task.

## Reused generic theorem and the exact unresolved invariant

The officially accepted proof PR13556 for L-meta-9484, head
2729f5c656ee99b60af92b92f1c6a45d549b431a, supplied a generic dependency and
twin-deletion theorem. Its source is preserved by the remote-status agent
at ../status-audit/PR13556-L_meta_9484.lean, SHA256
6a9c99d2183fbc3dea25bcb4c6a6d99d7c9fc6bc2bffb731aeb2e2f164fd4bbe.

Its `Rank A r R C` deletes one class of equal rows and one class of equal
columns simultaneously per round, then requires the remaining matrix to
satisfy Bic: every2x2 rectangle with three1s has its fourth entry1. The
classes are compared against the rows/columns present **before** both
deletions in that round. Empty classes are permitted.

`cut_budget` gives a dependency set N and a rank budget r with
|N|+r <= gates+1. Every raw input is necessary for this matrix (each row and
column has a1 and no row or column is universal), so |N|>=90. A103-gate
circuit would therefore imply Rank A14 on the full45x45 matrix.

Consequently a proof that Rank A14 is impossible would finish the task
through this generic theorem. The accepted k5 proof only excludes **three**
rounds: its successive class bounds are1,1,2 per side, giving at most8
deleted labels, while its terminal Bic obstruction requires10. There is
no established general2(r+1) deletion bound to substitute at r=14. Classes
can grow as opposite labels disappear. A numeral-only adaptation is invalid.

Useful structural identities, not yet a completed charging argument:

    N(A_i) = N(B_i) disjoint-union N(C_(i-1)),
    N(B_i) = {A_(i+1),C_i},
    N(C_(i-1)) = {A_(i-1),B_(i-1)}.

Thus the rows split into15 disjoint triples {A_i,B_i,C_(i-1)}; the columns
have the same decomposition. In a terminal Bic matrix, if all three labels
of such a row triple survive, one of the two operand rows must have become
zero. The same statement holds for column triples. No bound of two resolved
triples per deletion round has been proved: removing opposite labels can
zero profiles and merge classes, which is the missing amortized argument.

## Bounded small Rank probes

`rank_probe.py` is an ordinary recursive search over full current twin
classes. It is not a theorem prover. For k3 at two rounds it exhausted2,962
recursive calls in about0.007s without a witness. For k5 at four rounds it
timed out after20s and about6.56million calls. Neither output is a Lean
certificate, and neither settles the k15 task. Positive schedules would
be replayed directly; even a valid Rank schedule is only a necessary
circuit condition, not a construction of a representing circuit.

## Exact directed SAT encoding

The parent authorized one300-second, one-GiB solver run on Rank14, separate
from gate-level circuit synthesis. `rank-sat/encode.py` uses no symmetry
breaking. Each of the90 labels gets exactly one value in{0,...,14}:0 means
survive, while t>0 means deleted in round t. Prefix variables state deletion
in some positive round no later than t.

For each row pair deleted in the same round t, every column on which their
original entries differ must have been deleted strictly before t. The
analogous constraints are imposed for column pairs. At the end, each
three1/one0 rectangle must contain at least one deleted label. This is
exactly the finite Rank recursion; the encoding makes no hypothesis about
circuit gates or an unknown circuit's normal form.

The instance has2,610 variables and153,630 clauses, in five blocks:

| Block | Clauses |
|---|---:|
| Exactly one deletion value |9,540|
| Prefix definitions |10,710|
| Same-round row twins |66,510|
| Same-round column twins |66,510|
| Terminal Bic |360|

The CNF is2,582,217 bytes, SHA256
61c7a35162c198fb8f023c5bfca8b005a9ca37b1071f22f2734da162f4d291ab.
The encoder compared CNF satisfaction with a separately implemented direct
Rank replay on4,498 control schedules: all4,096 schedules for k2 with one
round,400 deterministic random schedules, and two valid k-round controls.
These tests support implementation consistency; they are not a formal
proof of the encoding.

`rank-sat/run.py` records exact times, verdict, resource bounds, and hashes
in sat-result.json. It requests compressed text LRAT output. A SAT verdict
must additionally pass verify_model.py, which checks all clauses, every
round's literal twins, and the final Bic condition. An UNSAT solver verdict
alone would not establish the Lean theorem; both the encoding bridge and
the proof certificate would still require formal verification.

For a bounded reproducible run, from this directory:

```sh
python baseline.py
python rank-sat/encode.py
PNP10083_CADICAL=/absolute/path/to/cadical python rank-sat/run.py
```

Run verify_model.py only if sat-result.json reports SAT. The automatic
workflow performs no solver rerun. CNF files and large incomplete proof
traces are reproducible intermediates and are excluded from the curated
manifest. The official task statement and PR source remain outside this
subdirectory; no lease credentials are used by these programs.
