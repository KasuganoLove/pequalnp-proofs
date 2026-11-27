# Promise witness generator

`generate_promise_proof.py` packages an already supplied circuit into a Lean
candidate. It performs no search, task allocation, lease operation, network
request, Lean build, strict check, or publication.

The generated source imports exactly:

```lean
import PEqualNP.Defs
import PEqualNP.Library.Helpers.PromiseColTree
```

All helper declarations live in the supplied gap's namespace. The final public
proposition is copied byte for byte from the statement file; its exact byte
interval and SHA-256 are recorded in the adjacent audit JSON. The generated
file is **not a checked proof until Lean and the project checker accept it**.

## Scope

For `n` left vertices and `m` right vertices, the target has `n * m` promise
inputs. Input wires `0 .. n-1` are the left indicators; wires `n .. n+m-1` are
the right indicators. On promise input `(u,v)`, precisely wires `u` and `n+v`
are true. Row mask `rows[u]` has bit `v` equal to the desired answer.

This certifies `PEqualNP.Represents.Represents`; it does **not** certify the
full Boolean graph edge function on all `2^(n+m)` assignments.

`--mode fanin` accepts AND, OR, and NOT gates with at most two listed pins,
and produces a `FanInTwo` proof. `--mode monotone` accepts only AND and OR
and produces a `Monotone2` proof, suitable for `RepSizeAtMost`. Both preserve
the repository's literal gate-list semantics:

- Gates are appended after the `n+m` raw inputs in their supplied order.
- An absent or future wire reads false; arbitrary output indices are allowed.
- Empty AND is true; empty OR is false.
- NOT negates only the first listed pin, or false when there is no first pin.
  A second listed NOT pin is ignored, as in `FanInTwo`.

The generator never normalizes a circuit or silently changes its gate count.

## Inputs

Circuit JSON is either an object:

```json
{"gates": [{"op": "and", "inputs": [0, 2]}], "output": 4}
```

or a bare array of gate records with `--output-wire` supplied separately.
Strict binary gates may also be written `["and", 0, 2]`. Numeric operation
codes are deliberately not guessed. Each natural number may be a JSON integer,
a decimal string, or a hexadecimal string such as `"0xff"`.

Rows JSON is an array containing **exactly `n`** masks; every mask must be
less than `2^m`. For example, `[1, 0]` describes the one-edge 2-by-2 matrix.
Dimensions, bound, mode, and qualified theorem name are explicit CLI arguments.

The statement file contains the proposition only, without a theorem name,
`:=`, or proof. The default final proof assembles:

```lean
⟨witness, witness_shape, witness_size, represented⟩
```

This directly matches the usual existential `FanInTwo` representation goal,
or the definition of `RepSizeAtMost` in monotone mode. Definitionally different
target descriptions may require an explicit statement-to-rows bridge.
`--final-proof adapter.lean.txt` supplies trusted tactic text excluding the
initial `by`. An adapter is ordinary source to be reviewed and checked; the
generator does not assert its correctness. It never changes the statement to
make an incompatible adapter fit.

## Invocation

From the repository workspace, with task-authorized witness inputs:

```bash
python pnp-session-2026-11-27/tooling/generate_promise_proof.py \
  --circuit witness.json \
  --rows row-masks.json \
  --left 2 --right 2 --bound 1 --mode fanin \
  --statement statement.txt \
  --theorem PEqualNP.Outside.L_meta_example \
  --lean-root pequalnp-proofs/lean \
  --output candidate/L_meta_example.lean
```

Use an actual public task name and its verbatim statement only when the project
workflow authorizes that task. The script itself does not acquire authorization
or inspect a lease. `--report` overrides the default `candidate.audit.json` path.

## Independent preflight

The generator first replays the supplied circuit with packed bit columns and
compares every physical promise bit to the given row masks. A mismatch stops
generation and reports the first `(u,v)` mismatch. For at most two million
scalar gate evaluations, it also runs a separate Boolean-list evaluator on
every promise input. `--scalar-all` forces this second check for larger
witnesses; otherwise the audit explicitly says that it was not run.

The preflight checks the input shape, gate count, operation mode, row-mask
range, output semantics, and scalar/packed agreement. It has no proof
authority: the output's audit always starts with `lean_compilation: NOT_RUN`
and `strict_project_checker: NOT_RUN`.

## Packed padding and tree capacity

The library argument `N` is an exponent: its Boolean columns have `2^N` bits.
The generator chooses the smallest `N` with `n*m <= 2^N`, and the smallest
tree depth `D` with `n+m+gates.length <= 2^D`.

When `n*m` is not a power of two, an empty AND or NOT can set unused high bits.
The library theorem asks for equality of the **whole** packed output, so merely
comparing physical low bits is not enough to construct its premise. The
generator therefore appends padding rows to a separate `replayRowMasks` list,
matching those high bits. It verifies that their first `n` entries are exactly
the supplied `rowMasks`. `represents_of_tcols` permits extra rows, and the
generated `replay_row_prefix` lemma transfers its result back to the real
matrix. No physical target row or public statement is altered. When either
side has zero vertices, representation is vacuous and the source uses
`Fin.elim0`, avoiding a meaningless replay equality.

## Kernel and numeric-literal design

- The output uses the imported balanced-tree replay, never a fresh evaluator
  or a full `Represents` computation over all pairs.
- Shape, size, row bounds, prefix equality, capacity, and output replay are
  separate theorem declarations. Only `output_replay` executes the whole
  circuit. Other proofs reuse the library's soundness theorem.
- Limits use `set_option ... <number> in` immediately before each declaration,
  including the final theorem. No option is set for the whole file or namespace.
- Every generated helper numeric token has at most 20 decimal digits. Larger
  values are base-`2^32` Horner expressions with short limbs. This includes
  large row masks, wire indices, and bounds.
- The public statement is never reformatted or rewritten. Any overlong
  numeric tokens in that external statement are reported separately for the
  project's statement policy; the generator does not invent an exemption or
  make the statement different.
- The final-proof adapter is external trusted input. Its syntax, dependencies,
  numeric literals, and exact statement fit remain subject to normal review
  and the official source guard.

The balanced tree removes the list replay's repeated linear lookup/append
overhead. It does not promise a fixed memory ceiling: large columns or long
circuits can still require substantial kernel resources. Avoid adding an
extra direct `by decide` proof of the whole representation proposition.

## Validation workflow when the environment is ready

1. Generate the candidate and retain the exact input files and audit JSON.
2. Check the audit's embedded statement byte interval against the public
   statement; review mode, dimensions, row order, and gate output numbering.
3. Run the project's source guard and a single ordinary Lean build in the
   pinned environment. Do not label the Python preflight as a Lean result.
4. Run the official strict checker on the immutable compiled candidate and
   exact statement. Record its exit code and explicit verdict. A killed
   process or ordinary Lean success is not an `ACCEPTED` strict verdict.
5. Follow the current authorized submission/lease workflow. This tool performs
   no remote write and cannot itself complete a project task.

## Provenance and current validation boundary

The source interface was read from these files in checkout
`3db0136bf094e975baaf20214b01e4b4579059f2`:

- `PEqualNP/Library/Helpers/PromiseColTree.lean`
- `PEqualNP/Library/Helpers/PromiseCol.lean`
- `PEqualNP/Library/Helpers/ReplayCol.lean`
- `PEqualNP/Library/Helpers/Replay.lean`
- `PEqualNP/Defs/Represents.lean`

Existing usage patterns were read in `L_meta_19357.lean`, `L_meta_19358.lean`,
and `L_meta_20578.lean`. The first two use only the same two imports. This
generator imports the reusable proof library; it does not copy those submitted
circuits or claim their authorship. Passing `--lean-root` records the exact
library-file hashes in each audit.

The generator was initially prepared while the environment was being restored.
After restoration, the one synthetic smoke candidate was compiled with
`lake env lean -j1` on 2026-11-27 at 03:12:40–03:12:44 UTC: **exit 0**, empty
stdout/stderr, 3.553 seconds. The full command, immutable source hash, and timing
are in `smoke/ordinary-result.json`; the log is `smoke/ordinary.log`. No official
strict checker was run, and this synthetic fixture is not a public task proof.

Twelve synthetic Python checks passed; see `python-checks.json`. The synthetic
`smoke/L_meta_generator_smoke.lean` also passed the current official tool's
extracted `format_py` with exit 0 and empty output, recorded in
`smoke/format-result.json`. This checks the actual guard, rather than a locally
reimplemented approximation. The format check and the separate ordinary Lean
run are distinct records; neither is an official strict-check verdict.

Reproduce these tooling-only checks without running Lean:

```bash
python pnp-session-2026-11-27/tooling/check_promise_generator.py
python pnp-session-2026-11-27/tooling/run_promise_smoke.py \
  --pnp-tool pnp-session-2026-11-27/resume/config-reference.local-only/new/tools/pnp.sh \
  --lean-root pequalnp-proofs/lean
```

The second command extracts the guard as text and runs only that Python body;
it never sources or executes the shell tool. Its tiny input state describes
allowed imports for a synthetic fixture and contains no live task or lease.
