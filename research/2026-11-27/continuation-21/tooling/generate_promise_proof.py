#!/usr/bin/env python3
"""Offline witness packaging for PromiseColTree, with no task/lease/network actions.

This checks a supplied circuit, never searches for one.  Generated Lean is a
candidate: this program neither compiles it nor runs the project checker.
See README-promise-generator.md for the input contract and validation workflow.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path
from typing import Any

IMPORTS = (
    "import PEqualNP.Defs\n"
    "import PEqualNP.Library.Helpers.PromiseColTree\n"
)
MAX_LITERAL_DIGITS = 20
LIMB_BASE = 1 << 32
DECL_LIMITS = "set_option maxRecDepth 100000 in\nset_option maxHeartbeats 100000000 in\n"


class InputError(ValueError):
    pass


def nat(value: Any, label: str) -> int:
    if isinstance(value, bool):
        raise InputError(f"{label}: a Boolean is not a natural-number encoding")
    if isinstance(value, int):
        result = value
    elif isinstance(value, str) and re.fullmatch(r"(?:0[xX][0-9a-fA-F]+|[0-9]+)", value):
        result = int(value, 16 if value.lower().startswith("0x") else 10)
    else:
        raise InputError(f"{label}: expected a nonnegative integer or decimal/hex string")
    if result < 0:
        raise InputError(f"{label}: expected a nonnegative integer")
    return result


def lean_nat(value: int) -> str:
    """Emit only short decimal tokens; large values use base-2^32 Horner form."""
    if len(str(value)) <= MAX_LITERAL_DIGITS:
        return str(value)
    limbs: list[int] = []
    while value:
        limbs.append(value % LIMB_BASE)
        value //= LIMB_BASE
    expr = str(limbs.pop())
    for limb in reversed(limbs):
        expr = f"({limb} + {LIMB_BASE} * {expr})"
    return expr


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def read_json(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError) as exc:
        raise InputError(f"Cannot read JSON {path}: {exc}") from exc


def ceil_log2(value: int) -> int:
    return max(0, (value - 1).bit_length()) if value else 0


def parse_circuit(data: Any, output_override: int | None, mode: str) -> tuple[list[dict], int]:
    if isinstance(data, dict):
        records = data.get("gates")
        supplied_output = data.get("output")
    else:
        records, supplied_output = data, None
    if not isinstance(records, list):
        raise InputError("circuit: expected a gate array or an object with a gates array")
    if supplied_output is not None:
        supplied_output = nat(supplied_output, "output")
    if output_override is not None and supplied_output is not None and output_override != supplied_output:
        raise InputError("--output-wire disagrees with the circuit's output field")
    output = supplied_output if output_override is None else output_override
    if output is None:
        raise InputError("a bare gate array requires --output-wire")
    allowed = {"and", "or"} if mode == "monotone" else {"and", "or", "not"}
    gates: list[dict] = []
    for j, record in enumerate(records):
        if isinstance(record, dict):
            op, pins = record.get("op"), record.get("inputs")
        elif isinstance(record, list) and len(record) == 3:
            op, pins = record[0], record[1:]
        else:
            raise InputError(f"gate {j}: expected {{op,inputs}} or [op,a,b]")
        if not isinstance(op, str) or op.lower() not in allowed:
            raise InputError(f"gate {j}: operation must be one of {sorted(allowed)}")
        if not isinstance(pins, list) or len(pins) > 2:
            raise InputError(f"gate {j}: expected zero, one, or two input indices")
        gates.append({"op": op.lower(), "inputs": [nat(v, f"gate {j} input") for v in pins]})
    return gates, output


def eval_columns(gates: list[dict], output: int, n: int, m: int, N: int) -> int:
    """Exactly the padded library columns, including nullary gates and NOT tails."""
    row_bits = (1 << m) - 1
    columns = [row_bits << (u * m) for u in range(n)]
    columns += [sum(1 << (u * m + v) for u in range(n)) for v in range(m)]
    padded_mask = (1 << (1 << N)) - 1
    for gate in gates:
        values = [columns[i] if i < len(columns) else 0 for i in gate["inputs"]]
        if gate["op"] == "and":
            value = padded_mask
            for operand in values:
                value &= operand
        elif gate["op"] == "or":
            value = 0
            for operand in values:
                value |= operand
        else:
            value = padded_mask ^ (values[0] if values else 0)
        columns.append(value)
    return columns[output] if output < len(columns) else 0


def eval_scalar(gates: list[dict], output: int, n: int, m: int, u: int, v: int) -> bool:
    """Independent Boolean-list interpreter for a single physical oneEach input."""
    wires = [i == u for i in range(n)] + [i == v for i in range(m)]
    for gate in gates:
        pins = gate["inputs"]
        if gate["op"] == "and":
            result = all(wires[i] if i < len(wires) else False for i in pins)
        elif gate["op"] == "or":
            result = any(wires[i] if i < len(wires) else False for i in pins)
        else:
            result = not (wires[pins[0]] if pins and pins[0] < len(wires) else False)
        wires.append(result)
    return wires[output] if output < len(wires) else False


def lean_list(values: list[int]) -> str:
    return "[\n" + ",\n".join("  " + lean_nat(v) for v in values) + "\n]" if values else "[]"


def render_helpers(gates: list[dict], output: int, rows: list[int], replay_rows: list[int],
                   n: int, m: int, bound: int, N: int, D: int, mode: str, name: str) -> str:
    codes = ",\n".join(
        "  ⟨." + g["op"] + ", [" + ", ".join(lean_nat(i) for i in g["inputs"]) + "]⟩"
        for g in gates
    )
    gate_list = "[\n" + codes + "\n]" if gates else "[]"
    shape_bool = "monotone2B" if mode == "monotone" else "fanInTwoB"
    shape_type = "Monotone2" if mode == "monotone" else "FanInTwo"
    text = f"""namespace {name}
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Library.Helpers.Replay PEqualNP.Library.Helpers.ReplayCol
open PEqualNP.Library.Helpers.PromiseCol PEqualNP.Library.Helpers.PromiseColTree

def witness : Circuit := ⟨{gate_list}, {lean_nat(output)}⟩

def rowMasks : List ℕ := {lean_list(rows)}

theorem witness_shape_check : {shape_bool} witness = true := by decide +kernel

theorem witness_shape : {shape_type} witness :=
  {shape_bool}_sound witness_shape_check

theorem witness_size : witness.size ≤ {lean_nat(bound)} := by decide +kernel

"""
    target_type = (f"PEqualNP.Represents.Represents\n"
                   f"    (fun (u : Fin {n}) (v : Fin {m}) => (rowMasks.getD u.val 0).testBit v.val) witness")
    if n == 0 or m == 0:
        impossible = "u" if n == 0 else "v"
        text += f"theorem represented : {target_type} := by\n  intro u v\n  exact Fin.elim0 {impossible}\n"
    else:
        replay_def = "rowMasks" if replay_rows == rows else lean_list(replay_rows)
        text += f"""-- Padding rows are used only by the packed replay.  The public matrix is rowMasks.
def replayRowMasks : List ℕ := {replay_def}

theorem replay_rows_bound_check :
    replayRowMasks.all (fun r => decide (r < 2 ^ {m})) = true := by decide +kernel

theorem replay_rows_bound : ∀ r ∈ replayRowMasks, r < 2 ^ {m} := by
  intro r hr
  exact of_decide_eq_true (List.all_eq_true.mp replay_rows_bound_check r hr)

theorem replay_row_prefix : ∀ u : Fin {n},
    replayRowMasks.getD u.val 0 = rowMasks.getD u.val 0 := by decide +kernel

theorem replay_operations : aonB witness = true := by decide +kernel

theorem promise_capacity : {n} * {m} ≤ 2 ^ {N} := by decide +kernel

theorem tree_capacity : {n} + {m} + witness.gates.length ≤ 2 ^ {D} := by decide +kernel

-- The only packed circuit computation.  Soundness comes from the imported theorem.
theorem output_replay :
    ((tcols {N} {D} witness {n} {m}).1.rd {D} witness.output ==
      tcol {m} replayRowMasks) = true := by decide +kernel

theorem represented : {target_type} := by
  have h := represents_of_tcols (n := {n}) (m := {m}) (N := {N}) (D := {D})
    promise_capacity witness replayRowMasks replay_rows_bound replay_operations
    tree_capacity output_replay
  intro u v
  simpa only [replay_row_prefix u] using h u v
"""
    text = re.sub(r"(?m)^(?=def |theorem )", lambda _: DECL_LIMITS, text)
    return text + f"\nend {name}\n\n"


def provenance(root: Path | None) -> dict:
    if root is None:
        return {}
    relatives = [
        "PEqualNP/Library/Helpers/PromiseColTree.lean",
        "PEqualNP/Library/Helpers/PromiseCol.lean",
        "PEqualNP/Library/Helpers/ReplayCol.lean",
        "PEqualNP/Library/Helpers/Replay.lean",
        "PEqualNP/Defs/Represents.lean",
    ]
    result = {}
    for relative in relatives:
        path = root / relative
        if not path.is_file():
            raise InputError(f"missing referenced library file {path}")
        result[relative] = {"sha256": sha(path.read_bytes()), "bytes": path.stat().st_size}
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--circuit", type=Path, required=True)
    parser.add_argument("--rows", type=Path, required=True, help="JSON array of n row masks")
    parser.add_argument("--left", type=int, required=True)
    parser.add_argument("--right", type=int, required=True)
    parser.add_argument("--bound", type=int, required=True)
    parser.add_argument("--output-wire", type=int)
    parser.add_argument("--mode", choices=("fanin", "monotone"), default="fanin")
    parser.add_argument("--statement", type=Path, required=True, help="exact proposition text, without theorem declaration")
    parser.add_argument("--theorem", required=True, help="qualified gap name, also used as helper namespace")
    parser.add_argument("--final-proof", type=Path, help="optional trusted Lean tactic block, excluding initial 'by'")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--report", type=Path, help="default: output with suffix .audit.json")
    parser.add_argument("--lean-root", type=Path, help="optional lean/ root for source provenance hashes")
    parser.add_argument("--scalar-all", action="store_true", help="independently replay every promise input even for large witnesses")
    parser.add_argument("--max-promise-rows", type=int, default=1_048_576)
    args = parser.parse_args()
    try:
        n, m, bound = (nat(args.left, "left"), nat(args.right, "right"), nat(args.bound, "bound"))
        output_override = None if args.output_wire is None else nat(args.output_wire, "output-wire")
        if n * m > args.max_promise_rows or max(n, m) > args.max_promise_rows:
            raise InputError("dimensions exceed --max-promise-rows; choose an explicit adequate cap")
        if not re.fullmatch(r"PEqualNP\.Outside\.L_[a-z0-9_]+", args.theorem) or args.theorem.endswith("_aux"):
            raise InputError("--theorem must be PEqualNP.Outside.L_<lowercase_gap>, not an _aux name")
        gates, output = parse_circuit(read_json(args.circuit), output_override, args.mode)
        if len(gates) > bound:
            raise InputError(f"{len(gates)} gates exceed the supplied bound {bound}")
        raw_rows = read_json(args.rows)
        if not isinstance(raw_rows, list) or len(raw_rows) != n:
            raise InputError(f"rows must contain exactly {n} row masks")
        rows = [nat(v, f"row {u}") for u, v in enumerate(raw_rows)]
        if any(r >= 1 << m for r in rows):
            raise InputError(f"a row mask has a bit outside the {m} right vertices")
        N, D = ceil_log2(n * m), ceil_log2(n + m + len(gates))
        packed = eval_columns(gates, output, n, m, N)
        target = sum(r << (u * m) for u, r in enumerate(rows))
        mismatch = (packed ^ target) & ((1 << (n * m)) - 1)
        if mismatch:
            bit = (mismatch & -mismatch).bit_length() - 1
            raise InputError(f"witness fails at oneEach(left={bit // m}, right={bit % m})")
        scalar_ran = args.scalar_all or n * m * max(1, len(gates)) <= 2_000_000
        if scalar_ran:
            for u in range(n):
                for v in range(m):
                    if eval_scalar(gates, output, n, m, u, v) != bool((rows[u] >> v) & 1):
                        raise InputError(f"independent scalar replay failed at ({u},{v})")
        # The library's exact packed equality includes unused positions up to 2^N.
        # Extra row blocks preserve the real prefix and encode these harmless bits.
        replay_rows = rows.copy()
        if m and packed >> (n * m):
            row_mask = (1 << m) - 1
            for u in range(n, ((1 << N) + m - 1) // m):
                replay_rows.append((packed >> (u * m)) & row_mask)
        if m and packed != sum(r << (u * m) for u, r in enumerate(replay_rows)):
            raise InputError("internal error: padded replay target does not equal the computed column")
        statement_bytes = args.statement.read_bytes()
        statement = statement_bytes.decode("utf-8")
        if not statement.strip() or statement.lstrip().startswith(("theorem ", "lemma ", "import ")):
            raise InputError("--statement must contain the exact proposition only")
        final_tactics = (args.final_proof.read_text(encoding="utf-8") if args.final_proof else
                         f"  exact ⟨{args.theorem}.witness, {args.theorem}.witness_shape,\n"
                         f"    {args.theorem}.witness_size, {args.theorem}.represented⟩\n")
        helpers = render_helpers(gates, output, rows, replay_rows, n, m, bound, N, D, args.mode, args.theorem)
        prefix = (IMPORTS + "\n-- Generated offline; the exact public statement is supplied separately.\n"
                  "-- Library replay proves only the one-left/one-right representation promise.\n\n" + helpers)
        prefix += DECL_LIMITS + f"theorem {args.theorem} :\n"
        suffix = "\n:= by\n" + final_tactics
        source = prefix.encode() + statement_bytes + suffix.encode()
        # Do not rewrite the supplied statement to satisfy a syntax policy.
        # All numeric tokens that this generator itself emits have at most 20 digits.
        helper_literals = re.findall(r"(?<![\w])\d+", helpers)
        if any(len(token) > MAX_LITERAL_DIGITS for token in helper_literals):
            raise InputError("internal error: generated helper contains an overlong numeric token")
        statement_literals = re.findall(r"(?<![\w])(?:0[xX][0-9a-fA-F]+|\d+)", statement)
        statement_long = [len(t[2:] if t.lower().startswith("0x") else t)
                          for t in statement_literals if len(t[2:] if t.lower().startswith("0x") else t) > 20]
        report = {
            "schema": "promise-witness-generator-v1",
            "theorem": args.theorem,
            "mode": args.mode,
            "dimensions": {"left": n, "right": m, "promise_inputs": n * m},
            "gates": len(gates), "size_bound": bound, "output_wire": output,
            "sample_exponent_N": N, "tree_depth_D": D,
            "padded_sample_bits": 1 << N, "padding_rows_added": len(replay_rows) - len(rows),
            "semantics": "oneEach promise only; absent/future reads false; empty AND true; NOT only head pin",
            "python_column_replay": "PASS",
            "python_scalar_replay": "PASS" if scalar_ran else "NOT_RUN: use --scalar-all",
            "scalar_inputs_checked": n * m if scalar_ran else 0,
            "lean_compilation": "NOT_RUN",
            "strict_project_checker": "NOT_RUN",
            "generated_helper_max_decimal_token_digits": max(map(len, helper_literals), default=0),
            "public_statement_overlong_token_digit_counts": statement_long,
            "public_statement_preserved_verbatim": True,
            "statement_source_byte_interval": [len(prefix.encode()), len(prefix.encode()) + len(statement_bytes)],
            "source_sha256": sha(source), "source_bytes": len(source),
            "inputs_sha256": {"circuit": sha(args.circuit.read_bytes()), "rows": sha(args.rows.read_bytes()),
                              "statement": sha(statement_bytes)},
            "final_proof_adapter_sha256": sha(args.final_proof.read_bytes()) if args.final_proof else None,
            "referenced_library_sources": provenance(args.lean_root),
        }
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_bytes(source)
        report_path = args.report or args.output.with_suffix(".audit.json")
        report_path.parent.mkdir(parents=True, exist_ok=True)
        report_path.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
        print(json.dumps({"output": str(args.output), "report": str(report_path), "gates": len(gates),
                          "promise_inputs": n * m, "source_sha256": sha(source),
                          "lean_compilation": "NOT_RUN"}, ensure_ascii=False))
        return 0
    except (InputError, OSError, UnicodeError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
