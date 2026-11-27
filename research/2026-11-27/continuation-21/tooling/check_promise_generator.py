#!/usr/bin/env python3
"""Small synthetic checks for the offline generator; never invokes Lean."""
from __future__ import annotations

import importlib.util
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
GENERATOR = HERE / "generate_promise_proof.py"
spec = importlib.util.spec_from_file_location("promise_generator", GENERATOR)
gen = importlib.util.module_from_spec(spec)
assert spec.loader is not None
spec.loader.exec_module(gen)


def main() -> None:
    cases = [
        ("one_edge", 2, 2, [{"op": "and", "inputs": [0, 2]}], 4, [1, 0], "fanin"),
        ("constant_padding", 1, 3, [{"op": "and", "inputs": []}], 4, [7], "monotone"),
        ("not_padding", 1, 3, [{"op": "not", "inputs": []}], 4, [7], "fanin"),
        ("not_ignored_tail", 1, 3, [{"op": "not", "inputs": [1, 0]}], 4, [6], "fanin"),
        ("forward_default", 1, 2, [{"op": "or", "inputs": [4]}, {"op": "and", "inputs": []}], 3, [0], "fanin"),
        ("absent_output", 1, 2, [], 999, [0], "fanin"),
        ("raw_output", 2, 2, [], 3, [2, 2], "monotone"),
        ("zero_left", 0, 3, [{"op": "not", "inputs": []}], 3, [], "fanin"),
        ("zero_right", 2, 0, [{"op": "and", "inputs": []}], 2, [0, 0], "monotone"),
        ("large_limb_row", 1, 80, [{"op": "and", "inputs": []}], 81, [(1 << 80) - 1], "monotone"),
    ]
    checked = []
    with tempfile.TemporaryDirectory(prefix="promise-generator-fixtures-") as tmp:
        work = Path(tmp)
        for label, n, m, gates, output, rows, mode in cases:
            case = work / label
            case.mkdir()
            (case / "circuit.json").write_text(json.dumps({"gates": gates, "output": output}))
            (case / "rows.json").write_text(json.dumps(rows))
            # These are synthetic generator fixtures, not claims about a desk task.
            shape = "PEqualNP.MetaComplexity.Monotone2" if mode == "monotone" else "PEqualNP.MetaComplexity.FanInTwo"
            statement = (f"(∃ C : PEqualNP.CircuitLowerBounds.Circuit, {shape} C ∧ "
                         f"C.size ≤ {len(gates)} ∧ PEqualNP.Represents.Represents "
                         f"(fun (u : Fin {n}) (v : Fin {m}) => "
                         f"(({rows!r} : List Nat).getD u.val 0).testBit v.val) C)\n")
            (case / "statement.txt").write_text(statement, encoding="utf-8")
            command = [sys.executable, str(GENERATOR), "--circuit", str(case / "circuit.json"),
                       "--rows", str(case / "rows.json"), "--left", str(n), "--right", str(m),
                       "--bound", str(len(gates)), "--mode", mode,
                       "--statement", str(case / "statement.txt"),
                       "--theorem", "PEqualNP.Outside.L_meta_generator_fixture",
                       "--output", str(case / "candidate.lean"), "--scalar-all"]
            result = subprocess.run(command, capture_output=True, text=True)
            assert result.returncode == 0, (label, result.stderr)
            audit = json.loads((case / "candidate.audit.json").read_text())
            source = (case / "candidate.lean").read_bytes()
            start, end = audit["statement_source_byte_interval"]
            assert source[start:end] == (case / "statement.txt").read_bytes()
            assert source.decode().splitlines()[:2] == gen.IMPORTS.splitlines()
            assert source.count(b"import ") == 2
            assert not re.search(rb"(?m)^set_option [^\n]+(?<! in)$", source)
            assert audit["lean_compilation"] == audit["strict_project_checker"] == "NOT_RUN"
            assert audit["python_scalar_replay"] == "PASS"
            assert audit["generated_helper_max_decimal_token_digits"] <= 20
            if label in ("constant_padding", "not_padding", "not_ignored_tail", "large_limb_row"):
                assert audit["padding_rows_added"] > 0
            if label == "large_limb_row":
                assert b"4294967296" in source[:start]
                assert audit["public_statement_overlong_token_digit_counts"]
            checked.append({"case": label, "promise_inputs": n * m,
                            "padding_rows_added": audit["padding_rows_added"], "result": "PASS"})

        # The CLI must fail before creating source for a mismatching witness.
        case = work / "one_edge"
        (case / "rows.json").write_text("[0,0]")
        bad_command = [sys.executable, str(GENERATOR), "--circuit", str(case / "circuit.json"),
                       "--rows", str(case / "rows.json"), "--left", "2", "--right", "2",
                       "--bound", "1", "--statement", str(case / "statement.txt"),
                       "--theorem", "PEqualNP.Outside.L_meta_generator_fixture",
                       "--output", str(case / "must-not-exist.lean")]
        result = subprocess.run(bad_command, capture_output=True, text=True)
        assert result.returncode == 2 and "fails at oneEach" in result.stderr
        assert not (case / "must-not-exist.lean").exists()
        checked.append({"case": "reject_incorrect_witness", "result": "PASS"})

    # Check emitted short-limb arithmetic itself, rather than only its length.
    for value in (0, 1, (1 << 64) - 1, 10**20, (1 << 257) + (1 << 128) + 42):
        expr = gen.lean_nat(value)
        assert re.fullmatch(r"[0-9 ()+*]+", expr)
        assert eval(expr, {"__builtins__": {}}) == value
        assert all(len(t) <= 20 for t in re.findall(r"\d+", expr))
    checked.append({"case": "large_limb_arithmetic", "result": "PASS"})
    print(json.dumps({"scope": "synthetic Python generator checks only",
                      "lean_compilation": "NOT_RUN", "strict_project_checker": "NOT_RUN",
                      "checks": checked}, indent=2))


if __name__ == "__main__":
    main()
