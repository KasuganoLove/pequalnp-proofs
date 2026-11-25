from pathlib import Path
import datetime
import hashlib
import json
import resource
import subprocess
import time

P = Path(__file__).resolve().parent
baseline = json.loads((P / "baseline.json").read_text())
for x in range(128):
    wires = [bool(x >> i & 1) for i in range(7)]
    for op, a, b in baseline["gates"]:
        assert a < len(wires) and b < len(wires)
        assert op in ("and", "or")
        wires.append(wires[a] and wires[b] if op == "and" else wires[a] or wires[b])
    expected = any((x >> a & 1) and (x >> b & 1) for a, b in baseline["edges"])
    assert wires[baseline["output"]] == expected
assert len(baseline["gates"]) == 11
def limits():
    resource.setrlimit(resource.RLIMIT_AS, (1024**3, 1024**3))
started = datetime.datetime.now(datetime.timezone.utc).isoformat()
before = time.monotonic()
with (P / "literal-result.json").open("w") as out, (P / "literal-progress.log").open("w") as err:
    process = subprocess.Popen([str(P / "literal-probe")], stdout=out, stderr=err,
                               preexec_fn=limits)
    try:
        code = process.wait(timeout=65)
    except subprocess.TimeoutExpired:
        process.kill()
        code = process.wait()
record = {
    "task": "L-meta-11315",
    "start_utc": started,
    "end_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "elapsed_wall_seconds": time.monotonic() - before,
    "exit_code": code,
    "address_space_limit_bytes": 1024**3,
    "source_sha256": hashlib.sha256((P / "literal-probe.cpp").read_bytes()).hexdigest(),
    "baseline_sha256": hashlib.sha256((P / "baseline.json").read_bytes()).hexdigest(),
    "baseline_assignments_verified": 128,
    "binary_budget": 9,
    "free_NOTs": "unbounded",
    "formal_certificate": False,
}
(P / "run.json").write_text(json.dumps(record, indent=2) + "\n")
print(json.dumps(record), flush=True)
