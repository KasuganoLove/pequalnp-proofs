from pathlib import Path
import datetime
import hashlib
import json
import resource
import subprocess
import sys
import time

P = Path(__file__).resolve().parent
mode = sys.argv[1] if len(sys.argv) > 1 else "optimized"
assert mode in ("optimized", "literal")
executable = P / ("probe" if mode == "optimized" else "literal-probe")
source = executable.with_suffix(".cpp")
command = [str(executable)] + (["10487", "10", "60"] if mode == "optimized" else [])
def limits():
    resource.setrlimit(resource.RLIMIT_AS, (1024**3, 1024**3))
started = datetime.datetime.now(datetime.timezone.utc).isoformat()
before = time.monotonic()
with (P / f"{mode}-result.json").open("w") as out, (P / f"{mode}-stderr.log").open("w") as err:
    process = subprocess.Popen(command, stdout=out, stderr=err, preexec_fn=limits)
    try:
        code = process.wait(timeout=65)
    except subprocess.TimeoutExpired:
        process.kill()
        code = process.wait()
record = {
    "mode": mode,
    "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
    "problem_sha256": hashlib.sha256((P / "problem.json").read_bytes()).hexdigest(),
    "start_utc": started,
    "end_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "elapsed_wall_seconds": time.monotonic() - before,
    "exit_code": code,
    "maximum_resident_set_size_kib": resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
    "address_space_limit_bytes": 1024**3,
    "task": "L-meta-10487",
    "binary_budget": 10,
    "free_NOTs": "unbounded",
    "sample_domain_only": True,
    "formal_certificate": False,
}
(P / f"{mode}-run.json").write_text(json.dumps(record, indent=2) + "\n")
print(json.dumps(record), flush=True)
