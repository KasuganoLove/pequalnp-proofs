from pathlib import Path
import datetime
import hashlib
import json
import resource
import subprocess
import sys
import time

P = Path(__file__).resolve().parent
mode = sys.argv[1]
assert mode in ("edges_all", "edges_maximal")
problem = json.loads((P / f"{mode}-problem.json").read_text())
def limits():
    resource.setrlimit(resource.RLIMIT_AS, (1024**3, 1024**3))
start = datetime.datetime.now(datetime.timezone.utc).isoformat()
before = time.monotonic()
with (P / f"{mode}-result.json").open("w") as out, (P / f"{mode}-progress.log").open("w") as err:
    child = subprocess.Popen([str(P / "probe"), mode], stdout=out, stderr=err,
                             preexec_fn=limits)
    try:
        code = child.wait(timeout=65)
    except subprocess.TimeoutExpired:
        child.kill()
        code = child.wait()
record = {"task": "L-meta-11315", "mode": mode, "start_utc": start,
          "end_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
          "wall_seconds": time.monotonic() - before, "exit_code": code,
          "address_space_limit_bytes": 1024**3,
          "source_sha256": hashlib.sha256((P / "probe.cpp").read_bytes()).hexdigest(),
          "problem_sha256": hashlib.sha256((P / f"{mode}-problem.json").read_bytes()).hexdigest(),
          "formal_certificate": False}
if code == 0:
    result = json.loads((P / f"{mode}-result.json").read_text())
    assert result["all_separating_initial_sublists"] == problem["all_separating_initial_sublists"]
    record["outcome"] = result["outcome"]
    if result["outcome"] == "FOUND":
        # Reconstruct one concrete ordinary circuit from the sampled signal path.
        samples = problem["positive_samples"] + problem["negative_samples"]
        sample_mask = problem["domain_mask"]
        wires = list(problem["raw_signatures"])
        available = {s: i for i, s in enumerate(wires)}
        gates = []
        not_cache = {}
        def add(op, a, b=None):
            if op == "not":
                z = sample_mask ^ wires[a]
                inputs = [a]
            elif op == "and":
                z = wires[a] & wires[b]
                inputs = [a, b]
            else:
                z = wires[a] | wires[b]
                inputs = [a, b]
            gates.append({"op": op, "inputs": inputs})
            wires.append(z)
            available[z] = len(wires) - 1
            return len(wires) - 1
        def neg(a):
            if a not in not_cache:
                not_cache[a] = add("not", a)
            return not_cache[a]
        for step in result["steps"]:
            a, b, op = available[step["a"]], available[step["b"]], step["op"]
            out = add("and", a, b) if op == 0 else add("or", a, b) if op == 1 else (
                add("and", a, neg(b)) if op == 2 else add("and", b, neg(a)))
            assert wires[out] == step["z"]
        output = available[result["found_output"]]
        if wires[output] != problem["positive_mask"]:
            output = neg(output)
        assert wires[output] == problem["positive_mask"]
        mismatches = []
        for x in range(128):
            w = [bool(x >> i & 1) for i in range(7)]
            for gate in gates:
                a = gate["inputs"][0]
                w.append(not w[a] if gate["op"] == "not" else (
                    w[a] and w[gate["inputs"][1]] if gate["op"] == "and" else
                    w[a] or w[gate["inputs"][1]]))
            target = any((x >> a & 1) and (x >> b & 1) for a, b in problem["edges"])
            if w[output] != target:
                mismatches.append(x)
        assert not set(mismatches).intersection(samples)
        model = {"gates": gates, "output": output, "total_gate_count": len(gates),
                 "binary_count": sum(g["op"] != "not" for g in gates),
                 "NOT_count": sum(g["op"] == "not" for g in gates),
                 "sample_mismatches": [], "full_128_mismatches": mismatches,
                 "full_target_correct": not mismatches,
                 "public_task_counterexample_claimed": False}
        (P / f"{mode}-model.json").write_text(json.dumps(model, indent=2) + "\n")
(P / f"{mode}-run.json").write_text(json.dumps(record, indent=2) + "\n")
print(json.dumps(record), flush=True)
