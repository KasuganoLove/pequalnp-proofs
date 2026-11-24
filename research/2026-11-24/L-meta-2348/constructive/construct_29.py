import json
from pathlib import Path

N = 14

def fano_incidence(p, l):
    return p == l or p == (l + 1) % 7 or p == (l + 3) % 7

def build():
    gates = []
    def gate(op, a, b):
        assert a != b and 0 <= a < N + len(gates) and 0 <= b < N + len(gates)
        gates.append({"op": op, "inputs": [a, b]})
        return N + len(gates) - 1
    stars = []
    for point in range(7):
        lines = [7 + line for line in range(7) if fano_incidence(point, line)]
        a = gate("or", lines[0], lines[1])
        b = gate("or", a, lines[2])
        stars.append(gate("and", point, b))
    output = stars[0]
    for star in stars[1:]:
        output = gate("or", output, star)
    original_output = output
    original_gates = list(gates)
    redundant = gate("or", original_output, stars[0])
    output = gate("and", original_output, redundant)
    return original_gates, original_output, gates, output

def evaluate(gates, output, x):
    wires = list(x)
    for gate in gates:
        a, b = gate["inputs"]
        wires.append(wires[a] and wires[b] if gate["op"] == "and" else wires[a] or wires[b])
    return wires[output]

def derivative(gates, output, base, differentiated):
    values = [i == base for i in range(N)]
    deriv = [i == differentiated for i in range(N)]
    for gate in gates:
        a, b = gate["inputs"]
        if gate["op"] == "and":
            d = (values[a] and deriv[b]) or (deriv[a] and values[b])
            value = values[a] and values[b]
        else:
            d = deriv[a] or deriv[b]
            value = values[a] or values[b]
        values.append(value)
        deriv.append(d)
    return values[output], deriv[output], deriv

def main():
    original, original_output, gates, output = build()
    assert len(original) == 27 and len(gates) == 29
    assert gates[0]["op"] == "or"
    for j, gate in enumerate(gates):
        assert gate["op"] in ("and", "or")
        a, b = gate["inputs"]
        assert a != b and a < N + j and b < N + j
    for bits in range(1 << N):
        x = [bool((bits >> i) & 1) for i in range(N)]
        target = any(fano_incidence(p, l) and x[p] and x[7 + l] for p in range(7) for l in range(7))
        assert evaluate(original, original_output, x) == target
        assert evaluate(gates, output, x) == target
    derivatives = []
    for p in range(7):
        for l in range(7):
            if fano_incidence(p, l):
                a = derivative(gates, output, p, 7 + l)
                b = derivative(gates, output, 7 + l, p)
                assert a[:2] == (False, False) and b[:2] == (False, False)
                derivatives.append({"point": p, "line": l, "directions": [a[1], b[1]]})
    record = {
        "input_count": N,
        "original_gate_count": len(original),
        "original_output": original_output,
        "original_edge_0_0_derivatives": [derivative(original, original_output, 0, 7)[1], derivative(original, original_output, 7, 0)[1]],
        "gate_count": len(gates),
        "output": output,
        "gates": gates,
        "all_16384_inputs_match_fano": True,
        "distinct_earlier_binary_operands": True,
        "first_gate_or": True,
        "all_incidence_derivatives": derivatives,
        "edge_0_0_derivative_witnesses": [derivative(gates, output, 0, 7)[2], derivative(gates, output, 7, 0)[2]],
        "limitation": "Exceeds the leased statement's bound by 2 gates; not a counterexample to L-meta-2348 and not a Lean proof."
    }
    Path(__file__).with_name("fano_double_reread_29.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps({k:record[k] for k in ("original_gate_count","original_output","original_edge_0_0_derivatives","gate_count","output","all_16384_inputs_match_fano","distinct_earlier_binary_operands","first_gate_or","limitation")},indent=2))
    print("all", len(derivatives), "incidences have both derivatives false")

if __name__ == "__main__":
    main()
