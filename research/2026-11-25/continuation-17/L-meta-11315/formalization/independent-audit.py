"""Read-only exact-data/template audit; no Lean build and no recursive search."""
from pathlib import Path
from collections import Counter
import difflib
import hashlib
import itertools
import json
import re

HERE = Path(__file__).resolve().parent
TASK = HERE.parent
source_path = HERE / "L_meta_11315.literal.lean"
source = source_path.read_text()
reference = (TASK.parent / "L-meta-10696/status-audit/L_meta_9539.reference.lean").read_text()
gap = json.loads((TASK / "gap.json").read_text())
E = [(0, 3), (0, 4), (1, 4), (2, 4), (0, 5), (1, 5),
     (3, 5), (0, 6), (1, 6), (3, 6), (5, 6)]
def f(x):
    return any((x >> a & 1) and (x >> b & 1) for a, b in E)
positive = [x for x in range(128) if f(x)]
negative = [x for x in range(128) if not f(x)]
sample_pairs = list(itertools.product(positive, negative))
half = len(sample_pairs)
assert half == 2160
rows_text = source.split("def rows : List W :=", 1)[1].split("\nset_option", 1)[0]
rows = [int(x, 16) for x in re.findall(r"0x[0-9a-f]+", rows_text)]
assert len(rows) == 7 and len(set(rows)) == 7
assert all(x < 1 << (2 * half) for x in rows)
for k, (p, n) in enumerate(sample_pairs):
    for i, row in enumerate(rows):
        assert (row >> k & 1) == (p >> i & 1)
        assert (row >> (k + half) & 1) == (n >> i & 1)
for k in range(2 * half):
    assignment = sum((row >> k & 1) << i for i, row in enumerate(rows))
    assert f(assignment) == (k < half)  # F = complement(goal), not goal.

marker = "theorem PEqualNP.Outside.L_meta_11315 : "
exact_statement = source.split(marker, 1)[1].split(" := by", 1)[0]
assert exact_statement == gap["statement"]
f_line = re.search(r"^def F .* := (.*)$", source, re.M).group(1)
assert [(int(a), int(b)) for a, b in re.findall(r"x (\d+) && x (\d+)", f_line)] == E
wg_line = re.search(r"^def wg .* := (.*)$", source, re.M).group(1)
gates = [(op, int(a), int(b)) for op, a, b in re.findall(
    r"GateOp\.(and|or), \[(\d+), (\d+)\]", wg_line)]
assert len(gates) == 11
for x in range(128):
    wires = [bool(x >> i & 1) for i in range(7)]
    for op, a, b in gates:
        assert a < len(wires) and b < len(wires)
        wires.append(wires[a] and wires[b] if op == "and" else wires[a] or wires[b])
    assert wires[17] == f(x)

def normalize(s):
    s = s.replace("import Mathlib.Tactic\n", "import Mathlib\n")
    s = s.replace("L_meta_11315", "L_meta_9539")
    s = re.sub(r"\b4320\b", "1400", s)
    s = re.sub(r"\b2160\b", "700", s)
    s = s.replace("Fin 7", "Fin 6").replace("inputs.length = 7", "inputs.length = 6")
    s = s.replace("search 9", "search 7").replace("9 < binaryCost", "7 < binaryCost")
    s = s.replace("search_complete ht 9", "search_complete ht 7")
    s = re.sub(r"^def F .*", "def F DATA", s, flags=re.M)
    s = re.sub(r"def rows : List W :=.*?(?=\nset_option)", "def rows DATA\n", s, flags=re.S)
    s = re.sub(r"^def wg .*", "def wg DATA", s, flags=re.M)
    for prefix in ["theorem bridge :", "theorem weval :", "theorem PEqualNP.Outside.L_meta_9539 :"]:
        start = s.index(prefix)
        end = s.index(" := by", start)
        s = s[:start] + prefix + " DATA" + s[end:]
    s = re.sub(r"rcases hg with rfl(?: \| rfl)+", "rcases hg with DATA", s)
    s = s.replace("L_meta_9539.wg, 17", "L_meta_9539.wg, 14")
    s = s.replace("wg.length = 11", "wg.length = 9")
    # Comments carry attribution; compare executable source independently.
    return "\n".join(line for line in s.splitlines()
                     if line.strip() and not line.lstrip().startswith("--"))
normalized_old = normalize(reference)
normalized_new = normalize(source)
diff = "\n".join(difflib.unified_diff(normalized_old.splitlines(), normalized_new.splitlines(),
                                    fromfile="checked9539-normalized", tofile="candidate11315-normalized"))
(HERE / "independent-generic.diff").write_text(diff + ("\n" if diff else ""))

# Independently enumerate exactly the first dispatch layer, in source order.
full = (1 << 128) - 1
pos_mask = sum(1 << x for x in positive)
raw = [sum((x >> i & 1) << x for x in range(128)) for i in range(7)]
def separates(ws):
    return all(not _matching(ws, q) for q in negative)
def _matching(ws, q):
    m = pos_mask
    for w in ws:
        m &= w if w >> q & 1 else full ^ w
    return m
low_mask = (1 << half) - 1
packed_full = (1 << (2 * half)) - 1
def packed_cuts(ws):
    c = 0
    for w in ws:
        c |= ((w >> half) ^ w) & low_mask
    return c == low_mask
initial = [m for m in range(128) if separates([raw[i] for i in range(7) if m >> i & 1])]
assert initial == [127]
children = []
for i, j in itertools.combinations(range(7), 2):
    rest = [k for k in range(7) if k not in (i, j)]
    a, b = raw[i], raw[j]
    pa, pb = rows[i], rows[j]
    values = [a & b, a | b, a & (full ^ b), b & (full ^ a)]
    packed = [pa & pb, pa | pb, pa & (packed_full ^ pb), pb & (packed_full ^ pa)]
    for op, (w, pw) in enumerate(zip(values, packed)):
        for keep in range(4):
            kept = ([i] if keep & 1 else []) + ([j] if keep & 2 else [])
            ws = [w] + [raw[k] for k in kept + rest]
            pws = [pw] + [rows[k] for k in kept + rest]
            passed = separates(ws)
            assert passed == packed_cuts(pws)
            if passed:
                children.append({"index": len(children), "pair": [i, j], "op": op,
                                 "keep_mask": keep, "extra": 3 - len(kept),
                                 "next_budget": 8, "retained_raw_order": kept + rest,
                                 "frontier_raw_signatures": [hex(v) for v in ws]})
assert len(children) == 92
(HERE / "independent-first-level.json").write_text(json.dumps(children, indent=2) + "\n")
result = {
    "source_sha256": hashlib.sha256(source.encode()).hexdigest(),
    "statement_exact": True,
    "statement_sha256": hashlib.sha256(exact_statement.encode()).hexdigest(),
    "positive_assignments": len(positive), "negative_assignments": len(negative),
    "sample_pairs": half, "sample_bits": 2 * half, "raw_columns": len(rows),
    "all_packed_bits_and_labels_match": True,
    "polarity": "positive lower half, negative upper half; F is complement(goal)",
    "witness_gates": len(gates), "witness_output": 17,
    "witness_all_128_assignments_match": True,
    "normalized_generic_source_identical": not diff,
    "initial_separating_raw_sublists": initial,
    "first_level_children": len(children),
    "first_level_keep_mask_counts": dict(Counter(c["keep_mask"] for c in children)),
    "all_first_level_raw_and_paired_guards_match": True,
    "recursive_search_run": False, "lean_run": False,
}
(HERE / "independent-audit.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
