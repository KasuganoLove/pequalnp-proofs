"""Build the eight candidate tables used by CheckForest1673.lean for L-meta-1673."""

import argparse
from functools import reduce
import operator
from pathlib import Path
import re
import time


ALL_ROWS = (1 << 512) - 1
ALL_PAIRS = (1 << 768) - 1
EXPECTED_COUNTS = (1, 80, 2664, 32704, 73709, 34621, 1862, 2)


class Search:
    def __init__(self, checkout):
        path = checkout / "lean/PEqualNP/Outside/L_meta_1667.lean"
        source = path.read_text(encoding="utf8").splitlines()

        def definition(name):
            return next(line for line in source if line.startswith(f"def {name} "))

        def hex_words(text):
            return [int(x, 16) for x in re.findall(r"0x([0-9a-f]+)", text)]

        self.raw = tuple(hex_words(definition("inputs")))
        self.goal, = hex_words(definition("graph"))
        samples = hex_words(definition("deadsamples"))
        assert len(self.raw) == 9 and len(samples) == 18
        self.sample = dict(zip(self.raw, zip(samples[::2], samples[1::2])))
        self.seed = self.operate(1, self.raw[0], self.raw[1])

        self.columns = []
        pattern = r"\((\d+),(\d+),(\d+),(\d+),(\d+)\)"
        for ci, fields in enumerate(re.findall(pattern, definition("deadcolumns"))):
            zeros, ones, _, _, lower = map(int, fields)
            domain = sum(1 << row for row in range(512)
                         if row & zeros == 0 and row & ones == ones)
            projected = {0, domain, *(w & domain for w in self.raw)}
            self.columns.append((ci, domain, lower, projected))
        assert len(self.columns) == 126

    @staticmethod
    def value(code, a, b, mask):
        if code == 0:
            return a & b
        if code == 1:
            return a | b
        return a ^ mask

    def operate(self, code, a, b):
        value = self.value(code, a, b, ALL_ROWS)
        if value not in self.sample:
            pa, qa = self.sample[a]
            pb, qb = self.sample[b]
            self.sample[value] = (self.value(code, pa, pb, ALL_PAIRS),
                                  self.value(code, qa, qb, ALL_PAIRS))
        return value

    def projected_pools(self, wires, history, bank, cap):
        pools = []
        for ci, domain, lower, raw in self.columns:
            available = set(raw)
            paid = 0
            for step in range(len(history)):
                value = bank[9 + step] & domain
                if value not in available:
                    paid |= 1 << step
                    available.add(value)
            constant = tuple(w & domain in (0, domain) for w in wires)
            margin = lower + sum(constant) - (cap - 1) - paid.bit_count()
            if margin >= 0:
                pools.append((ci, domain, paid, available, margin, constant))
        return pools

    def next_layer(self, frontier, cap, table):
        children = {}
        for wires, (history, bank) in frontier.items():
            pools = self.projected_pools(wires, history, bank, cap)
            indices = [bank.index(w) for w in wires]
            rules = set()
            coverage = {}

            for i, a in enumerate(wires):
                for j in range(i, len(wires)):
                    unary = i == j
                    operations = (2,) if unary else (0, 1)
                    drops = ((1, 0), (0, 0)) if unary else (
                        (1, 1), (1, 0), (0, 1), (0, 0))
                    for code in operations:
                        value = self.operate(code, a, wires[j])
                        if value in (0, ALL_ROWS) or value in wires:
                            continue
                        positive, negative = self.sample[value]
                        for da, db in drops:
                            count = len(wires) + 1 - da - db
                            if count > cap:
                                continue
                            oriented = count == cap
                            removed = (i if da else -1, j if db else -1)
                            key = (*removed, oriented)
                            if key not in coverage:
                                columns = (self.sample[w] for t, w in enumerate(wires)
                                           if t not in removed)
                                coverage[key] = reduce(operator.or_, (
                                    (p & ~q) if oriented else (p ^ q) for p, q in columns), 0)
                            new_column = positive & ~negative if oriented else positive ^ negative
                            if coverage[key] | new_column != ALL_PAIRS:
                                continue

                            for ci, dom, paid, available, margin, constant in pools:
                                v = value & dom
                                bound = margin + (v in (0, dom)) - da * constant[i] - db * constant[j]
                                if bound > (v not in available):
                                    rules.add((ci, paid))
                                    break
                            else:
                                child = tuple(sorted([value] + [w for t, w in enumerate(wires)
                                                                if t not in removed]))
                                if self.goal in child:
                                    raise RuntimeError(f"Target found with cap {cap}, history {history}")
                                if child not in children:
                                    instruction = (code, indices[i], indices[j])
                                    children[child] = (history + (instruction,), bank + (value,))

            operations = sum((a | (b << 4) | (code << 8)) << (10 * i)
                             for i, (code, a, b) in enumerate(history))
            live_mask = sum(1 << bank.index(w) for w in wires)
            numbers = [operations, live_mask, *(ci | (paid << 7) for ci, paid in sorted(rules))]
            table.write(" ".join(map(str, numbers)) + "\n")
        return children

    def run(self, out):
        out.mkdir(parents=True, exist_ok=True)
        bank = self.raw + (self.seed,)
        frontier = {tuple(sorted(bank)): (((1, 0, 1),), bank)}
        for cap, expected in zip(range(14, 6, -1), EXPECTED_COUNTS):
            size = len(frontier)
            if size != expected:
                raise RuntimeError(f"Cap {cap}: expected {expected} states, got {size}")
            start = time.monotonic()
            with (out / f"native1673-{cap}.txt").open("w", encoding="ascii", newline="\n") as f:
                frontier = self.next_layer(frontier, cap, f)
            print(f"cap {cap}: {size} states, {len(frontier)} children, "
                  f"{time.monotonic()-start:.1f} s", flush=True)
        if frontier:
            raise RuntimeError("Unresolved states remain")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkout", type=Path, help="pequalnp-proofs repository root")
    parser.add_argument("out", type=Path, help="destination for the eight generated tables")
    args = parser.parse_args()
    Search(args.checkout).run(args.out)
