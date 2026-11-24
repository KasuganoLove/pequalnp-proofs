"""Run the 1922 monotone frontier with the certified projections used for L1667."""
from functools import cache
import sys
import json
from pathlib import Path
from time import monotonic
import argparse
import re

parser = argparse.ArgumentParser()
parser.add_argument("repo", type=Path, help="Root of the pequalnp-proofs checkout")
parser.add_argument("--marked", action="store_true", help="Exclude the 13 marked truth tables")
parser.add_argument("--theta-states", action="store_true", help="Also use regenerated projected state tables")
parser.add_argument("--theta-opt", action="store_true", help="Use only projected signal membership")
parser.add_argument("--theta-dir", type=Path, default=Path(__file__).resolve().parent)
args = parser.parse_args()
source = (args.repo / "lean/PEqualNP/Outside/L_meta_1667.lean").read_text(encoding="utf-8")
def declaration(name):
    return next(line for line in source.splitlines() if line.startswith("def " + name + " "))

positives = (3,6,12,17,24,33,66,132,160,264,288,320)
negatives = (42,50,69,104,116,138,201,208,261,276,385,402)
full = (1 << (len(positives)*len(negatives))) - 1
all512 = (1 << 512) - 1
raw = tuple(int(v, 16) for v in re.findall(r"0x([0-9a-f]+)", declaration("inputs")))
goal = int(declaration("graph").split(":= ")[1], 16)
assert len(raw) == 9
cols = []
for idx, entry in enumerate(re.findall(r"\((\d+),(\d+),(\d+),(\d+),(\d+)\)", declaration("deadcolumns"))):
    zeros, ones, _, _, lower = map(int, entry)
    domain = sum(1 << r for r in range(512) if r & zeros == 0 and r & ones == ones)
    cols.append((idx, domain, lower, {0, domain, *[wire & domain for wire in raw]}))
assert len(cols) == 126
seed = raw[0] | raw[4]
fast = args.marked
exclude = {raw[a] & raw[b] for a,b in ((0,1),(1,2),(2,3),(3,8),(5,8),(0,5))}
exclude |= {seed & raw[j] for j in (1,2,3,5,6,7,8)}
theta_domain = all512 ^ seed
theta_allowed = None
theta_states = None
if "--theta-opt" in sys.argv or "--theta-states" in sys.argv:
    certificate = args.theta_dir / "theta1922-optimal.json"
    projected_words = [int(word,16) & theta_domain for word in json.loads(certificate.read_text())]
    theta_allowed = {0, theta_domain}
    theta_allowed.update(projected_words)
    if "--theta-states" in sys.argv:
        theta_idx = {v:1<<i for i,v in enumerate(projected_words)}
        theta_states = json.loads(certificate.with_name("theta1922-states.json").read_text())


@cache
def separated(w):
    rejected = sum(1 << j for j, r in enumerate(negatives) if not (w >> r) & 1)
    return sum(rejected << (12 * j) for j, r in enumerate(positives) if (w >> r) & 1)


def extend(ws, bank, cap):
    if theta_states is not None:
        seen = {0,theta_domain,*[w & theta_domain for w in raw]}
        paid_theta = {w & theta_domain for w in bank} - seen
    projections = []
    for _, domain, lower, base in cols:
        known = set(base)
        paid = 0
        for v in bank[9:]:
            image = v & domain
            if image not in known:
                paid += 1
                known.add(image)
        constant = tuple((v & domain) in (0, domain) for v in ws)
        margin = lower + sum(constant) - (cap - 1) - paid
        if margin >= 0:
            projections.append((domain, known, constant, margin))
    for i, a in enumerate(ws):
        for j in range(i+1, len(ws)):
            b = ws[j]
            rest = tuple(w for k, w in enumerate(ws) if k not in (i,j))
            unseparated = full
            for w in rest:
                unseparated &= ~separated(w)
            for z in (a & b, a | b):
                if z in (0, all512) or z in ws or (fast and z in exclude):
                    continue
                if theta_allowed is not None and (z & theta_domain) not in theta_allowed:
                    continue
                if z == goal:
                    raise RuntimeError(("TARGET", cap, ws, a, b))
                uncovered = unseparated & ~separated(z)
                for da, db in ((True,True), (True,False), (False,True), (False,False)):
                    if len(ws)+1-da-db > cap:
                        continue
                    if uncovered & ~(0 if da else separated(a)) & ~(0 if db else separated(b)):
                        continue
                    cut = False
                    for dom, known, constant, margin in projections:
                        val = z & dom
                        if margin + (val in (0,dom)) - da*constant[i] - db*constant[j] > (val not in known):
                            cut = True
                            break
                    if not cut:
                        new = (*rest, z, *((a,) if not da else ()), *((b,) if not db else ()))
                        if theta_states is not None:
                            extra = (z & theta_domain) not in seen | paid_theta
                            slots = 11-len(paid_theta)-extra
                            live_mask=0
                            for w in new:
                                live_mask |= theta_idx.get(w & theta_domain,0)
                            if slots<0 or not any(v & live_mask == v for v in theta_states[str(slots)]):
                                continue
                        yield tuple(sorted(new)), (*bank, z)


if __name__ == "__main__":
    # The no-seed case is the separate raw lower bound of L1667.
    layer = {tuple(sorted((*raw, seed))): (*raw, seed)}
    started = monotonic()
    for cap in range(14, 0, -1):
        nxt = {}
        for i, (ws, bank) in enumerate(layer.items(), 1):
            for state, history in extend(ws, bank, cap):
                nxt.setdefault(state, history)
            if monotonic()-started > 240 or len(nxt) > 250000:
                print("BOUND", cap, i, len(layer), len(nxt), flush=True)
                raise SystemExit(2)
        print(cap, len(layer), len(nxt), round(monotonic()-started,2), flush=True)
        layer = nxt
        if not layer:
            break
