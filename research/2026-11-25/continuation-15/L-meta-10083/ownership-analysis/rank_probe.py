#!/usr/bin/env python3
"""Bounded ordinary-Python probe of PR13556's twin-deletion Rank.

This produces only explicit positive rank witnesses. Failure/timeout is not
a proof of nonexistence, and a rank witness is not a representing circuit.
"""
import argparse
import json
import time


def matrix(k):
    n = 3 * k
    rows = [0] * n
    for i in range(k):
        for a in (i, k + i):
            for b in ((i + 1) % k, 2 * k + i):
                rows[a] |= 1 << b
                rows[b] |= 1 << a
    return rows


def bits(mask):
    while mask:
        b = mask & -mask
        yield b.bit_length() - 1
        mask ^= b


def classes(rows, R, C):
    out = {}
    for a in bits(R):
        s = rows[a] & C
        out[s] = out.get(s, 0) | (1 << a)
    return sorted(out.values(), key=lambda v: -v.bit_count())


def bic(rows, R, C):
    sigs = set(rows[a] & C for a in bits(R))
    return all(not (a & b) for a in sigs for b in sigs if a != b)


def probe(k, budget, seconds):
    rows = matrix(k)
    full = (1 << len(rows)) - 1
    begin = time.monotonic()
    failed = set()
    calls = 0

    def go(R, C, r):
        nonlocal calls
        calls += 1
        if calls % 1024 == 0 and time.monotonic() - begin > seconds:
            raise TimeoutError
        if bic(rows, R, C):
            return []
        if r == 0:
            return None
        key = (min(R, C), max(R, C), r)
        if key in failed:
            return None
        xs, ys = classes(rows, R, C), classes(rows, C, R)
        choices = [(X, Y) for X in xs for Y in ys]
        choices.sort(key=lambda q: -(q[0].bit_count() + q[1].bit_count()))
        for X, Y in choices:
            sub = go(R & ~X, C & ~Y, r - 1)
            if sub is not None:
                return [(list(bits(X)), list(bits(Y)))] + sub
        failed.add(key)
        return None

    result = {"k": k, "round_budget": budget, "seconds_cap": seconds,
              "scope": "ordinary computation of Rank only; not a circuit"}
    try:
        witness = go(full, full, budget)
        result["status"] = "witness" if witness is not None else "exhausted"
        if witness is not None:
            R = C = full
            for X, Y in witness:
                assert len({rows[a] & C for a in X}) <= 1
                assert len({rows[b] & R for b in Y}) <= 1
                R &= ~sum(1 << a for a in X)
                C &= ~sum(1 << b for b in Y)
            assert bic(rows, R, C)
            result["rounds"] = witness
            result["remaining_rows"] = list(bits(R))
            result["remaining_columns"] = list(bits(C))
    except TimeoutError:
        result["status"] = "timeout"
    result["elapsed_seconds"] = time.monotonic() - begin
    result["calls"] = calls
    result["failed_states"] = len(failed)
    return result


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("k", type=int)
    p.add_argument("budget", type=int)
    p.add_argument("--seconds", type=float, default=20)
    args = p.parse_args()
    print(json.dumps(probe(args.k, args.budget, args.seconds), indent=2))
