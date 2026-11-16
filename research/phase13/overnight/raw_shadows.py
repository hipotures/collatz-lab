#!/usr/bin/env python3
"""Bounded raw-shadow matrix computation; no height scan or project imports.

Exact results are append-only. A matrix checkpoint is saved before each gcd,
so an interrupted level can resume. Only the last completed level number is
kept after success; full raw coordinates are never published.
"""

import argparse
import hashlib
import json
from math import gcd
from pathlib import Path
import signal
import tempfile
import time


ROOT = Path(__file__).resolve().parent
TARGET = ROOT / "raw-shadows.jsonl"
CHECKPOINT = ROOT / "raw-shadow-checkpoint.json"
MAX_LEVEL = 8
MAX_EVIDENCE_BYTES = 65536
MAX_CHECKPOINT_BYTES = 8 * 1024 * 1024
FORMAT = "phase13-overnight-raw-shadow-v1"


def multiply(left, right):
    return tuple(tuple(sum(left[i][j] * right[j][k] for j in range(2))
                       for k in range(2)) for i in range(2))


def product(matrices):
    out = ((1, 0), (0, 1))
    for matrix in matrices:
        out = multiply(out, matrix)
    return out


def advance(zero, one):
    # Both products use the OLD pair. Order is the literal substitution order.
    return (product([one] * 5 + [zero]),
            product([one, zero, zero, one, one, one]))


def digest(value):
    value = abs(value)
    return hashlib.sha256(value.to_bytes((value.bit_length() + 7) // 8, "big")).hexdigest()


def coordinates(zero, one):
    preperiod = product([one, zero, zero])
    m, negative_d, b = one[0][0], one[0][1], one[1][1]
    u, negative_c, a = preperiod[0][0], preperiod[0][1], preperiod[1][1]
    return u * negative_d + negative_c * (b - m), a * (b - m)


def record(k, zero, one):
    s = 6 ** k
    for matrix in (zero, one):
        assert matrix[0][0] == 1 << s and matrix[1][0] == 0
        assert matrix[0][1] <= 0 and matrix[1][1] > 0 and matrix[1][1] % 2
    p, q = coordinates(zero, one)
    assert p < 0 < q and q % 2 == 1
    common = gcd(p, q)
    reduced_p, reduced_q = p // common, q // common
    height = max(abs(reduced_p), reduced_q)
    ell = (56 * s - 1) // 5
    assert 2 * height * height < 1 << ell
    return {"format": FORMAT, "k": k, "S": s, "L": ell,
            "raw_gcd": hex(common), "numerator_sign": -1,
            "denominator_sign": 1, "denominator_odd": True,
            "raw_numerator_bits": abs(p).bit_length(),
            "raw_denominator_bits": q.bit_length(),
            "reduced_numerator_bits": abs(reduced_p).bit_length(),
            "reduced_denominator_bits": reduced_q.bit_length(),
            "reduced_height_bits": height.bit_length(),
            "raw_numerator_abs_sha256": digest(p),
            "raw_denominator_sha256": digest(q),
            "reduced_numerator_abs_sha256": digest(reduced_p),
            "reduced_denominator_sha256": digest(reduced_q),
            "strict_uniqueness": True}


def inherited_control(row, inherited):
    if row["k"] < len(inherited):
        old = inherited[row["k"]]
        assert int(row["raw_gcd"], 16) == old["raw_gcd"]
        for key in ("k", "S", "L", "raw_numerator_abs_sha256",
                    "raw_denominator_sha256", "reduced_height_bits", "strict_uniqueness"):
            assert row[key] == old[key], f"inherited control differs: {key}"


def atomic_bytes(path, content, limit):
    assert len(content) <= limit, "bounded output cap exceeded"
    with tempfile.NamedTemporaryFile(dir=ROOT, prefix="raw-shadow-", suffix=".tmp",
                                     delete=False) as stream:
        temporary = Path(stream.name)
        stream.write(content)
    temporary.replace(path)


def save_checkpoint(k, zero, one):
    state = {"format": "phase13-raw-shadow-checkpoint-v1", "stage": "matrix-ready",
             "k": k, "matrices": [[[hex(x) for x in row] for row in matrix]
                                      for matrix in (zero, one)]}
    atomic_bytes(CHECKPOINT, (json.dumps(state, separators=(",", ":")) + "\n").encode(),
                 MAX_CHECKPOINT_BYTES)


def load_checkpoint(saved_count):
    assert CHECKPOINT.stat().st_size <= MAX_CHECKPOINT_BYTES
    checkpoint = json.loads(CHECKPOINT.read_bytes())
    assert checkpoint["format"] == "phase13-raw-shadow-checkpoint-v1"
    assert checkpoint["stage"] == "matrix-ready", "completed evidence needs no resume"
    k = checkpoint["k"]
    assert type(k) is int and 0 <= k <= MAX_LEVEL
    assert k in (saved_count - 1, saved_count), "checkpoint/evidence sequence differs"
    matrices = checkpoint["matrices"]
    assert len(matrices) == 2
    out = []
    for matrix in matrices:
        assert len(matrix) == 2 and all(len(row) == 2 for row in matrix)
        parsed = []
        for row in matrix:
            values = []
            for x in row:
                assert isinstance(x, str) and len(x) <= 2 * 6 ** MAX_LEVEL
                value = int(x, 16)
                assert hex(value) == x
                values.append(value)
            parsed.append(tuple(values))
        out.append(tuple(parsed))
    return k, *out


def expired(_signum, _frame):
    raise TimeoutError("raw-shadow level exceeded its budget; saved matrices/records survive")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--through-level", type=int, default=8)
    parser.add_argument("--seconds-per-level", type=int, default=180)
    parser.add_argument("--write", action="store_true", required=True)
    args = parser.parse_args()
    if not 0 <= args.through_level <= MAX_LEVEL or not 1 <= args.seconds_per_level <= 240:
        parser.error("through-level must be in 0..8; seconds-per-level in 1..240")
    previous = TARGET.read_bytes() if TARGET.exists() else b""
    assert len(previous) <= MAX_EVIDENCE_BYTES
    assert not previous or previous.endswith(b"\n")
    saved = [json.loads(line) for line in previous.splitlines()]
    assert [r["k"] for r in saved] == list(range(len(saved)))
    inherited = json.loads((ROOT.parent / "modular.json").read_bytes())["integer_levels"]
    for row in saved:
        inherited_control(row, inherited)
    if len(saved) > args.through_level:
        print("SKIP: requested levels already recorded; run the separate checker", flush=True)
        return
    signal.signal(signal.SIGALRM, expired)
    signal.alarm(args.seconds_per_level)
    if CHECKPOINT.exists():
        current, zero, one = load_checkpoint(len(saved))
    else:
        assert not saved, "missing resumable matrix state"
        current, zero, one = 0, ((2, 0), (0, 1)), ((2, -1), (0, 3))
    for k in range(len(saved), args.through_level + 1):
        signal.alarm(args.seconds_per_level)
        started = time.perf_counter()
        print(f"START k={k} seconds_budget={args.seconds_per_level}", flush=True)
        if current == k - 1:
            zero, one = advance(zero, one)
            current = k
        assert current == k
        save_checkpoint(k, zero, one)
        print(f"MATRICES k={k} elapsed_seconds={time.perf_counter() - started:.3f}", flush=True)
        row = record(k, zero, one)
        inherited_control(row, inherited)
        line = (json.dumps(row, sort_keys=True, separators=(",", ":")) + "\n").encode()
        previous += line
        atomic_bytes(TARGET, previous, MAX_EVIDENCE_BYTES)
        signal.alarm(0)
        print(f"COMPUTED k={k} gcd={row['raw_gcd']} "
              f"raw_bits={row['raw_numerator_bits']},{row['raw_denominator_bits']} "
              f"reduced_height_bits={row['reduced_height_bits']} "
              f"elapsed_seconds={time.perf_counter() - started:.3f}", flush=True)
    # Below the cap retain matrices for extending this bounded experiment.
    if args.through_level == MAX_LEVEL:
        done = {"format": "phase13-raw-shadow-checkpoint-v1", "stage": "complete",
                "through_level": args.through_level,
                "evidence_sha256": hashlib.sha256(previous).hexdigest()}
        atomic_bytes(CHECKPOINT, (json.dumps(done, indent=2) + "\n").encode(), MAX_CHECKPOINT_BYTES)
    print("PASS: exact computation complete; independent replay remains required", flush=True)


if __name__ == "__main__":
    main()
