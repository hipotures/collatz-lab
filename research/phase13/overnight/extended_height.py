#!/usr/bin/env python3
"""Sparse exact height experiments, separate from the capped Phase 13 engines.

The odd-coset optimizer uses integer discrepancies and skips stretches where
the current odd vector survives. Its output is only a candidate until the
independent verifier accepts a witness and a zero box-count certificate.
Large integers use canonical hexadecimal strings, avoiding decimal limits.
"""

import argparse
import hashlib
import json
from pathlib import Path
import signal
import tempfile
import time


ROOT = Path(__file__).resolve().parent
TARGET = ROOT / "heights.jsonl"
MAX_BITS = 600000
MAX_FILE_BYTES = 8 * 1024 * 1024
MAX_COEFFICIENT_BOUND = 4095
FORMAT = "phase13-overnight-height-v1"
IMAGES = ((1, 1, 1, 1, 1, 0), (1, 0, 0, 1, 1, 1))


def frontier_prefix(length):
    """Indexed substitution automaton, independently checked by literal words."""
    out = bytearray(length)
    for j in range(length):
        digits, index = [], j
        while index:
            index, digit = divmod(index, 6)
            digits.append(digit)
        bit = 1
        for digit in reversed(digits):
            bit = IMAGES[bit][digit]
        out[j] = bit
    return out


def residue(bits):
    """Forward affine offsets, composed in a balanced tree."""
    def block(lo, hi):
        if hi - lo <= 64:
            offset, three = 0, 1
            for j in range(lo, hi):
                if bits[j]:
                    offset = 3 * offset + (1 << (j - lo))
                    three *= 3
            return offset, three
        mid = (lo + hi) // 2
        left_c, left_a = block(lo, mid)
        right_c, right_a = block(mid, hi)
        return left_c * right_a + (right_c << (mid - lo)), left_a * right_a

    c, a = block(0, len(bits))
    modulus = 1 << len(bits)
    return -c * pow(a, -1, modulus) % modulus


def norm(v):
    return max(abs(v[0]), abs(v[1]))


def odd_translate(u, v):
    # A convex piecewise linear norm changes slope only at these four roots.
    choices = {-1, 1}
    for top, bottom in ((-u[0], v[0]), (-u[1], v[1]),
                        (u[1] - u[0], v[0] - v[1]),
                        (-u[1] - u[0], v[0] + v[1])):
        if bottom:
            k = top // bottom
            below = k if k & 1 else k - 1
            choices.update((below, below + 2))
    d = min(choices, key=lambda t: (norm((u[0] + t * v[0], u[1] + t * v[1])),
                                    abs(t), t))
    return (u[0] + d * v[0], u[1] + d * v[1]), d


def candidates(a, bits, samples):
    """Yield only requested N, maintaining discrepancies (a*q-p)/2^N.

    At N=0, f=(1,0), g=(0,1). f is outside the next cylinder and has
    odd discrepancy. An even g discrepancy allows a hold: double f and
    halve g's discrepancy. Otherwise the usual adaptive odd-coset update
    makes the new g discrepancy even before division by two. No a*q
    multiplication is needed at each bit. Hold runs are skipped exactly.
    Minimality is established by a separate certificate, not this invariant.
    """
    if not 0 <= bits <= MAX_BITS or not 0 <= a < 1 << bits:
        raise ValueError("invalid bit length or residue")
    samples = sorted(set(samples))
    if not samples or samples[0] < 0 or samples[-1] > bits:
        raise ValueError("invalid sparse samples")
    n, f, g, df, dg, updates = 0, (1, 0), (0, 1), -1, a, 0
    for target in samples:
        while n < target:
            if not dg & 1:
                count = min((dg & -dg).bit_length() - 1, target - n) if dg else target - n
                f = f[0] << count, f[1] << count
                dg >>= count
                n += count
                continue
            if norm(g) < norm(f):
                new_g, d = odd_translate(f, g)
                df, dg = dg, (df + d * dg) // 2
                f, g = (2 * g[0], 2 * g[1]), new_g
            else:
                new_g, d = odd_translate(g, f)
                dg = (dg + d * df) // 2
                f, g = (2 * f[0], 2 * f[1]), new_g
            n += 1
            updates += 1
        p, q = g if g[1] > 0 else (-g[0], -g[1])
        yield {"N": n, "A": a % (1 << n), "H": norm(g), "p": p, "q": q,
               "basis": [list(f), list(g)], "nonhold_updates": updates}


def floor_trace(n, m, a, b):
    trace, total = [], 0
    while True:
        qa, a = divmod(a, m)
        qb, b = divmod(b, m)
        trace.extend((hex(qa), hex(qb)))
        total += qa * n * (n - 1) // 2 + qb * n
        top = a * n + b
        if top < m:
            return trace, total
        n, b = divmod(top, m)
        m, a = a, m


class BasisLimitError(ValueError):
    """The compact certificate would require too many coefficient checks."""


def basis_certificate(basis, n, bound):
    """Exclude the symmetric odd-denominator box using exact alpha intervals.

    The independent checker validates lattice membership, determinant, parity,
    the exhaustive beta bound, and endpoint inequalities. Nothing here relies
    on the optimizer's shortest-vector invariant.
    """
    f, g = basis
    coefficient_bound = bound * (abs(f[0]) + abs(f[1])) // (1 << n)
    if coefficient_bound > MAX_COEFFICIENT_BOUND:
        raise BasisLimitError("compact coefficient enumeration exceeds 4095")
    intervals = []
    for beta in range(1, coefficient_bound + 1, 2):
        row, lower, upper, outside = [], None, None, False
        for fi, gi in zip(f, g):
            if fi == 0:
                row.append(None)
                outside |= abs(beta * gi) > bound
                continue
            ends = (-bound - beta * gi, bound - beta * gi)
            if fi < 0:
                ends = (-ends[1], -ends[0])
            divisor = abs(fi)
            lo, hi = -((-ends[0]) // divisor), ends[1] // divisor
            row.append([hex(lo), hex(hi)])
            lower = lo if lower is None else max(lower, lo)
            upper = hi if upper is None else min(upper, hi)
        if not outside and (lower is None or lower <= upper):
            raise ValueError("odd-denominator box is nonempty")
        intervals.append(row)
    return {"type": "odd-box-basis-interval-v1", "bound": hex(bound),
            "coefficient_bound": hex(coefficient_bound), "intervals": intervals}


def certify(candidate, bits, method="auto"):
    n, a, h = (candidate[k] for k in ("N", "A", "H"))
    bound, modulus = h - 1, 1 << n
    if method not in ("auto", "basis", "floor"):
        raise ValueError("unknown certificate method")
    minimality = None
    if method != "floor":
        try:
            minimality = basis_certificate(candidate["basis"], n, bound)
        except BasisLimitError:
            if method == "basis":
                raise
    if minimality is None:
        count = (bound + 1) // 2
        upper, upper_sum = floor_trace(count, modulus, 2 * a, a + bound)
        lower, lower_sum = floor_trace(count, modulus, 2 * a, a - bound - 1)
        if upper_sum != lower_sum:
            raise ValueError("candidate is not minimal")
        minimality = {"type": "odd-box-floor-sum-v1", "bound": hex(bound),
                      "upper": upper, "lower": lower,
                      "upper_sum": hex(upper_sum), "lower_sum": hex(lower_sum)}
    return {"format": FORMAT, "N": n,
            **{k: hex(candidate[k]) for k in ("A", "H", "p", "q")},
            "basis": [[hex(v) for v in row] for row in candidate["basis"]],
            "nonhold_updates": candidate["nonhold_updates"],
            "parity_sha256": hashlib.sha256(bytes(bits)).hexdigest(),
            "minimality": minimality}


def append_atomic(record):
    """Preserve every prior line byte for byte; atomically publish one more."""
    previous = TARGET.read_bytes() if TARGET.exists() else b""
    if previous and not previous.endswith(b"\n"):
        raise ValueError("incomplete existing checkpoint")
    existing = [json.loads(line) for line in previous.splitlines()]
    if record["N"] in {r["N"] for r in existing}:
        raise ValueError("refusing to replace an existing sample")
    line = (json.dumps(record, sort_keys=True, separators=(",", ":")) + "\n").encode()
    if len(previous) + len(line) > MAX_FILE_BYTES:
        raise ValueError("bounded evidence file would exceed 8 MiB")
    with tempfile.NamedTemporaryFile(dir=ROOT, prefix="height-", suffix=".tmp", delete=False) as stream:
        path = Path(stream.name)
        stream.write(previous + line)
    path.replace(TARGET)


def expired(_signum, _frame):
    raise TimeoutError("per-sample time budget exceeded; earlier records are durable")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--samples", type=int, nargs="+", required=True)
    parser.add_argument("--seconds-per-sample", type=int, default=90)
    parser.add_argument("--certificate", choices=("auto", "basis", "floor"), default="auto")
    parser.add_argument("--write", action="store_true", required=True)
    args = parser.parse_args()
    if not all(16384 < n <= MAX_BITS for n in args.samples):
        parser.error("overnight evidence samples must be in 16385..600000")
    if not 1 <= args.seconds_per_sample <= 180:
        parser.error("seconds-per-sample must be in 1..180")
    # Independent checker imports no producer code. Reuse never trusts JSON alone.
    from verify_results import verify_record
    if TARGET.exists() and TARGET.stat().st_size > MAX_FILE_BYTES:
        parser.error("existing evidence exceeds 8 MiB")
    saved = [json.loads(line) for line in TARGET.read_text().splitlines()] if TARGET.exists() else []
    done = set()
    signal.signal(signal.SIGALRM, expired)
    for record in saved:
        signal.alarm(args.seconds_per_sample)
        verify_record(record)
        done.add(record["N"])
        signal.alarm(0)
        print(f"REUSE VERIFIED N={record['N']}; skipping recomputation", flush=True)
    for n in sorted(set(args.samples) - done):
        signal.alarm(args.seconds_per_sample)
        started = time.perf_counter()
        print(f"START N={n} seconds_budget={args.seconds_per_sample}", flush=True)
        bits = frontier_prefix(n)
        a = residue(bits)
        print(f"RESIDUE N={n} elapsed_seconds={time.perf_counter() - started:.3f}", flush=True)
        candidate = next(candidates(a, n, [n]))
        print(f"CANDIDATE N={n} height_bits={candidate['H'].bit_length()} "
              f"elapsed_seconds={time.perf_counter() - started:.3f}", flush=True)
        record = certify(candidate, bits, method=args.certificate)
        print(f"TRANSCRIPT N={n} type={record['minimality']['type']} "
              f"elapsed_seconds={time.perf_counter() - started:.3f}", flush=True)
        verify_record(record)
        append_atomic(record)
        signal.alarm(0)
        print(f"CERTIFIED N={n} height_bits={candidate['H'].bit_length()} "
              f"nonhold_updates={candidate['nonhold_updates']} "
              f"elapsed_seconds={time.perf_counter() - started:.3f}", flush=True)
    print(f"Checkpoint: {TARGET.relative_to(ROOT)}; existing samples were verified and skipped")


if __name__ == "__main__":
    main()
