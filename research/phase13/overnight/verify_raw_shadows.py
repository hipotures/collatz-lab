#!/usr/bin/env python3
"""Independent raw-shadow replay using expanded positive-offset recurrences.

No producer or project imports. Denominators come from closed letter counts,
not matrix multiplication. Gcd checking splits Q=3^r*(b-2^S), using its
coprime factors rather than applying gcd to the same full coordinate pair.
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
MAX_LEVEL = 8
MAX_BYTES = 65536


def sha(value):
    magnitude = abs(value)
    return hashlib.sha256(magnitude.to_bytes((magnitude.bit_length() + 7) // 8, "big")).hexdigest()


def scalars(k):
    s, sign = 6 ** k, (-1) ** k
    r0, r1 = (5 * s - 5 * sign) // 7, (5 * s + 2 * sign) // 7
    return s, r0, r1, 1 << s, 3 ** r0, 3 ** r1


def offsets_next(c0, c1, m, a, b):
    # For X=x_0...x_5, c_X=sum(m^j*c_xj*prod(a_xi, i>j)).
    # Expand the two different six-letter words separately; no matrix routine.
    m2, m3, m4, m5 = m * m, m ** 3, m ** 4, m ** 5
    b2, b3, b4 = b * b, b ** 3, b ** 4
    new0 = m5 * c0 + a * c1 * (m4 + m3 * b + m2 * b2 + m * b3 + b4)
    new1 = (c1 * (a * a * b3 + m3 * b2 + m4 * b + m5)
            + c0 * (m * a * b3 + m2 * b3))
    return new0, new1


def shadow(k, c0, c1):
    s, r0, r1, m, a, b = scalars(k)
    preperiod_c = c1 * a * a + m * c0 * a + m * m * c0
    delta = b - m
    p = -(m ** 3 * c1 + preperiod_c * delta)
    q = 3 ** (r1 + 2 * r0) * delta
    return p, q, delta, r1 + 2 * r0


def split_gcd(p, delta, exponent):
    # delta is odd and coprime to 3, so its gcd factor and the 3-part separate.
    assert p and delta > 0 and delta % 2 and delta % 3
    rest, used = abs(p), 0
    while used < exponent and rest % 3 == 0:
        rest //= 3
        used += 1
    return 3 ** used * gcd(abs(p), delta)


def verify_row(row, k, c0, c1, inherited):
    p, q, delta, exponent = shadow(k, c0, c1)
    assert p < 0 < q and q % 2 == 1
    common = split_gcd(p, delta, exponent)
    assert p % common == q % common == 0
    reduced_p, reduced_q = p // common, q // common
    # Independently certify that no common factor remains in either Q factor.
    assert gcd(abs(reduced_p), delta // gcd(abs(p), delta)) == 1
    assert exponent == 0 or common % 3 == 0 or reduced_p % 3 != 0
    if common % 3 == 0:
        rest, remaining = common, exponent
        while rest % 3 == 0:
            rest //= 3
            remaining -= 1
        assert remaining >= 0 and (remaining == 0 or reduced_p % 3 != 0)
    h = max(abs(reduced_p), reduced_q)
    s, ell = 6 ** k, (56 * 6 ** k - 1) // 5
    assert 2 * h * h < 1 << ell
    expected = {"format": "phase13-overnight-raw-shadow-v1", "k": k, "S": s, "L": ell,
                "raw_gcd": hex(common), "numerator_sign": -1,
                "denominator_sign": 1, "denominator_odd": True,
                "raw_numerator_bits": abs(p).bit_length(), "raw_denominator_bits": q.bit_length(),
                "reduced_numerator_bits": abs(reduced_p).bit_length(),
                "reduced_denominator_bits": reduced_q.bit_length(),
                "reduced_height_bits": h.bit_length(),
                "raw_numerator_abs_sha256": sha(p), "raw_denominator_sha256": sha(q),
                "reduced_numerator_abs_sha256": sha(reduced_p),
                "reduced_denominator_sha256": sha(reduced_q), "strict_uniqueness": True}
    assert type(row["raw_gcd"]) is str and hex(int(row["raw_gcd"], 16)) == row["raw_gcd"]
    assert row == expected, f"independent replay differs at k={k}"
    if k < len(inherited):
        old = inherited[k]
        assert common == old["raw_gcd"]
        for key in ("k", "S", "L", "raw_numerator_abs_sha256", "raw_denominator_sha256",
                    "reduced_height_bits", "strict_uniqueness"):
            assert expected[key] == old[key], f"inherited evidence differs at k={k}"
    return p, q


def literal_controls():
    # Reverse integer rational branches, without using either large recurrence.
    words = ["0", "1"]
    c0, c1 = 0, 1
    for k in range(5):
        for word, offset in zip(words, (c0, c1)):
            numerator, denominator = 0, 1
            for bit in reversed(word):
                numerator *= 2
                if bit == "1":
                    numerator -= denominator
                    denominator *= 3
            assert numerator == -offset
            assert denominator == 3 ** word.count("1")
        if k < 4:
            _, _, _, m, a, b = scalars(k)
            c0, c1 = offsets_next(c0, c1, m, a, b)
            words = ["".join("100111" if bit == "1" else "111110" for bit in word)
                     for word in words]
    return 10


def expired(_signum, _frame):
    raise TimeoutError("independent raw-shadow replay exceeded its per-level budget")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--write", action="store_true")
    parser.add_argument("--seconds-per-level", type=int, default=180)
    args = parser.parse_args()
    if not 1 <= args.seconds_per_level <= 240:
        parser.error("seconds-per-level must be in 1..240")
    target = ROOT / "raw-shadows.jsonl"
    assert target.stat().st_size <= MAX_BYTES
    raw = target.read_bytes()
    assert raw.endswith(b"\n")
    rows = [json.loads(line) for line in raw.splitlines()]
    assert 1 <= len(rows) <= MAX_LEVEL + 1
    assert [row["k"] for row in rows] == list(range(len(rows)))
    baseline_raw = (ROOT.parent / "modular.json").read_bytes()
    inherited = json.loads(baseline_raw)["integer_levels"]
    signal.signal(signal.SIGALRM, expired)
    signal.alarm(args.seconds_per_level)
    controls = literal_controls()
    signal.alarm(0)
    c0, c1, old_scalars = 0, 1, None
    for k, row in enumerate(rows):
        signal.alarm(args.seconds_per_level)
        started = time.perf_counter()
        if old_scalars is not None:
            c0, c1 = offsets_next(c0, c1, *old_scalars)
        verify_row(row, k, c0, c1, inherited)
        _, _, _, m, a, b = scalars(k)
        old_scalars = m, a, b
        signal.alarm(0)
        print(f"VERIFIED k={k} gcd={row['raw_gcd']} "
              f"elapsed_seconds={time.perf_counter() - started:.3f}", flush=True)
    manifest = {"format": "phase13-raw-shadow-replay-v1",
                "classification": "independent exact finite replay; no asymptotic inference",
                "source_sha256": hashlib.sha256(raw).hexdigest(), "source_bytes": len(raw),
                "inherited_source_sha256": hashlib.sha256(baseline_raw).hexdigest(),
                "verified_levels": list(range(len(rows))),
                "inherited_controls": list(range(min(len(rows), len(inherited)))),
                "literal_reverse_branch_controls": controls,
                "gcd_method": "coprime denominator factors: 3-adic valuation and gcd(P, b-2^S)"}
    destination = ROOT / "raw-shadow-verification.json"
    if args.write:
        with tempfile.NamedTemporaryFile(dir=ROOT, prefix="raw-replay-", suffix=".tmp",
                                         delete=False) as stream:
            temporary = Path(stream.name)
            stream.write((json.dumps(manifest, indent=2) + "\n").encode())
        temporary.replace(destination)
    else:
        assert json.loads(destination.read_bytes()) == manifest
    print(f"PASS: {len(rows)} independently replayed levels; {controls} literal controls; "
          "inherited signs/gcds/hashes agree", flush=True)


if __name__ == "__main__":
    main()
