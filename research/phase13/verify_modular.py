#!/usr/bin/env python3
"""Bounded exact cancellation audit: full integers and independent modular maps.

This checker imports no project implementation. The finite cycle identities
give the infinite divisibility deductions proved in the theory report.
"""

import argparse
import hashlib
import json
from math import gcd
from pathlib import Path
import sys

sys.set_int_max_str_digits(20000)
ROOT = Path(__file__).resolve().parent


def matrix_product(items):
    m, c, a = 1, 0, 1
    for n, d, b in items:
        m, c, a = m * n, m * d + c * b, a * b
    return m, c, a


def digest(value):
    value = abs(value)
    return hashlib.sha256(value.to_bytes((value.bit_length() + 7) // 8, "big")).hexdigest()


def integer_checks():
    zero, one = (2, 0, 1), (2, 1, 3)
    out = []
    earlier = json.loads((ROOT / "analytics.json").read_text())["shadow_levels"]
    for k in range(8):
        m, d, b = one
        u, c, a = matrix_product([one, zero, zero])
        p, q = -(u * d + c * (b - m)), a * (b - m)
        common = gcd(p, q)
        s, ell = 6 ** k, (56 * 6 ** k - 1) // 5
        h = max(abs(p) // common, q // common)
        assert q > 0 and q % 2 and 2 * h * h < 2 ** ell
        cap = 14 * s * 3 ** ((20 * s - 6 * (-1) ** k) // 7)
        assert h <= cap
        if k >= 2:
            assert 2 * cap * cap < 2 ** ell
        if k < len(earlier):
            assert (p // common, q // common) == (earlier[k]["p"], earlier[k]["q"])
        out.append({"k": k, "S": s, "L": ell, "raw_gcd": common,
                    "raw_numerator_abs_sha256": digest(p), "raw_denominator_sha256": digest(q),
                    "reduced_height_bits": h.bit_length(), "strict_uniqueness": True})
        zero, one = (matrix_product([one] * 5 + [zero]),
                     matrix_product([one, zero, zero, one, one, one]))
    assert [r["raw_gcd"] for r in out] == [3, 1, 1, 1, 1, 1, 1, 347]
    return out


def cycle_check(modulus, start, period, identity):
    def compose(f, g):
        return f[0] * g[0] % modulus, (f[0] * g[1] + f[1]) % modulus
    def product(items):
        f = (1, 0)
        for g in items:
            f = compose(f, g)
        return f
    inv = pow(3, -1, modulus)
    zero, one = (2, 0), (2 * inv % modulus, -inv % modulus)
    first, special, last = None, None, None
    for k in range(start + period + 1):
        if k == start:
            first = [list(zero), list(one)]
        if k == identity:
            special = [list(zero), list(one)]
            assert one == (1, 0)
        if k == start + period:
            last = [list(zero), list(one)]
        zero, one = (product([one] * 5 + [zero]),
                     product([one, zero, zero, one, one, one]))
    assert start <= identity < start + period and first == last
    return {"modulus": modulus, "cycle_start": start, "period": period,
            "identity_level": identity, "start_state": first,
            "repeat_state": last, "identity_state": special}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    result = {"format": "phase13-cancellation-v1", "integer_levels": integer_checks(),
              "cycles": [cycle_check(347, 1, 86, 7),
                         cycle_check(347 ** 2, 62, 14878, 5425)]}
    target = ROOT / "modular.json"
    if args.write:
        target.write_text(json.dumps(result, indent=2) + "\n")
    else:
        assert result == json.loads(target.read_text())
    print("PASS: raw gcds at levels 0..7; first positive-level noncoprime pair at k=7; "
          "exact recurrence cycles modulo 347 and 347^2")


if __name__ == "__main__":
    main()
