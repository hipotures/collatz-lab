#!/usr/bin/env python3
"""Independent exact replication of the written structural arguments.

No height engine or certificate-producer imports. --write records finite
evidence; --check reproduces it. Universally quantified claims are proved in
the theory report / Lean modules, not inferred from this enumeration.
"""

import argparse
from fractions import Fraction
import gzip
import json
from math import gcd, isclose, log2
from pathlib import Path
import sys

sys.set_int_max_str_digits(20000)
ROOT = Path(__file__).resolve().parent


def substitute(s):
    return "".join("100111" if b == "1" else "111110" for b in s)


def inverse(prefix, y):
    for bit in reversed(prefix):
        y = 2 * y if bit == "0" else (2 * y - 1) / 3
    return y


def affine(s):
    slope, offset = 1, 0
    for j, bit in enumerate(s):
        if bit == "1":
            slope *= 3
            offset = 3 * offset + 2 ** j
    return slope, offset


def numerator_parities(p, q, n):
    out = []
    for _ in range(n):
        bit = p % 2
        out.append(str(bit))
        p = (3 * p + q) // 2 if bit else p // 2
    return "".join(out)


def data():
    w = "1"
    while len(w) < 16385:
        w = substitute(w)
    finite = json.loads(gzip.decompress((ROOT / "heights.json.gz").read_bytes()))
    heights = {r["N"]: r for r in finite["families"][0]["records"]}
    records = []
    u, v = "100", "1"
    for k in range(5):
        s, e = 6 ** k, (-1) ** k
        ell = (56 * s - 1) // 5
        assert u == w[:3 * s] and v == w[:s]
        a, c = affine(u)
        b, d = affine(v)
        ru, rv = u.count("1"), v.count("1")
        assert 7 * ru == 15 * s - 8 * e
        assert 7 * rv == 5 * s + 2 * e
        # Construct the periodic seed by solving an independently evaluated
        # rational inverse-branch fixed-point equation.
        y0, y1 = inverse(v, Fraction(0)), inverse(v, Fraction(1))
        periodic = y0 / (1 - (y1 - y0))
        shadow = inverse(u, periodic)
        p, q = shadow.numerator, shadow.denominator
        raw_p = -(2 ** (3 * s) * d + c * (b - 2 ** s))
        raw_q = a * (b - 2 ** s)
        assert Fraction(raw_p, raw_q) == shadow
        assert q > 0 and q % 2 == 1 and gcd(p, q) == 1
        h = max(abs(p), q)
        upper = 14 * s * 3 ** (ru + rv)
        assert h <= upper
        itinerary = numerator_parities(p, q, ell + 1)
        assert itinerary[:ell] == w[:ell] and itinerary[ell] != w[ell]
        assert h == heights[ell]["H"]
        assert 2 * h * h < 2 ** ell
        next_h = heights[ell + 1]["H"]
        assert 2 ** ell <= 2 * h * next_h
        records.append({"k": k, "S": s, "match_length": ell, "first_failure": ell,
                        "preperiod_weight": ru, "period_weight": rv,
                        "p": p, "q": q, "raw_gcd": gcd(raw_p, raw_q),
                        "height": h, "height_upper_bound": upper,
                        "log2H_over_match": log2(h) / ell,
                        "next_height": next_h})
        u, v = substitute(u), substitute(v)
    # Independently check the elementary pressure/offset estimates used in
    # the all-level proof; this finite check is additional evidence only.
    a, c = 1, 0
    for n, bit in enumerate(w[:16384]):
        assert 2 ** n <= 4 * a
        assert c <= 2 * n * a
        if bit == "1":
            a *= 3
            c = 3 * c + 2 ** n
    # Product matrices are inverse branches [[2^len,-c],[0,3^r]].
    assert affine("100111") == (81, 179)
    assert affine("111110") == (243, 211)
    commutator_upper_right = -64 * 211 - 179 * 243 - (-64 * 179 - 211 * 81)
    assert commutator_upper_right == -28454
    # Deliberately false common multiplier 81 already fails on source 10.
    true = inverse("100111111110", Fraction(0))
    false = Fraction(-179, 81) + Fraction(64, 81) * Fraction(-211, 81)
    true_residue = true.numerator * pow(true.denominator, -1, 4096) % 4096
    false_residue = false.numerator * pow(false.denominator, -1, 4096) % 4096
    assert true_residue != false_residue
    return {"format": "phase13-analytic-replication-v1", "shadow_levels": records,
            "pressure_prefixes_checked": 16384,
            "common_multiplier_counterexample": {"source_prefix": "10", "N": 12,
                                                    "actual_A": true_residue, "false_A": false_residue},
            "inverse_matrix_commutator_upper_right": commutator_upper_right}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    result = data()
    target = ROOT / "analytics.json"
    if args.write:
        target.write_text(json.dumps(result, indent=2) + "\n")
    else:
        saved = json.loads(target.read_text())
        for actual, expected in zip(result["shadow_levels"], saved["shadow_levels"]):
            assert isclose(actual.pop("log2H_over_match"), expected.pop("log2H_over_match"),
                           rel_tol=1e-14, abs_tol=1e-14)
        assert result == saved
    print("PASS: five independently constructed rational shadow levels, exact first failures, "
          "height/minimum/crossing checks, pressure controls and false-multiplier counterexample")


if __name__ == "__main__":
    main()
