#!/usr/bin/env python3
"""Independent certificate checker: imports NO producer/project implementation.

    python3 research/phase13/verify_certificates.py research/phase13/heights.json.gz

The trusted computing base here is Python exact integer/Fraction arithmetic,
not Lean. The Euclidean certificate identity is proved in the theory report.
"""

import argparse
from fractions import Fraction
import gzip
import json
from math import gcd
from pathlib import Path
import sys

sys.set_int_max_str_digits(20000)


def checked_sum(quotients, expected):
    """Verify a finite Euclidean identity chain from certified quotients.

    Full intermediate large integers are reconstructed rather than stored.
    Quotients are validated by inequalities, not by trusting a solver call.
    """
    assert quotients and len(quotients) % 2 == 0
    n, m, a, b = expected
    result = 0
    for i in range(0, len(quotients), 2):
        assert n >= 0 and m > 0
        qa, qb = quotients[i:i + 2]
        ra, rb = a - qa * m, b - qb * m
        assert 0 <= ra < m and 0 <= rb < m
        result += qa * (n * (n - 1) // 2) + qb * n
        top = ra * n + rb
        if i + 2 == len(quotients):
            assert top < m, "nonterminal certificate truncated"
        else:
            assert top >= m and ra > 0
            next_n, next_b = divmod(top, m)
            n, m, a, b = next_n, ra, m, next_b
    return result


def verify(record, word=None):
    n, a, h, p, q = (record[k] for k in ("N", "A", "H", "p", "q"))
    assert 0 <= n <= 16384 and 0 <= a < 2 ** n
    assert q > 0 and q % 2 == 1 and gcd(p, q) == 1
    assert h == max(abs(p), q) and (p - a * q) % (2 ** n) == 0
    if word is not None:
        assert len(word) >= n and all(b in (0, 1) for b in word)
        # Reverse rational inverse branches, independently of forward offsets.
        seed = Fraction(0)
        for bit in reversed(word[:n]):
            seed = 2 * seed if bit == 0 else (2 * seed - 1) / 3
        assert seed.numerator * pow(seed.denominator, -1, 2 ** n) % (2 ** n) == a
        value = p
        for bit in word[:n]:
            assert value % 2 == bit, "actual numerator parity differs"
            value = (3 * value + q) // 2 if bit else value // 2
    cert = record["minimality"]
    assert cert["type"] == "odd-box-floor-sum-v1" and cert["bound"] == h - 1
    b = h - 1
    terms = (b + 1) // 2
    upper = checked_sum(cert["upper"], (terms, 2 ** n, 2 * a, a + b))
    lower = checked_sum(cert["lower"], (terms, 2 ** n, 2 * a, a - b - 1))
    assert upper == cert["upper_sum"] and lower == cert["lower_sum"]
    assert upper - lower == 0, "there is a smaller-height vector"
    if "basis" in record:
        (u, v), (r, s) = record["basis"]
        assert abs(u * s - v * r) == 2 ** n
        assert (u - a * v) % (2 ** n) == (r - a * s) % (2 ** n) == 0
    return True


def literal_word(spec, length):
    """Independent simultaneous list substitution; no indexed-word recursion."""
    if spec["kind"] == "morphism":
        out = "1"
        while len(out) < length:
            out = "".join(spec["one"] if b == "1" else spec["zero"] for b in out)
        return [int(b) for b in out[:length]]
    if spec["kind"] == "periodic":
        period = spec["period"]
        return [int(period[j % len(period)]) for j in range(length)]
    if spec["kind"] == "explicit":
        return [int(b) for b in spec["bits"][:length]]
    raise ValueError("unknown word specification")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("path", type=Path)
    args = parser.parse_args()
    raw = args.path.read_bytes()
    data = json.loads(gzip.decompress(raw) if args.path.suffix == ".gz" else raw)
    count = 0
    for family in data["families"]:
        word = literal_word(family["spec"], max(x["N"] for x in family["records"]))
        for record in family["records"]:
            verify(record, word)
            count += 1
    print(f"Independent verification: {count} primitive witnesses, parity prefixes, and optimality certificates")


if __name__ == "__main__":
    main()
