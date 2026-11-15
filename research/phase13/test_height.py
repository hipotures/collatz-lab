#!/usr/bin/env python3
"""Bounded exact cross-checks and hostile certificates; no stochastic tests."""

from copy import deepcopy
from fractions import Fraction
from itertools import product
from math import gcd

import height_lattice as lattice
import height_reference as reference
from verify_certificates import verify


def brute(a, n):
    m = 1 << n
    best = (max(1, m), 0, 1)
    for q in range(1, max(2, m // 2 + 1), 2):
        p = a * q % m
        if p > m // 2:
            p -= m
        candidate = max(abs(p), q), p, q
        if candidate < best:
            best = candidate
    return best


def parity(q, p, length):
    out = []
    for _ in range(length):
        out.append(p % 2)
        p = (3 * p + q) // 2 if p % 2 else p // 2
    return out


def residue(bits):
    value = Fraction(0)
    for b in reversed(bits):
        value = 2 * value if not b else (2 * value - 1) / 3
    return value.numerator * pow(value.denominator, -1, 1 << len(bits)) % (1 << len(bits))


def main():
    sums = 0
    for n, m, a, b in product(range(8), range(1, 12), range(-8, 9), range(-8, 9)):
        assert reference.floor_sum(n, m, a, b) == sum((a * i + b) // m for i in range(n))
        sums += 1
    cases = 0
    for n in range(12):
        for a in range(1 << n):
            exact = brute(a, n)[0]
            ref = reference.reconstruct(a, n)
            opt = lattice.reconstruct(a, n)
            assert ref[0] == opt[0] == exact, (a, n, ref, opt, exact)
            h, p, q = opt
            assert gcd(p, q) == 1 and q > 0 and q % 2
            record = {"N": n, "A": a, "H": h, "p": p, "q": q,
                      "minimality": reference.minimality_certificate(a, n, h)}
            verify(record)
            cases += 1
    # Independent parity cylinder equivalence, with signed odd denominators.
    signed = 0
    for n in range(7):
        for a in range(1 << n):
            expected = parity(1, a, n)
            for q in range(-9, 10, 2):
                for p in range(-12, 13):
                    assert (parity(q, p, n) == expected) == ((p - a * q) % (1 << n) == 0)
                    assert parity(q, p, n) == parity(-q, -p, n)
                    signed += 1
    # Actual numerator iteration reproduces both issue regressions. For H_12
    # test every signed p and positive odd q below 513, without using residues.
    word = "1"
    while len(word) < 12:
        word = "".join("100111" if b == "1" else "111110" for b in word)
    bits = [int(x) for x in word[:12]]
    assert parity(1, -3, 11) == bits[:11]
    assert all(parity(q, p, 11) != bits[:11] for q in (1,) for p in range(-2, 3))
    rejected = 0
    for q in range(1, 513, 2):
        for p in range(-512, 513):
            assert parity(q, p, 12) != bits
            rejected += 1
    assert parity(513, 509, 12) == bits
    assert reference.reconstruct(residue(bits[:11]), 11)[0] == 3
    assert lattice.reconstruct(residue(bits), 12)[0] == 513
    # Rational controls, nonprimitive odd scalings and the even-q trap.
    for n in (1, 2, 11, 64, 256):
        for p, q in [(0, 1), (-1, 1), (1, 1)]:
            a = residue(parity(q, p, n))
            assert lattice.reconstruct(a, n)[0] == 1
            assert reference.reconstruct(a, n)[0] == 1
            assert parity(3 * q, 3 * p, n) == parity(q, p, n)
        a = 1 << (n - 1)
        assert reference.reconstruct(a, n)[0] == max(1, a)
        if n > 1:
            assert (0 - a * 2) % (1 << n) == 0
            assert (0 - a) % (1 << n) != 0
    # Independent deterministic large residues exercise arbitrary precision.
    for n in (64, 127, 256, 511):
        a = pow(7, n, 1 << n)
        assert reference.reconstruct(a, n)[0] == lattice.reconstruct(a, n)[0]
    a, n = residue(bits), 12
    h, p, q = lattice.reconstruct(a, n)
    good = {"N": n, "A": a, "H": h, "p": p, "q": q,
            "minimality": reference.minimality_certificate(a, n, h)}
    mutations = []
    for key, value in [("H", h + 1), ("p", p + 1), ("q", 2 * q), ("A", a ^ 1)]:
        bad = deepcopy(good); bad[key] = value; mutations.append(bad)
    bad = deepcopy(good); bad["minimality"]["upper"].pop(); mutations.append(bad)
    bad = deepcopy(good); bad["minimality"]["lower_sum"] += 1; mutations.append(bad)
    bad = deepcopy(good); bad["minimality"]["lower"][0] += 1; mutations.append(bad)
    for bad in mutations:
        try:
            verify(bad, bits)
        except (AssertionError, ValueError):
            pass
        else:
            raise AssertionError("hostile certificate accepted")
    print(f"PASS: {sums} signed floor sums; {cases} exhaustive residues; "
          f"{signed} signed parity cylinders; {rejected} direct H_12 exclusions; "
          f"7 rejected corrupt certificates; H_11=3, H_12=513")


if __name__ == "__main__":
    main()
