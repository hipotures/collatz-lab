#!/usr/bin/env python3
"""Exact odd-denominator box counting and minimax reconstruction (Python ints).

This route uses Euclidean floor sums and binary searches, not lattice reduction.
See phase13-theory.md for the counting identity and certificate semantics.
"""

from math import gcd


VERSION = "odd-box-floor-sum-v1"
MAX_BITS = 16384


def floor_sum(n, m, a, b, trace=None):
    """Sum floor((a*i+b)/m), 0<=i<n; signed a,b, n>=0, m>0."""
    if n < 0 or m <= 0:
        raise ValueError("floor sum requires n>=0 and m>0")
    total = 0
    while True:
        qa, a = divmod(a, m)
        qb, b = divmod(b, m)
        if trace is not None:
            trace.extend((qa, qb))
        total += qa * n * (n - 1) // 2 + qb * n
        y = a * n + b
        if y < m:
            return total
        n, b = divmod(y, m)
        m, a = a, m


def box_count(a, m, bound, terms=None):
    """Count ALL pairs |p|<=bound, 1<=q<=bound odd, p=a*q (mod m)."""
    if bound < 0:
        return 0
    n = (bound + 1) // 2 if terms is None else terms
    return (floor_sum(n, m, 2 * a, a + bound)
            - floor_sum(n, m, 2 * a, a - bound - 1))


def reconstruct(a, bits):
    if not 0 <= bits <= MAX_BITS or not 0 <= a < 1 << bits:
        raise ValueError("invalid bit length or residue")
    m = 1 << bits
    lo, hi = 1, max(1, m // 2)
    while lo < hi:
        mid = (lo + hi) // 2
        if box_count(a, m, mid):
            hi = mid
        else:
            lo = mid + 1
    height = lo
    # Locate the first odd denominator with an eligible numerator, by counts.
    left, right = 1, (height + 1) // 2
    while left < right:
        mid = (left + right) // 2
        if box_count(a, m, height, terms=mid):
            right = mid
        else:
            left = mid + 1
    q = 2 * left - 1
    p = a * q % m
    if 2 * p > m:
        p -= m
    assert max(abs(p), q) == height and gcd(p, q) == 1
    return height, p, q


def minimality_certificate(a, bits, height):
    """Two telescoping Euclidean transcripts certify no vector at H-1."""
    m, b = 1 << bits, height - 1
    n = (b + 1) // 2
    positive, negative = [], []
    u = floor_sum(n, m, 2 * a, a + b, positive)
    v = floor_sum(n, m, 2 * a, a - b - 1, negative)
    if u != v:
        raise ValueError("claimed height is not minimal")
    return {"type": VERSION, "bound": b, "upper": positive,
            "lower": negative, "upper_sum": u, "lower_sum": v}
