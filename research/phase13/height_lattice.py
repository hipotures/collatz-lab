#!/usr/bin/env python3
"""Adaptive exact odd-denominator minimization, replicating Klapper--Goresky.

The input is the ordinary seed residue, not its Collatz parity word. This
module does not import the reference algorithm or the certificate verifier.
"""

from math import gcd


VERSION = "kg-odd-coset-v1"
MAX_BITS = 16384


def norm(v):
    return max(abs(v[0]), abs(v[1]))


def best_odd_translate(u, v):
    """Minimize max(|u0+d*v0|,|u1+d*v1|) over ALL odd integers d.

    A convex piecewise linear function changes slopes only at a zero of a
    coordinate or an equality of their absolute values. Bracket every such
    breakpoint by odd integers. Include +-1 for flat or degenerate pieces.
    """
    candidates = {-1, 1}
    for numerator, denominator in [(-u[0], v[0]), (-u[1], v[1]),
                                   (u[1] - u[0], v[0] - v[1]),
                                   (-u[1] - u[0], v[0] + v[1])]:
        if denominator:
            k = numerator // denominator
            lower = k if k % 2 else k - 1
            candidates.update((lower, lower + 2))
    def key(d):
        point = (u[0] + d * v[0], u[1] + d * v[1])
        return norm(point), abs(d), d
    d = min(candidates, key=key)
    return (u[0] + d * v[0], u[1] + d * v[1]), d


def profile(a, bits):
    """Yield (N,H,p,q,even basis vector,odd basis vector,transition).

    All N are produced once; retained f,g have determinant magnitude 2^N.
    f has even coordinates and is outside the next cylinder. g is a norm
    minimizer over odd second coordinates. Global minimality is checked by
    an independent box certificate rather than trusting this invariant alone.
    """
    if not 0 <= bits <= MAX_BITS or not 0 <= a < 1 << bits:
        raise ValueError("invalid bit length or residue")
    first = (a & -a).bit_length() - 1 if a else bits
    for n in range(1, min(first, bits) + 1):
        yield n, 1, 0, 1, (1 << n, 0), (0, 1), "zero"
    if first >= bits:
        return
    k = first + 1
    f, g = (0, 2), (1 << first, 1)
    yield k, norm(g), g[0], g[1], f, g, "initialize"
    for k in range(k + 1, bits + 1):
        modulus = 1 << k
        if (a * g[1] - g[0]) % modulus == 0:
            f = (2 * f[0], 2 * f[1])
            transition = "hold"
        elif norm(g) < norm(f):
            new_g, d = best_odd_translate(f, g)
            f, g = (2 * g[0], 2 * g[1]), new_g
            transition = f"swap:{d}"
        else:
            g, d = best_odd_translate(g, f)
            f = (2 * f[0], 2 * f[1])
            transition = f"translate:{d}"
        p, q = g if g[1] > 0 else (-g[0], -g[1])
        assert q % 2 == 1 and gcd(p, q) == 1
        assert abs(f[0] * g[1] - f[1] * g[0]) == modulus
        assert (p - a * q) % modulus == 0
        yield k, norm(g), p, q, f, g, transition


def reconstruct(a, bits):
    if bits == 0:
        return 1, 0, 1
    last = None
    for last in profile(a, bits):
        pass
    return last[1:4]
