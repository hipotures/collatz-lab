#!/usr/bin/env python3
"""Finite exact spectral and exploratory transport checks; no external theorem trusted."""
import sys
sys.dont_write_bytecode = True
from fractions import Fraction
from verify_noncontracting import affine, substitute


def power_count(length, r0, r1, k, b):
    count, size = b, 1
    for _ in range(k):
        count, size = r0 * size + (r1 - r0) * count, length * size
    return count


def ratio_witness(length, r0, r1, s, d):
    denominator = length - r1 + r0
    assert d * r0 < denominator * s and 3**s < 2**d
    b = max(1, abs(r1 - r0))
    c = d * (denominator + r0) + denominator * d
    k = b * c + 1  # Constructed in exists_power_ratio_bound, not a bounded search.
    size = length**k
    cap = s * size // d
    assert (c + 1) * b**k <= size
    for parent in (0, 1):
        assert power_count(length, r0, r1, k, parent) <= cap
    assert d * cap <= s * size
    # The Lean rational_ratio_contraction theorem then proves 3^cap < 2^size.
    # Deliberately do not construct these enormous Collatz powers.
    return k


def main():
    parameter_cases = 0
    for length in range(2, 13):
        for r0 in range(length + 1):
            for r1 in range(1, length + 1):  # Prolongability forces r1>=1.
                delta, denominator = r1 - r0, length - r1 + r0
                if denominator == 0:
                    assert r0 == 0 and r1 == length
                    continue
                assert abs(delta) < length
                assert 3**r0 != 2**denominator
                for k in range(8):
                    for b in (0, 1):
                        count = power_count(length, r0, r1, k, b)
                        assert 0 <= count <= length**k
                        assert denominator * count == r0 * length**k + delta**k * (denominator * b - r0)
                        assert abs(denominator * count - r0 * length**k) <= abs(delta)**k * (denominator + r0)
                parameter_cases += 1
    fixtures = [(3, 2, 1, 5, 8), (4, 3, 1, 5, 8), (5, 4, 1, 5, 8),
                (3, 0, 1, 1, 2), (4, 1, 1, 1, 2), (6, 2, 2, 1, 2)]
    levels = [ratio_witness(*row) for row in fixtures]
    # Literal nonprimitive controls: D=0 constant one, D>0 constant one,
    # and a subcritical fixed point with the zero image containing no ones.
    for one, zero in (([1, 1, 1], [0, 0, 0]), ([1, 1, 1], [1, 0, 0]),
                      ([1, 0, 0], [0, 0, 0])):
        r1, r0 = sum(one), sum(zero)
        bits = [1]
        for k in range(6):
            assert len(bits) == 3**k
            assert sum(bits) == power_count(3, r0, r1, k, 1)
            bits = [x for b in bits for x in (one if b else zero)]
    # Variable cocycle: these two affine maps do not commute, and have
    # incompatible common-center equations (c=-5 vs c=-1).
    assert affine([1, 1, 0]) == (2, 5)
    assert affine([1, 1, 1]) == (3, 19)
    assert 27*5 + 8*19 == 287
    assert 9*19 + 8*5 == 211
    assert 287 - 211 == 76

    # Exploratory finite-coefficient transport for nu=mu^2. These are finite
    # checks of a proposed Mahler route, not a proved analytic value theorem.
    bits = [1]
    for _ in range(8):
        bits = substitute(bits)
    heights = [0]
    for bit in bits:
        heights.append(heights[-1] + bit)
    nu0, nu1 = substitute(substitute([0])), substitute(substitute([1]))
    assert nu0 == [1, 1, 0] * 3
    assert nu1 == nu0[:-1] + [1]
    pref = [sum(nu0[:j]) for j in range(9)]
    assert pref == [0, 1, 2, 2, 3, 4, 4, 5, 6]
    for n in range(200):
        for j in range(9):
            assert heights[9*n + j] == 6*n + heights[n] + pref[j]
    # H(x,y)=sum x^n y^W(n), finite homogeneous coefficient identities.
    y = Fraction(1, 3)
    for n in range(1000):
        parent, col = divmod(n, 9)
        assert y**heights[n] == y**pref[col] * y**(6*parent + heights[parent])
        if n:
            assert y**heights[n] - y**heights[n-1] == (y-1)*bits[n-1]*y**heights[n-1]
    # Independent seed normalization from finite affine offsets at x=2.
    for n in (1, 2, 3, 6, 9, 27, 81):
        r, c = affine(bits[:n])
        seed_sum = -sum(Fraction(2**j, 3**(heights[j] + 1)) for j in range(n) if bits[j])
        assert seed_sum == -Fraction(c, 3**r)
    print(f'{parameter_cases} spectral parameter cases: exact counts, negative/zero eigenvalues PASS')
    print(f'Effective separating-slope witness levels {levels}; degenerate controls PASS')
    print('Noncommuting cocycles and finite two-step prefix-height/seed transport PASS')
    print('Analytic Mahler convergence/transcendence is NOT established by these finite checks')


if __name__ == '__main__':
    main()
