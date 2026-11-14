#!/usr/bin/env python3
"""Finite exact regressions for Phase 11; these computations are not infinite proofs."""
from itertools import accumulate


def substitute(bits):
    return [x for b in bits for x in ([1, 1, 0] if b else [1, 1, 1])]


def indexed(n):
    if n == 0:
        return 1
    parent, column = divmod(n, 3)
    return 1 if column < 2 else 1 - indexed(parent)


def affine(bits):
    weight, offset = 0, 0
    for j, b in enumerate(bits):
        if b:
            weight += 1
            offset = 3 * offset + 2**j
    return weight, offset


def replay(p, q, bits):
    initial = p
    for b in bits:
        assert p % 2 == b
        p = (3 * p + q) // 2 if b else p // 2
    r, c = affine(bits)
    assert 2**len(bits) * p == 3**r * initial + c * q
    return p


def main():
    bits = [1]
    for k in range(9):
        assert bits == [indexed(n) for n in range(3**k)]
        assert 4 * sum(bits) == 3 * 3**k + (-1)**k
        if k < 8:
            bits = substitute(bits)
    assert bits[:9] == [1, 1, 0, 1, 1, 0, 1, 1, 1]
    prefix = [0] + list(accumulate(bits))
    for k in range(9):
        for n in range(3**k):
            assert abs(4 * prefix[n] - 3 * n) <= 2 * k
    for a in range(len(bits) - 2):
        assert sum(bits[a:a + 3]) >= 2
    for h in range(1, 41):
        for a in range(81):
            assert sum(bits[a:a + 3*h]) >= 2*h
        assert 3**(2*h) > 2**(3*h)
    # Bounded partition checks support the theorem but do not replace its quantifiers.
    for t in range(9):
        for k in range(1, 81):
            maximum = max(sum(bits[t+k*n:t+k*(n+1)]) for n in range(3))
            assert 3 * maximum >= 2 * k
            assert 3**maximum > 2**k
    # Actual signed, unreduced and sign-normalized rational finite itineraries.
    finite = bits[:81]
    r, c = affine(finite)
    modulus = 2**len(finite)
    for q in (1, 5):
        p = (-c * q * pow(3**r, -1, modulus)) % modulus
        for initial in (p, p - modulus):
            end = replay(initial, q, finite)
            assert replay(3 * initial, 3 * q, finite) == 3 * end
            assert replay(-initial, -q, finite) == -end
    # Independent rational periodic controls, including a supercritical square word.
    p = 1
    for n in range(100):
        assert p % 2 == 1 - n % 2
        p = (3 * p + 1) // 2 if p % 2 else p // 2
    assert replay(-1, 1, [1] * 100) == -1
    print('Phase 11 finite checks: literal levels 0..8, all prefix discrepancies,')
    print('windows/group obstruction, signed 81-bit witnesses and rational controls: PASS')


if __name__ == '__main__':
    main()
