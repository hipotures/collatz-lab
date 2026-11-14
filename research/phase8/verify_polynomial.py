#!/usr/bin/env python3
"""Independent finite checks of Phase 8 polynomial identities; standard library only.

These checks are regression evidence. Universal claims come from Lean proofs.
"""
from random import Random


def homogeneous(coefficients, a, b, length):
    return sum(coefficients[j] * a**j * b**(length - 1 - j) for j in range(length))


def convolution(coefficients, word, n):
    return sum(c * word[n - j] for j, c in enumerate(coefficients) if j <= n)


def v2(n):
    assert n
    n = abs(n)
    return (n & -n).bit_length() - 1


def main():
    rng = Random(14)
    count = 0
    for degree in range(7):
        for length in range(degree + 1, degree + 15):
            for a, b in ((0, 0), (0, 3), (2, 0), (4, 3), (16, 27), (-2, 3), (2, -3)):
                p0 = [rng.randrange(-9, 10) for _ in range(degree + 1)]
                p1 = [rng.randrange(-9, 10) for _ in range(degree + 1)]
                word = [rng.randrange(-3, 4) for _ in range(length)]
                residual = [(p0[n] if n <= degree else 0) + convolution(p1, word, n)
                            for n in range(length)]
                tail = sum(p1[j] * b**(degree - j) * homogeneous(word[length - j:], a, b, j)
                           for j in range(1, degree + 1))
                lhs = b**(length - 1) * homogeneous(p0, a, b, degree + 1)
                lhs += homogeneous(p1, a, b, degree + 1) * homogeneous(word, a, b, length)
                rhs = b**degree * homogeneous(residual, a, b, length) + a**length * tail
                assert lhs == rhs
                constant = (degree + 1) * (2 + sum(map(abs, p0 + p1)))
                if a >= 0 and b >= 0:
                    maximum = max(a, b, 1)
                    for u, denominator in ((-13, -5), (17, 9)):
                        form = denominator * homogeneous(p0, a, b, degree + 1)
                        form += u * homogeneous(p1, a, b, degree + 1)
                        assert abs(form) <= constant * maximum**degree * (abs(u) + abs(denominator))
                count += 1

    word = [1]
    while len(word) < 128:
        word = [c for letter in word for c in ([1, 0] if letter else [0, 1])]
    p0 = [1, -6, 3, -4, -3, 6, -9]
    p1 = [-1, 6, -3, 5, -3, -2, -1]
    residual = [(p0[n] if n < 7 else 0) + convolution(p1, word, n) for n in range(14)]
    assert residual == [0] * 13 + [8]
    modulus = 2**64
    rank, numerator = 0, 0
    for j, bit in enumerate(word[:64]):
        if bit:
            rank += 1
            numerator = (numerator - 2**j * pow(3**rank, -1, modulus)) % modulus
    assert numerator == 3195543223027673837
    actual = numerator
    for bit in word[:64]:
        assert actual % 2 == bit
        actual = actual // 2 if bit == 0 else (3 * actual + 1) // 2
    a, b, denominator, u = 4, 3, -1, 3 * (-numerator + 2)
    valuations = []
    for k in range(2):
        form = denominator * homogeneous(p0, a, b, 7) + u * homogeneous(p1, a, b, 7)
        valuations.append(v2(form))
        assert form == (69953636695298807955456, -7357915019712427889214357504)[k]
        delta = (b*b - a*a) * u - denominator * b * a
        denominator, u = denominator * (b - a) * (b*b - a*a), b * delta
        a, b = a*a, b*b
    assert valuations == [29, 55]
    # The general proof only guarantees the formula after m > v2(8) = 3.
    assert not (2 > v2(8)) and 4 > v2(8)
    print(f"{count} exact convolution identities; signed height checks; coefficient-8 valuations {valuations}")


if __name__ == "__main__":
    main()
