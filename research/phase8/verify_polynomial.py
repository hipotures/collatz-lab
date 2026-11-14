#!/usr/bin/env python3
"""Independent finite checks of Phase 8 polynomial identities; standard library only.

These checks are regression evidence. Universal claims come from Lean proofs.
"""
from random import Random
from functools import reduce
from math import gcd
from itertools import product


def homogeneous(coefficients, a, b, length):
    return sum(coefficients[j] * a**j * b**(length - 1 - j) for j in range(length))


def convolution(coefficients, word, n):
    return sum(c * word[n - j] for j, c in enumerate(coefficients) if j <= n)


def v2(n):
    assert n
    n = abs(n)
    return (n & -n).bit_length() - 1


def integer_null_vector(rows, width):
    """Independent division-free reconstruction, including deficient rank."""
    pivot_index = next((i for i, row in enumerate(rows) if row[0]), None)
    if pivot_index is None:
        return [1] + [0] * (width - 1)
    pivot = rows[pivot_index]
    reduced = [[pivot[0] * row[j] - row[0] * pivot[j] for j in range(1, width)]
               for i, row in enumerate(rows) if i != pivot_index]
    y = integer_null_vector(reduced, width - 1)
    return [-sum(c * value for c, value in zip(pivot[1:], y))] + [pivot[0] * value for value in y]


def determinant(matrix):
    """Exact Bareiss determinant for the six fixed prefix systems."""
    rows = [row[:] for row in matrix]
    size, previous, sign = len(rows), 1, 1
    for k in range(size - 1):
        pivot = next((i for i in range(k, size) if rows[i][k]), None)
        if pivot is None:
            return 0
        if pivot != k:
            rows[k], rows[pivot] = rows[pivot], rows[k]
            sign = -sign
        for i in range(k + 1, size):
            for j in range(k + 1, size):
                value = rows[k][k] * rows[i][j] - rows[i][k] * rows[k][j]
                assert value % previous == 0
                rows[i][j] = value // previous
            rows[i][k] = 0
        previous = rows[k][k]
    return sign * rows[-1][-1]


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

    matrix_count = 0
    for rows_count in range(9):
        for trial in range(16):
            rows = [[rng.randrange(-4, 5) for _ in range(rows_count + 1)]
                    for _ in range(rows_count)]
            if trial % 4 == 0:
                rows = [[0] * (rows_count + 1) for _ in range(rows_count)]
            elif trial % 4 == 1:
                for row in rows:
                    row[0] = 0
            elif trial % 4 == 2 and rows_count >= 2:
                rows[-1] = rows[0][:]
            x = integer_null_vector(rows, rows_count + 1)
            assert len(x) == rows_count + 1 and any(x)
            assert all(sum(c * value for c, value in zip(row, x)) == 0 for row in rows)
            matrix_count += 1
    print(f"{matrix_count} exact integer null vectors, including zero and deficient-rank matrices")

    first_ledger_failures = []
    for degree in range(6):
        first = next(length for length in range(2, 102)
                     if max(2**length, 3**(length - 1))**(degree*(length - 1) + 2*length - 1)
                     >= 2**((2*degree + 1)*length*(length - 1)))
        first_ledger_failures.append(first)
    assert first_ledger_failures == [2, 2, 2, 7, 16, 101]
    assert all(2**((2*degree + 1)*101) <= 3**(degree*100 + 201) for degree in range(6))
    print(f"First worst-parameter ledger failures for degrees 0..5: {first_ledger_failures}")

    normal_prefix = [1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1]
    determinants = [determinant([[normal_prefix[n - j] for j in range(size)]
                                for n in range(size, 2 * size)]) for size in range(1, 7)]
    assert determinants == [1, -1, 1, -1, -1, -1]
    hard_one = normal_prefix + [1] * 987 + [0]
    hard_zero = hard_one[:]
    hard_zero[0], hard_zero[999] = 0, 1
    assert len(hard_one) == len(hard_zero) == 1000
    assert hard_one[0] == 1 and hard_one != hard_zero
    assert sum(hard_one) == sum(hard_zero) == 993
    assert [j for j in range(1000) if hard_one[j] != hard_zero[j]] == [0, 999]
    assert 2**19 <= 3**12
    for degree in range(6):
        assert ((2 * degree + 1) * 1000 * 999) * 12 <= 19 * 993 * (degree * 999 + 1999)
    hard_p1 = integer_null_vector([[hard_one[n - j] for j in range(7)] for n in range(7, 13)], 7)
    content = reduce(gcd, map(abs, hard_p1))
    hard_p1 = [c // content for c in hard_p1]
    hard_p0 = [-convolution(hard_p1, hard_one, n) for n in range(7)]
    assert hard_p1 == [-1, -1, 1, 1, 2, 1, -1]
    assert hard_p0 == [1, 2, 0, -1, -2, -4, -1]
    assert [(hard_p0[n] if n <= 6 else 0) + convolution(hard_p1, hard_one, n)
            for n in range(14)] == [0] * 13 + [-1]
    high_one = [1] * 101
    high_one[1] = 0
    high_zero = [1] * 101
    high_zero[100] = 0
    high_word = high_one + high_zero
    assert [([-1, 1, -1][n] if n <= 2 else 0) + convolution([1, -1, 0], high_word, n)
            for n in range(202)] == [0] * 201 + [-1]
    print("Six exact nonsingular prefix systems; hard length-1000 degree-six pair; degree-two/order-201 pair")

    encoded_windows = 0
    for base in range(1, 8):
        for length in range(5):
            seen = set()
            for digits in product(range(base), repeat=length):
                code = 0
                for digit in digits:
                    symbol = digit - 3
                    code = base * code + (symbol - (-3))
                assert 0 <= code < base**length and code not in seen
                seen.add(code)
                encoded_windows += 1
            assert len(seen) == base**length
    for p0, p1, sequence in (
        ([-3, 2, 0], [1, 0, -1], [3 if n % 2 == 0 else -2 for n in range(32)]),
        ([7, 0], [1, -1], [-7] * 32),
        ([0, -1, 0], [1, -2, 1], list(range(32))),
    ):
        assert all((p0[n] if n < len(p0) else 0) + convolution(p1, sequence, n) == 0
                   for n in range(32))
    print(f"{encoded_windows} signed-alphabet encodings; singleton, signed periodic and unbounded rational identities")

    secondary_p0 = [13, 4, 17, 8, 21, 25, 18, 7, 20, -2, 9]
    secondary_p1 = [-13, -4, -4, -4, -4, -4, 7, 9, -2, 9, 11]
    secondary_seed = 24489870188561073689074139556808871213586148320332801509179590176121701984609
    secondary_word = [1]
    while len(secondary_word) < 256:
        secondary_word = [c for letter in secondary_word for c in ([1, 0, 1] if letter else [0, 1, 1])]
    actual = secondary_seed
    for bit in secondary_word[:256]:
        assert actual % 2 == bit
        actual = actual // 2 if bit == 0 else (3 * actual + 1) // 2
    assert [(secondary_p0[n] if n <= 10 else 0) + convolution(secondary_p1, secondary_word, n)
            for n in range(22)] == [0] * 21 + [24]
    a, b, denominator, u = 8, 9, 3, 9 * (secondary_seed + 10)
    secondary_valuations = []
    for k in range(2):
        assert (b**21 * u - denominator * homogeneous(secondary_word, a, b, 22)) % a**22 == 0
        form = denominator * homogeneous(secondary_p0, a, b, 11)
        form += u * homogeneous(secondary_p1, a, b, 11)
        secondary_valuations.append(v2(form))
        delta = (b**3 - a**3) * u - denominator * b * (a * b + a*a)
        denominator, u = denominator * (b - a) * (b**3 - a**3), b * delta
        a, b = a**3, b**3
    assert secondary_valuations == [68, 192]
    assert 68 != 21 * 3 + v2(24) and 192 == 21 * 9 + v2(24)
    print("Actual coefficient-24 premature valuation: 68 instead of 66; safe next level: 192")

    semantic_fixtures = [
        ([0, 1], [1, 0], 13, -15),
        ([0, 1, 1], [1, 0, 1], 353, -283),
        ([1, 0, 1, 0], [1, 1, 0, 0], 12947, -801),
        ([1, 1, 1, 0, 1], [1, 1, 1, 1, 0], 25850607, -4964693),
        ([0, 1, 1, 0, 1, 1], [1, 0, 1, 0, 1, 1], 11999337121, -8722791131),
    ]
    for zero, one, positive, negative in semantic_fixtures:
        length = len(one)
        literal = [c for letter in one for c in (one if letter else zero)]
        for numerator, denominator in ((positive, 1), (negative, 5), (3 * negative, 15)):
            actual = numerator
            for bit in literal:
                assert actual % 2 == bit
                actual = actual // 2 if bit == 0 else (3 * actual + denominator) // 2
        extended = [1]
        while len(extended) < 128:
            extended = [c for letter in extended for c in (one if letter else zero)]
        assert extended[:length**2] == literal
        rows = [[extended[n - j] for j in range(7)] for n in range(7, 13)]
        p1 = integer_null_vector(rows, 7)
        assert any(p1)
        p0 = [-convolution(p1, extended, n) for n in range(7)]
        assert all((p0[n] if n <= 6 else 0) + convolution(p1, extended, n) == 0
                   for n in range(13))
        if length == 6:
            assert sum(one) == sum(zero) == 4 and 3**4 > 2**6
            assert not 81**37 < 2**180
            assert 81**37 < 2**390
            explicit_p0 = [0, -1, 0, -1, 1, -1, 0]
            explicit_p1 = [0, 1, 0, 0, -1, 0, 0]
            residual = [(explicit_p0[n] if n <= 6 else 0) + convolution(explicit_p1, extended, n)
                        for n in range(14)]
            assert residual == [0] * 13 + [1]
    print("Literal substitution and signed/unreduced rational prefixes at L=2..6; five degree-six pairs")

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
