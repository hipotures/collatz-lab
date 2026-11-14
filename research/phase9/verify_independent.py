#!/usr/bin/env python3
"""Independent Phase 9 cross-checks of the equal-weight argument.

This script shares no code with the Lean development or with the Phase 7/8
checkers.  It re-derives, with exact integer and rational arithmetic, the
identities used in the written proof (paper/main.tex) and tests them on all
admissible substitutions of small length:

  T1  Bernstein's series for the seed agrees with the block formula
      x = -c0/(1-z0) - (c1-c0) V(z0) modulo 2^M, and the seed's first
      parities reproduce the word.
  T2  The Mahler recursion in the factored form used for the tower,
      V(z^L) = b^e ((b^L-a^L) V(z) b^(L-1) - b Q0(a,b)) / (b^(L-1) a^s G*(a,b) (b^L-a^L)),
      holds modulo 2^M along z_k = z0^(L^k).
  T3  A degree-six pair computed by rational elimination has a nonzero
      denominator, residual order N >= 13, and satisfies the strict gap.
  T4  The 2-adic valuation of P0(z_k) + P1(z_k) V(z_k) equals
      N L^(k+1) + v2(R_N) whenever L^(k+1) > v2(R_N).
  T5  The numerical ledger: degree six closes for all 2 <= L <= 400;
      degrees 0..5 first fail at L = 2, 2, 2, 7, 16, 101.
  T6  Bounded aperiodicity evidence and the unequal-weight control 101/010.

All checks are finite.  They support, and do not replace, the proofs.
"""
from fractions import Fraction
from itertools import product
import sys

M_BITS = 900
MOD = 1 << M_BITS


def inv(x):
    return pow(x % MOD, -1, MOD)


def fixed_point(mu, n):
    w = [1]
    while len(w) < n:
        w = [b for a in w for b in mu[a]]
    return w[:n]


def admissible(L):
    for m0 in product((0, 1), repeat=L):
        for m1 in product((0, 1), repeat=L):
            if m1[0] == 1 and m0 != m1 and sum(m0) == sum(m1):
                yield list(m0), list(m1)


def v2(x):
    x %= MOD
    if x == 0:
        return M_BITS
    return (x & -x).bit_length() - 1


def series_value(word, a, b):
    """sum_j word[j] (a/b)^j modulo 2^M, for a even and b odd."""
    z = a * inv(b) % MOD
    total, power = 0, 1
    for bit in word:
        if power == 0:
            break
        if bit:
            total = (total + power) % MOD
        power = power * z % MOD
    return total


def check_seed(m0, m1):
    L, r = len(m0), sum(m1)
    word = fixed_point({0: m0, 1: m1}, M_BITS + L)
    x, i = 0, 0
    for d, bit in enumerate(word[:M_BITS]):
        if bit:
            x = (x - (1 << d) * inv(3 ** (i + 1))) % MOD
            i += 1
    y = x
    for k in range(60):
        assert (y & 1) == word[k]
        y = (3 * y + 1) // 2 if y & 1 else y // 2

    def c(m):
        total, t = 0, 0
        for pos, bit in enumerate(m):
            if bit:
                total = (total + (1 << pos) * inv(3 ** (t + 1))) % MOD
                t += 1
        return total

    z0 = (1 << L) * inv(3 ** r) % MOD
    V = series_value(word, 1 << L, 3 ** r)
    c0, c1 = c(m0), c(m1)
    assert (c1 - c0) % MOD != 0
    assert (-c0 * inv(1 - z0) - (c1 - c0) * V) % MOD == x


def check_recursion(m0, m1, levels):
    L, r = len(m0), sum(m1)
    word = fixed_point({0: m0, 1: m1}, M_BITS + L)
    diff = [j for j in range(L) if m0[j] != m1[j]]
    s, e = diff[0], diff[-1]
    a, b = 1 << L, 3 ** r
    for _ in range(levels):
        if a.bit_length() > M_BITS // 2:
            break
        V = series_value(word, a, b)
        V_next = series_value(word, a ** L, b ** L)
        Q0 = sum(m0[j] * a ** j * b ** (L - 1 - j) for j in range(L))
        Gs = sum((m1[s + i] - m0[s + i]) * a ** i * b ** (e - s - i)
                 for i in range(e - s + 1))
        assert Gs % 2 == 1
        # V(z) (b^L - a^L) - b Q0 = a^s G* b^(-e) (b^L - a^L) V(z^L)
        lhs = (V * (b ** L - a ** L) - b * Q0) % MOD
        rhs = (a ** s * Gs * inv(b ** e) * (b ** L - a ** L) * V_next) % MOD
        assert lhs == rhs
        a, b = a ** L, b ** L


def rational_null_vector(rows, n):
    """A nonzero rational solution of rows . x = 0 with n > len(rows) unknowns."""
    mat = [[Fraction(v) for v in row] for row in rows]
    pivots, rank = [], 0
    for col in range(n):
        piv = next((i for i in range(rank, len(mat)) if mat[i][col] != 0), None)
        if piv is None:
            continue
        mat[rank], mat[piv] = mat[piv], mat[rank]
        pv = mat[rank][col]
        mat[rank] = [v / pv for v in mat[rank]]
        for i in range(len(mat)):
            if i != rank and mat[i][col] != 0:
                f = mat[i][col]
                mat[i] = [x - f * y for x, y in zip(mat[i], mat[rank])]
        pivots.append(col)
        rank += 1
    free = next(c for c in range(n) if c not in pivots)
    x = [Fraction(0)] * n
    x[free] = Fraction(1)
    for i, col in enumerate(pivots):
        x[col] = -mat[i][free]
    return x


def degree_pair(word, d):
    rows = [[word[n - j] if n >= j else 0 for j in range(d + 1)]
            for n in range(d + 1, 2 * d + 1)]
    x = rational_null_vector(rows, d + 1)
    den = 1
    for v in x:
        den = den * v.denominator // gcd(den, v.denominator)
    p1 = [int(v * den) for v in x]
    assert any(p1)
    p0 = [-sum(p1[j] * word[n - j] for j in range(n + 1)) for n in range(d + 1)]
    return p0, p1


def gcd(a, b):
    while b:
        a, b = b, a % b
    return a


def residual(p0, p1, word, n):
    d = len(p1) - 1
    base = p0[n] if n <= d else 0
    return base + sum(p1[j] * word[n - j] for j in range(min(d, n) + 1))


def check_certificate(m0, m1, d=6, levels=3):
    L, r = len(m0), sum(m1)
    word = fixed_point({0: m0, 1: m1}, 4000)
    p0, p1 = degree_pair(word, d)
    N = next(n for n in range(3000) if residual(p0, p1, word, n) != 0)
    assert N >= 2 * d + 1
    diff = [j for j in range(L) if m0[j] != m1[j]]
    e = diff[-1]
    m = max(2 ** L, 3 ** r)
    assert m ** (d * (L - 1) + L + e) < 2 ** (L * (L - 1) * N)
    lead = residual(p0, p1, word, N)
    val = (lead & -lead).bit_length() - 1
    long_word = fixed_point({0: m0, 1: m1}, M_BITS + L)
    a, b = 1 << L, 3 ** r
    for k in range(levels):
        expected = N * L ** (k + 1) + val
        if expected + 8 >= M_BITS:
            break
        z = a * inv(b) % MOD
        V = series_value(long_word, a, b)
        P0 = sum(cf * pow(z, j, MOD) for j, cf in enumerate(p0)) % MOD
        P1 = sum(cf * pow(z, j, MOD) for j, cf in enumerate(p1)) % MOD
        got = v2(P0 + P1 * V)
        if L ** (k + 1) > val:
            assert got == expected, (m0, m1, k, got, expected)
        else:
            assert got >= N * L ** (k + 1)
        a, b = a ** L, b ** L
    return N, val


def ledger_closes(d, L):
    r = e = L - 1
    m = max(2 ** L, 3 ** r)
    return m ** (d * (L - 1) + L + e) < 2 ** (L * (L - 1) * (2 * d + 1))


def ledger_closes_all(d, L):
    """All r, e < L.  The left side is monotone in r and e, so the case
    r = e = L - 1 decides; a few smaller r are also tested directly."""
    if not ledger_closes(d, L):
        return False
    for r in {0, 1, L // 2, max(L - 2, 0)}:
        if r >= L:
            continue
        m = max(2 ** L, 3 ** r)
        if not m ** (d * (L - 1) + L + (L - 1)) < 2 ** (L * (L - 1) * (2 * d + 1)):
            return False
    return True


def eventually_periodic_bounded(word, max_start, max_period):
    """True if some period p <= max_period holds from index max_start on.
    (A period that holds from an earlier index also holds from max_start.)"""
    n = len(word)
    tail = word[max_start:]
    return any(tail[p:] == tail[:n - max_start - p] for p in range(1, max_period + 1))


def main():
    count = 0
    stats = {}
    for L in range(2, 6):
        for m0, m1 in admissible(L):
            check_seed(m0, m1)
            check_recursion(m0, m1, 3)
            N, val = check_certificate(m0, m1)
            stats[(N, val)] = stats.get((N, val), 0) + 1
            word = fixed_point({0: m0, 1: m1}, 1500)
            assert not eventually_periodic_bounded(word, 60, 120)
            count += 1
    print(f"T1-T4, T6: {count} admissible substitutions with 2 <= L <= 5 passed")
    print("  largest first-residual order:", max(n for n, _ in stats),
          "; largest leading 2-adic valuation:", max(v for _, v in stats))
    tm_N, tm_val = check_certificate([0, 1], [1, 0])
    print(f"  Thue-Morse 10/01: N = {tm_N}, leading valuation = {tm_val}")

    for L in range(2, 401):
        assert ledger_closes_all(6, L)
    first_fail = []
    for d in range(6):
        L = 2
        while ledger_closes(d, L):
            L += 1
        first_fail.append(L)
    assert first_fail == [2, 2, 2, 7, 16, 101], first_fail
    print("T5: degree six closes for 2 <= L <= 400; degrees 0..5 first fail at", first_fail)

    alt = fixed_point({0: [0, 1, 0], 1: [1, 0, 1]}, 300)
    assert alt == [1 - (i % 2) for i in range(300)]
    y = 1
    for i in range(300):
        assert (y & 1) == alt[i]
        y = (3 * y + 1) // 2 if y & 1 else y // 2
    print("T6: unequal-weight control 101/010 is periodic and realised by the seed 1")
    print("all independent checks passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
