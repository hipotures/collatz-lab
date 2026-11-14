#!/usr/bin/env python3
"""Exact finite checks for research/mahler-generalization.md (issue #10, Gate B).

Standard library only, exact integer / rational arithmetic only, deterministic.
Run from the repository root:

    python3 research/mahler-family/verify_family.py

It rewrites research/mahler-family/evidence.json and summary.md byte for byte.

Everything here is a FINITE check (`verified-for-finite-domain`). The theorems in
research/mahler-generalization.md are proved by algebra in that file; this script
only guards the algebra against transcription errors and reproduces the bounded
Pade table. It proves nothing about any infinite statement.

Sections
  1. the family mu_L(1) = 1^(L-1) 0, mu_L(0) = 1^(L-2) 0 1 for 4 <= L <= 12
  2. the explicit case L = 5 (constants, checkpoints, periodic control, tower levels)
  3. the single bounded exact Pade search for L = 5, degree bound 1 <= m <= 16
  4. the identities behind the general criterion (Theorem B) on every admissible
     uniform morphism of length 2 <= L <= 5
"""

import json
import os
import sys
from fractions import Fraction
from functools import reduce
from itertools import product
from math import gcd

FAMILY_RANGE = range(4, 13)
MAX_PADE_DEGREE = 16
HERE = os.path.dirname(os.path.abspath(__file__))


# ----------------------------------------------------------------------------
# basic exact helpers
# ----------------------------------------------------------------------------

def v2(x):
    """2-adic valuation of a nonzero integer."""
    assert x != 0
    x = abs(x)
    count = 0
    while x % 2 == 0:
        x //= 2
        count += 1
    return count


def t_step(n):
    """Accelerated Collatz map on a non-negative integer."""
    return (3 * n + 1) // 2 if n & 1 else n // 2


def fixed_point(mu0, mu1, length):
    """Prefix of lim mu^j(1) obtained by literally iterating the substitution."""
    assert mu1[0] == 1
    word = [1]
    while len(word) < length:
        word = [s for b in word for s in (mu1 if b else mu0)]
    return word[:length]


def family_blocks(L):
    return [1] * (L - 2) + [0, 1], [1] * (L - 1) + [0]


def family_word_by_recurrence(L, length):
    """w(Ln+j) = 1 (j <= L-3), w(Ln+L-2) = w(n), w(Ln+L-1) = 1 - w(n)."""
    word = [0] * length
    for i in range(length):
        n, j = divmod(i, L)
        if j <= L - 3:
            word[i] = 1
        elif j == L - 2:
            word[i] = word[n]
        else:
            word[i] = 1 - word[n]
    return word


def block_offset(block):
    """c(v) with T^|v|(y) = (3^r y + c(v)) / 2^|v| along the parity block v."""
    c = 0
    for pos, bit in enumerate(block):
        if bit:
            c = 3 * c + (1 << pos)
    return c


def seed_by_parity_positions(word, bits):
    """-sum_i 2^(d_i) / 3^(i+1) mod 2^bits over the odd positions d_i < bits."""
    mod = 1 << bits
    inv3 = pow(3, -1, mod)
    total, inv3_pow = 0, 1
    for pos in range(bits):
        if word[pos]:
            inv3_pow = inv3_pow * inv3 % mod
            total = (total + (1 << pos) * inv3_pow) % mod
    return (-total) % mod


def seed_by_lifting(word, bits):
    """Bit-by-bit lift of the unique residue whose itinerary starts with word."""
    x = 0
    for k in range(1, bits + 1):
        for cand in (x, x + (1 << (k - 1))):
            y, ok = cand, True
            for j in range(k):
                if (y & 1) != word[j]:
                    ok = False
                    break
                y = t_step(y)
            if ok:
                x = cand
                break
        else:
            raise AssertionError("no lift")
    return x


def series_value(word, z, mod):
    """F(z) = sum_n w(n) z^n modulo a power of two, for even z."""
    total, z_pow = 0, 1
    for bit in word:
        if z_pow == 0:
            return total
        if bit:
            total = (total + z_pow) % mod
        z_pow = z_pow * z % mod
    raise AssertionError("word too short for the requested 2-adic precision")


def homogenise(coeffs, a, b, degree):
    """sum_j coeffs[j] a^j b^(degree-j)."""
    return sum(c * a ** j * b ** (degree - j) for j, c in enumerate(coeffs))


# ----------------------------------------------------------------------------
# tower / linear form identities for a uniform equal-weight morphism
# ----------------------------------------------------------------------------

def morphism_data(mu0, mu1):
    L = len(mu0)
    r = sum(mu1)
    assert len(mu1) == L and sum(mu0) == r and mu1[0] == 1 and mu0 != mu1
    diff = [x - y for x, y in zip(mu1, mu0)]
    s = next(j for j in range(L) if diff[j])
    e = max(j for j in range(L) if diff[j])
    t = mu1.index(0)
    A, B = 2 ** L, 3 ** r
    return dict(L=L, r=r, s=s, e=e, t=t, N=L * t + s, A=A, B=B, m=max(A, B),
                gstar=diff[s:e + 1], c0=block_offset(mu0), c1=block_offset(mu1))


def check_tower(mu0, mu1, levels):
    """Check, modulo a large power of two, every identity the proofs rely on.

    Returns the exact valuations v2(R(z_k)) for k < levels.
    """
    d = morphism_data(mu0, mu1)
    L, s, e, N, A, B = d["L"], d["s"], d["e"], d["N"], d["A"], d["B"]
    bits = N * L ** levels + 8 * L + 64
    mod = 1 << bits
    word = fixed_point(mu0, mu1, bits + 2 * L)

    # leading term of R(t) = Q_1(t) - (1 - t^L) F(t): exactly +-t^N
    period = [mu1[i % L] for i in range(N + L)]
    assert word[:N] == period[:N] and word[N] != period[N]
    r_coeff = [(mu1[n] if n < L else 0) - word[n] + (word[n - L] if n >= L else 0)
               for n in range(N + L)]
    assert all(c == 0 for c in r_coeff[:N]) and r_coeff[N] in (1, -1)

    # v2(c_0 - c_1) = s and the seed identity
    assert v2(d["c0"] - d["c1"]) == s
    kappa = (d["c0"] - d["c1"]) >> s
    z0 = A * pow(B, -1, mod) % mod
    f0 = series_value(word, z0, mod)
    seed_bits = min(bits - L, 384)
    seed = seed_by_parity_positions(word, seed_bits)
    lhs = ((B - A) * seed + d["c0"]) * B
    rhs = (B - A) * (d["c0"] - d["c1"]) * f0
    assert (lhs - rhs) % (1 << seed_bits) == 0

    a, b = A, B
    D = abs(B - A) * abs(kappa)          # D_0 for q = 1
    valuations = []
    for _ in range(levels):
        z = a * pow(b, -1, mod) % mod
        f = series_value(word, z, mod)
        z_next = pow(z, L, mod)
        f_next = series_value(word, z_next, mod)
        q0 = sum(pow(z, j, mod) for j in range(L) if mu0[j])
        q1 = sum(pow(z, j, mod) for j in range(L) if mu1[j])
        g = (q1 - q0) % mod
        # Mahler equation at z
        assert ((1 - z_next) * f - q0 - g * (1 - z_next) * f_next) % mod == 0
        # linear form
        rz = (q1 - (1 - z_next) * f) % mod
        val = v2(rz)
        assert val == N * v2(a), (mu0, mu1, val)
        valuations.append(val)
        # tower step: a^s sigma u_{k+1} = b^e Delta_k
        u = D * f % mod
        q0h = homogenise(mu0, a, b, L - 1)
        q1h = homogenise(mu1, a, b, L - 1)
        gstar_h = homogenise(d["gstar"], a, b, e - s)
        assert gstar_h % 2 != 0
        D_next = D * abs(gstar_h) * abs(b ** L - a ** L)
        sigma = 1 if gstar_h * (b ** L - a ** L) > 0 else -1
        u_next = D_next * f_next % mod
        delta = (b ** L - a ** L) * u - D * b * q0h
        assert (a ** s * sigma * u_next - b ** e * delta) % mod == 0
        # E_k = D_k b Q_1h - (b^L - a^L) u_k = D_k b^L R(z_k)
        E = (D * b * q1h - (b ** L - a ** L) * u) % mod
        assert (E - D * pow(b, L, mod) * rz) % mod == 0
        assert D % 2 == 1 and v2(E) == val
        a, b, D = a ** L, b ** L, D_next
    return d, valuations


def criterion_holds(d):
    """Theorem B hypothesis (C): 2^(L (L-1) N) > m^(L^2 + e)."""
    return 2 ** (d["L"] * (d["L"] - 1) * d["N"]) > d["m"] ** (d["L"] ** 2 + d["e"])


# ----------------------------------------------------------------------------
# 1. the family
# ----------------------------------------------------------------------------

def family_section():
    rows = []
    for L in FAMILY_RANGE:
        mu0, mu1 = family_blocks(L)
        length = 4096
        word = fixed_point(mu0, mu1, length)
        assert word == family_word_by_recurrence(L, length)
        pow3, pow2 = 1, 1
        for k in range(1, length + 1):
            pow2 *= 2
            if word[k - 1]:
                pow3 *= 3
            assert pow3 > pow2
        A, B = 2 ** L, 3 ** (L - 1)
        assert block_offset(mu1) == B - 2 ** (L - 1)
        assert block_offset(mu0) == B - 2 ** (L - 2)
        levels = 3 if L <= 5 else 2
        d, valuations = check_tower(mu0, mu1, levels)
        assert (d["s"], d["e"], d["t"], d["N"]) == (L - 2, L - 1, L - 1, L * L - 2)
        assert valuations == [(L * L - 2) * L ** (k + 1) for k in range(levels)]
        bits = 256
        seed = seed_by_parity_positions(word, bits)
        assert seed % (1 << 96) == seed_by_lifting(word, 96)
        # closed form x = -c_0/(B-A) + 2^(L-2)/B F(A/B) modulo 2^bits
        mod = 1 << bits
        f0 = series_value(word, A * pow(B, -1, mod) % mod, mod)
        formula = (-(B - 2 ** (L - 2)) * pow(B - A, -1, mod)
                   + 2 ** (L - 2) * pow(B, -1, mod) * f0) % mod
        assert formula == seed
        # the positive integer seed + 2^bits follows the prefix and grows
        n = seed + mod
        y = n
        for j in range(bits):
            assert (y & 1) == word[j]
            y = t_step(y)
        assert y > n
        gain, cost = L * (L * L - 2), L * L + L - 1
        assert 2 ** gain > 3 ** cost and criterion_holds(d)
        assert 5 * gain - 8 * cost == 5 * L ** 3 - 8 * L ** 2 - 18 * L + 8
        rows.append(dict(L=L, A=str(A), B=str(B), order_N=L * L - 2,
                         levels_checked=levels, valuations=valuations,
                         gain_exp2=gain, cost_exp3=cost,
                         seed_mod_2_64=str(seed % (1 << 64))))
    return rows


# ----------------------------------------------------------------------------
# 2. L = 5
# ----------------------------------------------------------------------------

def l5_section():
    L, A, B = 5, 32, 81
    mu0, mu1 = family_blocks(L)
    assert (mu1, mu0) == ([1, 1, 1, 1, 0], [1, 1, 1, 0, 1])
    assert (block_offset(mu1), block_offset(mu0), B - A) == (65, 73, 49)
    word = fixed_point(mu0, mu1, 8192)
    assert "".join(map(str, word[:30])) == "111101111011110111101110111110"
    checkpoints = []
    for bits in (20, 40, 80, 160, 320, 640, 1280):
        mod = 1 << bits
        seed = seed_by_parity_positions(word, bits)
        f0 = series_value(word, A * pow(B, -1, mod) % mod, mod)
        assert (3969 * seed + 5913 - 392 * f0) % mod == 0       # 81(49x+73) = 392 F
        assert (49 * seed + 73) % 8 == 0
        blocks = bits // L
        # block law: 32 g_{n+1} = 81 g_n - 392 w(n) with g_n = 49 T^(5n)(x) + 73
        n = seed + mod
        y = n
        ones = 0
        for j in range(bits):
            assert (y & 1) == word[j]
            ones += word[j]
            y = t_step(y)
        assert ones == 4 * blocks and y > n
        # periodic control (11110)^infinity <-> -65/49
        control = (-65 * pow(49, -1, mod)) % mod
        yc = control + mod
        first_divergence = None
        for j in range(bits + 2 * L):
            if (yc & 1) != (0 if j % L == L - 1 else 1):
                first_divergence = j
                break
            yc = t_step(yc)
        assert first_divergence is not None and first_divergence >= bits
        checkpoints.append(dict(bits=bits, seed=str(seed), odd_steps=ones,
                                control_seed=str(control + mod),
                                control_first_divergence=first_divergence))
    # tower constants
    a, b = A, B
    d1 = 49 * (b - a) * (b ** 5 - a ** 5)
    d1_uncancelled = d1 * a ** 3
    assert d1 % 2 == 1 and v2(d1_uncancelled) == 15
    _, valuations = check_tower(mu0, mu1, 3)
    assert valuations == [115, 575, 2875]
    assert 2 ** 115 > 2 ** 69 * 3 ** 29 and 2 ** 115 < 2 ** 70 * 3 ** 29
    # height constants used in the proof
    assert Fraction(3, 32 ** 3) + Fraction(1, 81 ** 3) < 1
    assert Fraction(1) / (1 - Fraction(32, 81)) == Fraction(81, 49) < 3
    return dict(A=A, B=B, c0=73, c1=65, B_minus_A=49, order_N=23,
                word_prefix_30="".join(map(str, word[:30])),
                checkpoints=checkpoints, d1=str(d1),
                v2_d1_uncancelled=15, valuations_k012=valuations,
                ledger="2^115 > 2^69 * 3^29")


# ----------------------------------------------------------------------------
# 3. bounded exact Pade search
# ----------------------------------------------------------------------------

def nullspace(rows, ncols):
    """Exact rational nullspace by Gauss-Jordan elimination."""
    mat = [[Fraction(x) for x in row] for row in rows]
    pivots, rank = [], 0
    for col in range(ncols):
        if rank == len(mat):
            break
        pivot = next((i for i in range(rank, len(mat)) if mat[i][col] != 0), None)
        if pivot is None:
            continue
        mat[rank], mat[pivot] = mat[pivot], mat[rank]
        inv = 1 / mat[rank][col]
        mat[rank] = [x * inv for x in mat[rank]]
        for i in range(len(mat)):
            if i != rank and mat[i][col] != 0:
                factor = mat[i][col]
                mat[i] = [x - factor * y for x, y in zip(mat[i], mat[rank])]
        pivots.append(col)
        rank += 1
    basis = []
    for free in (c for c in range(ncols) if c not in pivots):
        vec = [Fraction(0)] * ncols
        vec[free] = Fraction(1)
        for i, col in enumerate(pivots):
            vec[col] = -mat[i][free]
        basis.append(vec)
    return basis


def primitive(vec):
    den = reduce(lambda x, y: x * y // gcd(x, y), (v.denominator for v in vec), 1)
    ints = [int(v * den) for v in vec]
    g = reduce(gcd, (abs(v) for v in ints), 0)
    return [v // g for v in ints]


def pade_row(word, m, L):
    """Minimal-degree solution of p0 + p1 F = O(z^(2m+1)), deg p0, deg p1 <= m."""
    def rows(d):
        return [[word[n - i] for i in range(d + 1)] for n in range(m + 1, 2 * m + 1)]
    null_dim = len(nullspace(rows(m), m + 1))
    for d in range(m + 1):
        ns = nullspace(rows(d), d + 1)
        if ns:
            assert len(ns) == 1
            p1 = primitive(ns[0]) + [0] * (m - d)
            break
    p0 = [-sum(p1[i] * word[n - i] for i in range(n + 1)) for n in range(m + 1)]
    assert reduce(gcd, (abs(v) for v in p0 + p1), 0) == 1
    shift = 0
    while p0[shift] == 0 and p1[shift] == 0:
        shift += 1
    p0, p1 = p0[shift:], p1[shift:]
    while p0 and p0[-1] == 0:
        p0.pop()
    while p1 and p1[-1] == 0:
        p1.pop()
    if next(v for v in p1 if v) > 0:
        p0, p1 = [-v for v in p0], [-v for v in p1]
    degree = max(len(p0), len(p1)) - 1

    def coeff(n):
        base = p0[n] if n < len(p0) else 0
        return base + sum(p1[i] * word[n - i] for i in range(min(n, len(p1) - 1) + 1))
    order = next(n for n in range(len(word)) if coeff(n) != 0)
    assert order >= 2 * m + 1 - shift
    lead = coeff(order)
    gain, cost = L * order, (L - 1) * degree + 2 * L - 1
    return dict(m=m, null_dim=null_dim, shift=shift, reduced_degree=degree,
                p0=p0, p1=p1, order=order, leading_coeff=lead, v2_leading=v2(lead),
                l1=sum(abs(v) for v in p0 + p1), linf=max(abs(v) for v in p0 + p1),
                gain_exp2=gain, cost_exp3=cost, asymptotic_ledger_closes=2 ** gain > 3 ** cost)


def pade_section():
    L = 5
    word = fixed_point(*family_blocks(L), 4096)
    table = [pade_row(word, m, L) for m in range(1, MAX_PADE_DEGREE + 1)]
    row5 = table[4]
    assert (row5["p0"], row5["p1"]) == ([1, 1, 1, 1], [-1, 0, 0, 0, 0, 1])
    assert (row5["order"], row5["leading_coeff"], row5["reduced_degree"]) == (23, 1, 5)
    assert all(row["reduced_degree"] == 5 and row["order"] == 23 for row in table[4:])
    assert not table[0]["asymptotic_ledger_closes"]
    # control: the same routine reproduces the published L = 4 table of issue #7
    word4 = fixed_point(*family_blocks(4), 4096)
    control = [pade_row(word4, m, 4) for m in range(1, MAX_PADE_DEGREE + 1)]
    assert [(r["order"], r["leading_coeff"]) for r in control] == [
        (3, 1), (5, -2), (7, 3), (14, 1), (14, 1), (14, 1), (14, 1), (14, 1), (14, 1),
        (21, -11), (23, 34), (25, -1), (27, 227), (29, 299), (31, -960), (58, 1)]
    return table


# ----------------------------------------------------------------------------
# 4. general criterion (Theorem B): identities on all small admissible morphisms
# ----------------------------------------------------------------------------

def criterion_section():
    rows = []
    for L in range(2, 6):
        for mu1 in product((0, 1), repeat=L):
            if mu1[0] != 1:
                continue
            for mu0 in product((0, 1), repeat=L):
                if mu0 == mu1 or sum(mu0) != sum(mu1):
                    continue
                d, valuations = check_tower(list(mu0), list(mu1), 2)
                rows.append(dict(L=L, mu1="".join(map(str, mu1)), mu0="".join(map(str, mu0)),
                                 r=d["r"], t=d["t"], s=d["s"], e=d["e"], N=d["N"],
                                 supercritical=d["B"] > d["A"],
                                 criterion_holds=criterion_holds(d),
                                 valuations=valuations))
    return rows


# ----------------------------------------------------------------------------
# output
# ----------------------------------------------------------------------------

def poly(coeffs):
    terms = []
    for i, c in enumerate(coeffs):
        if c == 0:
            continue
        mag = "" if abs(c) == 1 and i > 0 else str(abs(c))
        var = "" if i == 0 else ("z" if i == 1 else f"z^{i}")
        terms.append(("-" if c < 0 else "+") + " " + mag + var)
    text = " ".join(terms).lstrip("+ ").strip()
    return text if text else "0"


def write_summary(evidence):
    lines = [
        "# Phase 5 generated summary: the family `mu_L` and the case `L = 5`",
        "",
        "Generated by `python3 research/mahler-family/verify_family.py`. Every row is an",
        "exact finite check (`verified-for-finite-domain`); the proofs are in",
        "[`../mahler-generalization.md`](../mahler-generalization.md).",
        "",
        "## Family `mu_L(1) = 1^(L-1) 0`, `mu_L(0) = 1^(L-2) 0 1`",
        "",
        "| L | A = 2^L | B = 3^(L-1) | N = L^2 - 2 | tower levels checked | v2(E_k) | ledger |",
        "|---|---|---|---|---|---|---|",
    ]
    for row in evidence["family"]:
        lines.append(
            f"| {row['L']} | {row['A']} | {row['B']} | {row['order_N']} | "
            f"{row['levels_checked']} | {', '.join(map(str, row['valuations']))} | "
            f"2^{row['gain_exp2']} > 3^{row['cost_exp3']} |")
    l5 = evidence["l5"]
    lines += [
        "",
        "## `L = 5` checkpoints",
        "",
        "`x_K` is the unique residue modulo `2^K` whose first `K` parities are `w_5`;",
        "`n = x_K + 2^K` is a positive integer with that prefix and `T^K(n) > n`.",
        "",
        "| K | odd steps | x_K mod 2^64 | control `-65/49` first divergence |",
        "|---|---|---|---|",
    ]
    for cp in l5["checkpoints"]:
        lines.append(f"| {cp['bits']} | {cp['odd_steps']} | {int(cp['seed']) % (1 << 64)} | "
                     f"{cp['control_first_divergence']} |")
    lines += [
        "",
        f"Cancelled `D_1 = {l5['d1']}` (odd); uncancelled `v2(D_1) = {l5['v2_d1_uncancelled']}`;",
        f"`v2(E_k)` for `k = 0, 1, 2`: {', '.join(map(str, l5['valuations_k012']))}.",
        "",
        "## Bounded exact Pade search for `L = 5`, `1 <= m <= 16`",
        "",
        "Asymptotic ledger: `2^(5 N)` against `3^(4 M + 9)`.",
        "",
        "| m | null dim | shift | M | N | c | v2(c) | L1 | reduced p0 | reduced p1 | ledger |",
        "|---|---|---|---|---|---|---|---|---|---|---|",
    ]
    for row in evidence["pade_l5"]:
        verdict = "closes" if row["asymptotic_ledger_closes"] else "**fails**"
        lines.append(
            f"| {row['m']} | {row['null_dim']} | {row['shift']} | {row['reduced_degree']} | "
            f"{row['order']} | {row['leading_coeff']} | {row['v2_leading']} | {row['l1']} | "
            f"`{poly(row['p0'])}` | `{poly(row['p1'])}` | "
            f"2^{row['gain_exp2']} vs 3^{row['cost_exp3']}: {verdict} |")
    crit = evidence["criterion"]
    lines += [
        "",
        "## General criterion: admissible morphisms with `2 <= L <= 5`",
        "",
        "Admissible: `mu(1)` starts with `1`, `mu(0) != mu(1)`, equal number of ones.",
        "The identities of the proof were checked on all of them at tower levels 0 and 1;",
        "the last column counts those satisfying the sufficient inequality (C).",
        "",
        "| L | admissible morphisms | identities checked | criterion (C) holds |",
        "|---|---|---|---|",
    ]
    for L in range(2, 6):
        sub = [r for r in crit if r["L"] == L]
        lines.append(f"| {L} | {len(sub)} | {len(sub)} | {sum(r['criterion_holds'] for r in sub)} |")
    lines += ["", "Morphisms with `L <= 4` satisfying (C):", ""]
    for r in crit:
        if r["L"] <= 4 and r["criterion_holds"]:
            lines.append(f"- `1 -> {r['mu1']}`, `0 -> {r['mu0']}` "
                         f"(`t = {r['t']}`, `s = {r['s']}`, `e = {r['e']}`, `N = {r['N']}`)")
    lines.append("")
    return "\n".join(lines)


def main():
    evidence = dict(
        schema="collatz-lab-mahler-family-v1",
        status="verified-for-finite-domain",
        family=family_section(),
        l5=l5_section(),
        pade_l5=pade_section(),
        criterion=criterion_section(),
    )
    with open(os.path.join(HERE, "evidence.json"), "w", encoding="utf-8") as fh:
        json.dump(evidence, fh, indent=1, sort_keys=True)
        fh.write("\n")
    with open(os.path.join(HERE, "summary.md"), "w", encoding="utf-8") as fh:
        fh.write(write_summary(evidence))
    crit = evidence["criterion"]
    print(f"family rows: {len(evidence['family'])}; Pade rows: {len(evidence['pade_l5'])}; "
          f"admissible morphisms checked: {len(crit)}; "
          f"criterion holds for {sum(r['criterion_holds'] for r in crit)}")
    print("all exact finite checks passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
