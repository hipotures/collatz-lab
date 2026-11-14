#!/usr/bin/env python3
"""Bounded exact Phase 7 certificates. No infinite claim follows from this file.

Standard library only. Rewrites evidence.json deterministically. Degrees 1--24;
no extension is needed because small, unit-leading pairs already close ledgers.
Rust independently checks every polynomial pair and both residue formulae.
"""

import argparse
import json
from fractions import Fraction
from functools import reduce
from math import gcd, lcm
from pathlib import Path


def fixed_point(zero, one, length):
    word = [1]
    while len(word) < length:
        word = [a for b in word for a in (one if b else zero)]
    return word[:length]


def nullspace(rows, width):
    matrix = [[Fraction(a) for a in row] for row in rows]
    pivots = []
    for col in range(width):
        pivot = next((i for i in range(len(pivots), len(matrix)) if matrix[i][col]), None)
        if pivot is None:
            continue
        rank = len(pivots)
        matrix[rank], matrix[pivot] = matrix[pivot], matrix[rank]
        scale = matrix[rank][col]
        matrix[rank] = [a / scale for a in matrix[rank]]
        for i in range(len(matrix)):
            if i != rank:
                scale = matrix[i][col]
                matrix[i] = [a - scale * b for a, b in zip(matrix[i], matrix[rank])]
        pivots.append(col)
    basis = []
    for col in range(width):
        if col not in pivots:
            vec = [Fraction(0)] * width
            vec[col] = 1
            for i, pivot in enumerate(pivots):
                vec[pivot] = -matrix[i][col]
            basis.append(vec)
    return basis


def valuation(n):
    assert n
    n = abs(n)
    return (n & -n).bit_length() - 1


def approximant(word, degree, L, e, m):
    for d in range(degree + 1):
        rows = [[word[n - j] for j in range(d + 1)] for n in range(degree + 1, 2 * degree + 1)]
        basis = nullspace(rows, d + 1)
        if basis:
            assert len(basis) == 1
            denominator = reduce(lcm, (a.denominator for a in basis[0]), 1)
            p1 = [int(a * denominator) for a in basis[0]]
            break
    p0 = [-sum(p1[j] * word[n - j] for j in range(min(n, d) + 1))
          for n in range(degree + 1)]
    shift = 0
    while p0[0] == p1[0] == 0:
        p0.pop(0)
        p1.pop(0)
        shift += 1
    while p0[-1] == 0:
        p0.pop()
    while p1[-1] == 0:
        p1.pop()
    content = reduce(gcd, map(abs, p0 + p1))
    sign = -1 if next(a for a in p1 if a) > 0 else 1
    p0 = [sign * a // content for a in p0]
    p1 = [sign * a // content for a in p1]
    M = max(len(p0), len(p1)) - 1
    coefficients = [(p0[n] if n < len(p0) else 0) +
                    sum(p1[j] * word[n - j] for j in range(min(n, len(p1) - 1) + 1))
                    for n in range(512)]
    N = next(n for n, a in enumerate(coefficients) if a)
    c = coefficients[N]
    gain, cost = L * (L - 1) * N, (L - 1) * M + L + e
    return dict(search_degree=degree, common_shift_removed=shift, p0=p0, p1=p1,
                degree=M, order=N, leading_coefficient=c, v2_leading=valuation(c),
                norm_l1=sum(map(abs, p0 + p1)), gain_exp2=gain, cost_exp_m=cost,
                ledger_closes=2**gain > m**cost)


def offset(block):
    c = 0
    for j, bit in enumerate(block):
        if bit:
            c = 3 * c + 2**j
    return c


def target(name, zero, one):
    L, r = len(one), sum(one)
    A, B = 2**L, 3**r
    c0, c1 = offset(zero), offset(one)
    diff = [j for j in range(L) if zero[j] != one[j]]
    s, e, t = min(diff), max(diff), one.index(0)
    N = L * t + s
    word = fixed_point(zero, one, 4096)
    table = [approximant(word, degree, L, e, max(A, B)) for degree in range(1, 25)]
    checkpoints = []
    for bits in (32, 64, 128, 256):
        mod = 2**bits
        # The inverse parity-position sum is independent of the Mahler identity.
        seed, rank = 0, 0
        for j, bit in enumerate(word[:bits]):
            if bit:
                rank += 1
                seed = (seed - 2**j * pow(3**rank, -1, mod)) % mod
        z = A * pow(B, -1, mod) % mod
        f = sum(bit * pow(z, j, mod) for j, bit in enumerate(word[:bits])) % mod
        assert (B * ((B - A) * seed + c0) - (B - A) * (c0 - c1) * f) % mod == 0
        y = seed
        for j in range(bits):
            assert y % 2 == word[j]
            y = y // 2 if not (y & 1) else (3 * y + 1) // 2
        checkpoints.append(dict(bits=bits, seed=str(seed), terminal_numerator=str(y)))
    # Adversarial finite search; every candidate uses the actual signed map.
    checked = 0
    for q in range(1, 32, 2):
        for p in range(-512, 513):
            y = p
            for j in range(64):
                if y % 2 != word[j]:
                    break
                y = y // 2 if y % 2 == 0 else (3 * y + q) // 2
            else:
                raise AssertionError((name, p, q, "unexpected 64-symbol match"))
            checked += 1
    return dict(name=name, zero=zero, one=one, L=L, r=r, A=A, B=B,
                c0=c0, c1=c1, t=t, s=s, e=e, periodic_order=N,
                criterion_holds=2**(L * (L - 1) * N) > max(A, B)**(L * L + e),
                tower_height_exponent=L + e, checkpoints=checkpoints, pade=table,
                finite_falsification=dict(p_min=-512, p_max=512, q_max=31,
                                         prefix_length=64, candidates=checked, matches=0))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="compare committed evidence without rewriting it")
    args = parser.parse_args()
    targets = [target("thue-morse", [0, 1], [1, 0]),
               target("secondary", [0, 1, 1], [1, 0, 1])]
    assert targets[0]["pade"][2]["p0"] == [1, 0, -1]
    assert targets[0]["pade"][2]["p1"] == [-1, 0, 1, 1]
    assert targets[1]["pade"][1]["p0"] == [1]
    assert targets[1]["pade"][1]["p1"] == [-1, 0, 1]
    evidence = dict(schema="collatz-lab-uncovered-v1", status="verified-for-finite-domain",
                    coefficient_check_length=512, max_search_degree=24, targets=targets)
    path = Path(__file__).with_name("evidence.json")
    rendered = json.dumps(evidence, sort_keys=True, indent=2) + "\n"
    if args.check:
        assert path.read_text() == rendered, "committed evidence is stale"
    else:
        path.write_text(rendered)
    print("48 exact Pade rows; 8 modular checkpoints; 32800 signed rational candidates; all checks passed")


if __name__ == "__main__":
    main()
