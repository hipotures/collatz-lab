#!/usr/bin/env python3
"""Reproduce finite Phase 12 evidence. Universal proofs are in Lean/the report.

Uses only the Python standard library and no existing repository verifier.
Run --check to compare the complete deterministic record with evidence.json.
Run --write only when intentionally updating that reviewed record.
"""

import argparse
from collections import deque
from fractions import Fraction
import hashlib
from itertools import product
import json
from pathlib import Path


IMAGES = {48: b"111110", 49: b"100111"}


def expand(xs):
    return b"".join(IMAGES[b] for b in xs)


def literal_prefix(n):
    xs = b"1"
    while len(xs) < n:
        xs = expand(xs)
    return xs[:n]


def indexed(n):
    if n == 0:
        return 1
    parent, col = divmod(n, 6)
    if col in (0, 3, 4):
        return 1
    return (1 - indexed(parent)) if col in (1, 2) else indexed(parent)


def affine(xs):
    """Closed sum over one positions; independent of the offset recurrence."""
    positions = [j for j, b in enumerate(xs) if b == 49]
    r = len(positions)
    c = sum(2**j * 3 ** (r - i - 1) for i, j in enumerate(positions))
    return 2 ** len(xs) - 3**r, c, r


def orbit(p, q, n):
    assert q % 2 == 1
    states, bits = [p], []
    for _ in range(n):
        bit = p % 2
        bits.append(48 + bit)
        numerator = 3 * p + q if bit else p
        assert numerator % 2 == 0
        p = numerator // 2
        states.append(p)
    return bytes(bits), states


def lift(xs, q):
    """Integer in the unique residue class, then center it for q != 1."""
    _, c, r = affine(xs)
    mod = 2 ** len(xs)
    p = (-c * q * pow(3**r, -1, mod)) % mod
    return p if q == 1 else p - mod


def lcp_at(xs, m):
    ell = 0
    while m + ell < len(xs) and xs[m + ell] == xs[ell]:
        ell += 1
    return ell


def z_values(xs):
    z = [0] * len(xs)
    left = right = 0
    for m in range(1, len(xs)):
        if m < right:
            z[m] = min(right - m, z[m - left])
        while m + z[m] < len(xs) and xs[m + z[m]] == xs[z[m]]:
            z[m] += 1
        if m + z[m] > right:
            left, right = m, m + z[m]
    return z


def closed_language(xs, n):
    """Least closure under all six child offsets, retaining occurrence witnesses.

    If a row occurs at a, its child occurs at 6a+r. Conversely each positive
    start descends to floor(a/6)<a. These two induction arguments, not prefix
    saturation, establish exactness of the returned finite global language.
    """
    seen = {xs[:n]: 0}
    todo = deque(seen)
    while todo:
        row = todo.popleft()
        expanded = expand(row)
        for r in range(6):
            child = expanded[r : r + n]
            assert len(child) == n
            if child not in seen:
                seen[child] = 6 * seen[row] + r
                todo.append(child)
    for row, a in seen.items():
        assert row == bytes(48 + indexed(a + j) for j in range(n))
    return seen


def exhaustive_returns():
    words = pairs = nonzero = zero = extra_bit_failures = overlaps = 0
    for n in range(10):
        for letters in product((48, 49), repeat=n):
            xs = bytes(letters)
            words += 1
            forms = [affine(xs[:m]) for m in range(n + 1)]
            # Include all partial/overlapping matches, empty matches and m=0.
            returns = [(m, ell) for m in range(n + 1)
                       for ell in range(lcp_at(xs, m) + 1)]
            for m, ell in returns:
                for k, f in returns:
                    pairs += 1
                    a, c, _ = forms[m]
                    b, d, _ = forms[k]
                    det = a * d - b * c
                    mod = 2 ** min(m + ell, k + f)
                    assert det % mod == 0
                    assert det == 0 or abs(det) >= mod
                    if ell > m > 0 or f > k > 0:
                        overlaps += 1
                    if det:
                        nonzero += 1
                        extra_bit_failures += det % (2 * mod) != 0
                    else:
                        zero += 1
    assert extra_bit_failures > 0 and overlaps > 0
    # False match: 10 does not return at position 1; determinant -2 is not 0 mod 4.
    a, c, _ = affine(b"1")
    b, d, _ = affine(b"10")
    assert a * d - b * c == -2
    assert (a * d - b * c) % 4 != 0
    # Dropping odd q from the *forms cancellation* lemma fails: p=0,q=4,K=2.
    assert (a * 0 - c * 4) % 4 == (b * 0 - d * 4) % 4 == 0
    return dict(words=words, return_pairs=pairs, nonzero=nonzero, zero=zero,
                overlapping_pairs=overlaps, extra_precision_counterexamples=extra_bit_failures,
                malformed_match_determinant=-2, even_denominator_counterexample=True)


def signed_checks():
    witnesses = form_checks = 0
    for n in range(1, 8):
        for letters in product((48, 49), repeat=n):
            xs = bytes(letters)
            for q in (1, 5, -5, 15):
                p = lift(xs, q)
                bits, states = orbit(p, q, n)
                assert bits == xs
                assert orbit(-p, -q, n)[1] == [-y for y in states]
                assert orbit(3 * p, 3 * q, n)[1] == [3 * y for y in states]
                witnesses += 1
                for m in range(n + 1):
                    a, c, r = affine(xs[:m])
                    # Check the closed affine sum against a separate recurrence.
                    offset = 0
                    for j, bit in enumerate(xs[:m]):
                        if bit == 49:
                            offset = 3 * offset + 2**j
                    assert c == offset
                    assert 2**m * states[m] == 3**r * p + c * q
                    ell = lcp_at(xs, m)
                    e = a * p - c * q
                    assert e == 2**m * (p - states[m])
                    assert e % (2 ** (m + ell)) == 0
                    for k in range(n + 1):
                        b, d, _ = affine(xs[:k])
                        f = b * p - d * q
                        assert b * e - a * f == (a * d - b * c) * q
                    form_checks += 1
    for p, q, expected in [(1, 1, b"10" * 60), (-1, 1, b"1" * 120),
                            (-1, -1, b"10" * 60), (1, -1, b"1" * 120)]:
        assert orbit(p, q, 120)[0] == expected
        for m in (2, 4, 10):
            a, c, _ = affine(expected[:m])
            b, d, _ = affine(expected[:2 * m])
            assert a * d - b * c == 0
    control = b"1"
    while len(control) < 120:
        control = b"".join(b"101" if b == 49 else b"010" for b in control)
    assert control[:120] == b"10" * 60
    return dict(signed_witnesses=witnesses, form_checks=form_checks,
                controls="101/010 at 1/1; all-one at -1/1; signed and unreduced")


def candidate_checks():
    xs = literal_prefix(60000)
    assert xs == bytes(48 + indexed(n) for n in range(len(xs)))
    counts = [0]
    for b in xs:
        counts.append(counts[-1] + (b == 49))
    k = 0
    for n, r in enumerate(counts):
        while n >= 6**k:
            k += 1
        assert abs(7 * r - 5 * n) <= 10 * k
    for n in range((len(xs) - 6) // 6):
        assert counts[6 * n + 6] == 5 * (n + 1) - counts[n + 1]
    power_rows = []
    images = {0: b"0", 1: b"1"}
    for k in range(6):
        for b, row in images.items():
            r = row.count(49)
            assert 7 * r == 5 * 6**k + (-1)**k * (7 * b - 5)
            power_rows.append([k, b, r])
        images = {b: expand(row) for b, row in images.items()}
    z = z_values(xs)
    best = Fraction(0)
    best_m = None
    for m in range(1, 7500):
        ell = z[m]
        assert m + ell < len(xs)  # a real next mismatch, not a truncated scan
        assert ell == lcp_at(xs, m)
        parent, col = divmod(m, 6)
        b = indexed(parent)
        predicted = (6 * z[parent] + 1 if col == 0 else
                     (1 - b) if col in (1, 2) else
                     1 if col == 3 else 2 - b if col == 4 else b)
        assert ell == predicted
        assert 5 * ell + 1 <= 2 * m
        ratio = Fraction(2 ** (ell + counts[m]), 3 ** counts[m])
        if ratio > best:
            best, best_m = ratio, m
    languages = []
    for n in (2, 6, 36, 216, 864):
        language = closed_language(xs, n)
        observed = {xs[a : a + n] for a in range(len(xs) - n + 1)}
        assert observed == language.keys()
        languages.append(dict(length=n, observed_60000=len(observed), global_count=len(language),
                              sha256=hashlib.sha256(b"".join(sorted(language))).hexdigest()))
    assert [row['observed_60000'] for row in languages[-2:]] == [724, 2676]
    # Known-method reduction: true level-two weights and exact expanding growth gap.
    block_weights = [expand(expand(bytes([b]))).count(49) for b in (48, 49)]
    assert block_weights == [25, 26]
    assert 2**36 < 3**26 and 3**26 < 2**45
    assert 2**7 < 3**5 and 3**20 < 2**35
    prefix = xs[:81]
    witnesses = []
    for q in (1, 5, 15):
        p = 3 * lift(prefix, 5) if q == 15 else lift(prefix, q)
        bits, states = orbit(p, q, len(prefix))
        assert bits == prefix
        witnesses.append(dict(p=str(p), q=q, end=str(states[-1])))
    return dict(prefix_length=len(xs), prefix_sha256=hashlib.sha256(xs).hexdigest(),
                weights=[4, 5], incidence=[[1, 2], [5, 4]], eigenvalues=[6, -1],
                power_rows=power_rows, languages=languages, shifts_scanned=7499,
                positive_returns=sum(z[m] > 0 for m in range(1, 7500)),
                largest_match=max(z[1:7500]), best_weight_ratio=str(best), best_shift=best_m,
                scale_returns=[[3 * 6**k, (6**(k+1) - 1) // 5] for k in range(5)],
                level_two_weights=block_weights, known_collision_gap=[str(2**45), str(3**26)],
                finite_81_bit_witnesses=witnesses)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = dict(evidence_kind="finite exact checks; see Lean/report for universal proofs",
                  exhaustive=exhaustive_returns(), signed=signed_checks(), candidate=candidate_checks())
    rendered = json.dumps(result, indent=2, sort_keys=True) + '\n'
    path = Path(__file__).with_name('evidence.json')
    if args.check:
        assert path.read_text() == rendered, 'Phase 12 evidence differs; inspect before updating'
        print('Phase 12 finite evidence matches evidence.json; all assertions passed')
    elif args.write:
        path.write_text(rendered)
        print('Wrote Phase 12 finite evidence after all assertions passed')
    else:
        print(rendered, end='')


if __name__ == '__main__':
    main()
