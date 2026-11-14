#!/usr/bin/env python3
"""Issue #26: independent finite checks, using only Python's standard library.

Run: python3 research/phase12/referee_checks.py
No imports, evidence files, or arithmetic routines from the reviewed project.
Assertions test finite instances; universal proofs are in the referee report.
"""

from collections import deque
from fractions import Fraction
from hashlib import sha256
from itertools import product
import json


IMAGES = (bytes((1, 1, 1, 1, 1, 0)), bytes((1, 0, 0, 1, 1, 1)))


def substitute(bits):
    return b"".join(IMAGES[b] for b in bits)


def indexed(n):
    """Evaluate base-six digits from the root, independently of substitution."""
    digits = []
    while n:
        n, r = divmod(n, 6)
        digits.append(r)
    b = 1
    for r in reversed(digits):
        b = IMAGES[b][r]
    return b


def coefficients(bits):
    """Closed sum over odd positions, rather than the project's recursion."""
    positions = [j for j, b in enumerate(bits) if b]
    r = len(positions)
    c = sum((1 << j) * 3 ** (r - i - 1) for i, j in enumerate(positions))
    return r, c, (1 << len(bits)) - 3**r


def rational_orbit(p, q, length):
    """Evaluate T on reduced Fractions, including sign normalization."""
    x = Fraction(p, q)
    assert x.denominator % 2 == 1
    bits, states = [], [x]
    for _ in range(length):
        b = x.numerator % 2
        bits.append(b)
        x = (3 * x + 1) / 2 if b else x / 2
        states.append(x)
    return bytes(bits), states


def inverse_zero_tail(bits):
    p, q = 0, 1
    for b in reversed(bits):
        p, q = (2 * p - q, 3 * q) if b else (2 * p, q)
    return p, q


def z_array(bits):
    """Exact common prefix lengths at every shift; linear-time string scan."""
    z = [0] * len(bits)
    left = right = 0
    for i in range(1, len(bits)):
        if i <= right:
            z[i] = min(right - i + 1, z[i - left])
        while i + z[i] < len(bits) and bits[z[i]] == bits[i + z[i]]:
            z[i] += 1
        if i + z[i] - 1 > right:
            left, right = i, i + z[i] - 1
    return z


def finite_compatibility():
    words = pairs = overlap = nonzero = extra_fail = signed = forms = 0
    smallest = smallest_one = None
    for length in range(10):
        for values in product((0, 1), repeat=length):
            bits = bytes(values)
            words += 1
            data = [coefficients(bits[:m]) for m in range(length + 1)]
            # Each finite word really reaches zero, rather than merely solving
            # a modular equation. Check signed and unreduced representations.
            p, q = inverse_zero_tail(bits)
            assert q > 0 and q % 2 == 1
            assert rational_orbit(p, q, length + 4)[0] == bits + bytes(4)
            for scale in (-3, -1, 1, 3):
                got, states = rational_orbit(scale * p, scale * q, length + 4)
                assert got == bits + bytes(4)
                signed += 1
                for m, (r, c, a) in enumerate(data):
                    numerator = states[m] * (scale * q)
                    assert numerator.denominator == 1
                    assert (1 << m) * numerator == 3**r * (scale * p) + c * (scale * q)
                    assert a * (scale * p) - c * (scale * q) == (1 << m) * (scale * p - numerator)
                    forms += 1
            # A different witness with each of several signed denominators.
            r, c, _ = data[-1]
            modulus = 1 << length
            for denom in (-15, -5, -1, 1, 5, 15):
                residue = (-c * denom * pow(3**r, -1, modulus)) % modulus
                for numerator in (residue, residue - modulus):
                    got, _ = rational_orbit(numerator, denom, length)
                    assert got == bits
                    signed += 1
            matches = []
            for m in range(length + 1):
                limit = 0
                while m + limit < length and bits[m + limit] == bits[limit]:
                    limit += 1
                matches.extend((m, ell) for ell in range(limit + 1))
            for m, ell in matches:
                _, cm, am = data[m]
                for n, f in matches:
                    _, cn, an = data[n]
                    det = am * cn - an * cm
                    k = min(m + ell, n + f)
                    bound = 1 << k
                    assert det % bound == 0
                    assert (abs(det) < bound) == (det == 0)
                    # Elimination checked at a signed, noncanonical witness.
                    em, en = am * p - cm * q, an * p - cn * q
                    assert an * em - am * en == det * q
                    pairs += 1
                    overlap += (ell > m > 0 or f > n > 0)
                    nonzero += det != 0
                    if det % (2 * bound):
                        extra_fail += 1
                        if 0 < m < n and ell > 0 and f > 0:
                            witness = dict(word="".join(map(str, values)), m=m, n=n,
                                           ell=ell, f=f, determinant=det, exponent=k)
                            if smallest is None:
                                smallest = witness
                            if values[0] == 1 and smallest_one is None:
                                smallest_one = witness
    # False actual-match premise: 101 has a true return at 2 but not at 1.
    _, cm, am = coefficients(bytes((1,)))
    _, cn, an = coefficients(bytes((1, 0)))
    det = am * cn - an * cm
    assert det == -2 and det % 4 != 0
    # Oddness is indispensable for the forms lemma. Both forms are -4.
    assert (am * 0 - cm * 4, an * 0 - cn * 4) == (-4, -4)
    # Positive periodic and negative fixed-point controls must survive.
    assert rational_orbit(1, 1, 120)[0] == bytes((1, 0)) * 60
    alt = b"\x01"
    for _ in range(5):
        alt = b"".join(bytes((1, 0, 1)) if b else bytes((0, 1, 0)) for b in alt)
    assert alt == (bytes((1, 0)) * ((len(alt) + 1) // 2))[:len(alt)]
    assert rational_orbit(-1, 1, 120)[0] == bytes((1,)) * 120
    assert rational_orbit(1, -1, 120)[0] == bytes((1,)) * 120
    assert rational_orbit(-3, 3, 120)[0] == bytes((1,)) * 120
    assert smallest and smallest_one
    return dict(words=words, ordered_return_pairs=pairs, overlapping_pairs=overlap,
                nonzero=nonzero, zero=pairs - nonzero, extra_bit_failures=extra_fail,
                signed_witnesses=signed, affine_form_checks=forms,
                smallest_nonempty_distinct_positive_returns=smallest,
                smallest_starting_one=smallest_one,
                false_match_and_even_denominator_controls="det=-2; modulus=4")


def candidate_checks():
    bits = bytes((1,))
    power = [bytes((0,)), bytes((1,))]
    counts = []
    level_checks = return_checks = 0
    for k in range(8):
        assert len(bits) == 6**k
        assert all(indexed(j) == b for j, b in enumerate(bits))
        z = z_array(bits)
        for m in range(1, len(bits)):
            assert 5 * z[m] + 1 <= 2 * m
            if m < 40:  # Cross-check the Z implementation with direct slicing.
                assert bits[:z[m]] == bits[m:m + z[m]]
                if m + z[m] < len(bits):
                    assert bits[z[m]] != bits[m + z[m]]
            return_checks += 1
        for b in (0, 1):
            weight = sum(power[b])
            assert 7 * weight == 5 * 6**k + (-1)**k * (7 * b - 5)
            counts.append([k, b, weight])
        level_checks += 1
        if k < 7:
            bits = substitute(bits)
            power = [substitute(row) for row in power]
    z = z_array(bits)
    weights = [0]
    for j, b in enumerate(bits):
        weights.append(weights[-1] + b)
        n, k = j + 1, 0
        while n >= 6**k:
            k += 1
        assert abs(7 * weights[-1] - 5 * n) <= 10 * k
    for m in range(1, len(bits)):
        n, r = divmod(m, 6)
        predicted = (6 * z[n] + 1 if r == 0 else
                     (1 - bits[n] if r in (1, 2) else
                      (1 if r == 3 else (2 - bits[n] if r == 4 else bits[n]))))
        assert z[m] == min(predicted, len(bits) - m)
    # Boundary values and strictness: increasing +1 to +2 is false.
    equality = []
    for k in range(6):
        m, ell = 3 * 6**k, (6**(k + 1) - 1) // 5
        assert z[m] == ell and 5 * ell + 1 == 2 * m
        equality.append([m, ell])
    for n in range(len(bits) // 6):
        b = bits[n]
        assert bits[6 * n:6 * n + 6] == bytes((1, 1 - b, 1 - b, 1, 1, b))
        for t in range(7):
            assert weights[6 * n + t] == 5 * n - weights[n] + sum(IMAGES[b][:t])
    # Arbitrarily located windows (finite sample), checking the independently
    # proved uniform estimate after decomposition into aligned S-blocks.
    window_checks = 0
    for k in range(6):
        s = 6**k
        for start in (0, 1, 5, 6, 7, 35, 36, 71, 215, 864, 9999):
            for length in (0, 1, 2, 5, 6, 7, 81, 216, 864, 7777):
                w = weights[start + length] - weights[start]
                assert abs(7 * w - 5 * length) <= Fraction(5 * length, s) + 10 * s
                window_checks += 1
    witnesses = []
    for p, q, end in (
        (553314936599421495781373, 1, 119765852333396201932225031),
        (-2069128595461409219917839, 5, -447866004387740064765897887),
        (-6207385786384227659753517, 15, -1343598013163220194297693661),
    ):
        for scale in (1, -1, 3):
            got, states = rational_orbit(scale * p, scale * q, 81)
            assert got == bits[:81]
            assert states[-1] * (scale * q) == scale * end
        witnesses.append(dict(p=str(p), q=q, end=str(end)))
    assert 3**5 > 2**7 and 3**20 < 2**35 and 3**25 > 2**39
    assert 2**45 > 3**26
    return bits, dict(levels=level_checks, indexed_symbols=len(bits),
                      maximal_return_checks=return_checks, power_counts=counts,
                      equality_returns=equality, uniform_window_checks=window_checks,
                      signed_81_step_witnesses=witnesses,
                      prefix_60000_sha256=sha256(bits[:60000]).hexdigest())


def language_checks(bits):
    rows = []
    for length in (2, 6, 36, 216, 864):
        seen = {bits[:length]: 0}
        todo = deque(seen)
        while todo:
            factor = todo.popleft()
            expanded = substitute(factor)
            for r in range(6):
                child = expanded[r:r + length]
                assert len(child) == length
                if child not in seen:
                    seen[child] = 6 * seen[factor] + r
                    todo.append(child)
        # Occurrence certification uses an independent base-six evaluation.
        for factor, start in seen.items():
            actual = (bits[start:start + length] if start + length <= len(bits) else
                      bytes(indexed(start + j) for j in range(length)))
            assert factor == actual
        observed = {bits[j:j + length] for j in range(60000 - length + 1)}
        assert observed == set(seen)
        if length in (6, 36, 216):
            assert len(seen) <= 4 * length
        digest = sha256(b"".join(sorted(seen))).hexdigest()
        rows.append(dict(length=length, global_closure_count=len(seen),
                         observed_60000=len(observed), sha256=digest,
                         maximum_witness_start=max(seen.values())))
    assert [row["global_closure_count"] for row in rows] == [4, 17, 118, 724, 2676]
    return rows


def main():
    compatibility = finite_compatibility()
    bits, candidate = candidate_checks()
    result = dict(evidence="independent finite exact checks; not universal proofs",
                  compatibility=compatibility, candidate=candidate,
                  factor_languages=language_checks(bits))
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
