#!/usr/bin/env python3
"""Independent bounded witness and no-smaller-height certificate verifier.

Imports no project implementation or optimizer. Literal substitution and
reverse inverse branches independently reconstruct the requested cylinder.
Python exact arithmetic and the written box-exclusion identities are the trust
boundary; these computations are not Lean-kernel proofs or asymptotic results.
"""

import argparse
import hashlib
import json
from math import gcd
from pathlib import Path
import signal


ROOT = Path(__file__).resolve().parent
MAX_BITS = 600000
MAX_FILE_BYTES = 8 * 1024 * 1024
MAX_COEFFICIENT_BOUND = 4095


def integer(value):
    if type(value) is int:
        return value
    assert isinstance(value, str) and len(value) <= 4 * MAX_BITS
    decoded = int(value, 16)
    assert hex(decoded) == value, "noncanonical integer"
    return decoded


def literal_prefix(n):
    word = "1"
    while len(word) < n:
        word = "".join("100111" if b == "1" else "111110" for b in word)
    return bytearray(int(b) for b in word[:n])


def inverse_residue(bits):
    # Reverse exact rational branches without Fraction reductions. This is
    # deliberately different from the producer's forward affine offset tree.
    numerator, denominator = 0, 1
    for bit in reversed(bits):
        numerator *= 2
        if bit:
            numerator -= denominator
            denominator *= 3
    modulus = 1 << len(bits)
    return numerator * pow(denominator, -1, modulus) % modulus


def checked_sum(quotients, state):
    assert quotients and len(quotients) % 2 == 0
    assert len(quotients) <= 8 * MAX_BITS + 8
    terms, modulus, coefficient, offset = state
    total = 0
    for j in range(0, len(quotients), 2):
        qa, qb = map(integer, quotients[j:j + 2])
        assert terms >= 0 and modulus > 0
        ra, rb = coefficient - qa * modulus, offset - qb * modulus
        assert 0 <= ra < modulus and 0 <= rb < modulus, "invalid Euclidean quotient"
        total += qa * (terms * (terms - 1) // 2) + qb * terms
        top = ra * terms + rb
        if j + 2 == len(quotients):
            assert top < modulus, "truncated transcript"
        else:
            assert top >= modulus and ra > 0, "extra transcript steps"
            terms, new_offset = divmod(top, modulus)
            modulus, coefficient, offset = ra, modulus, new_offset
    return total


def checked_basis(basis, n, a):
    assert isinstance(basis, list) and len(basis) == 2
    assert all(isinstance(row, list) and len(row) == 2 for row in basis)
    f, g = ([integer(x) for x in row] for row in basis)
    modulus = 1 << n
    assert abs(f[0] * g[1] - f[1] * g[0]) == modulus, "wrong lattice index"
    assert (f[0] - a * f[1]) % modulus == (g[0] - a * g[1]) % modulus == 0
    return f, g


def checked_basis_box(cert, basis, n, a, bound):
    """Check endpoint inequalities, never call the producer's interval code.

    Membership plus index proves this is a basis of the whole cylinder lattice.
    Odd q forces odd beta. The determinant bound and central symmetry reduce
    ALL vectors in the box to the listed positive odd beta values.
    """
    assert cert["type"] == "odd-box-basis-interval-v1"
    assert 0 <= bound and integer(cert["bound"]) == bound
    f, g = checked_basis(basis, n, a)
    assert f[1] % 2 == 0 and g[1] % 2 == 1, "basis denominator parity"
    modulus, cap = 1 << n, integer(cert["coefficient_bound"])
    assert 0 <= cap <= MAX_COEFFICIENT_BOUND, "coefficient cap exceeded"
    top = bound * (abs(f[0]) + abs(f[1]))
    assert cap * modulus <= top < (cap + 1) * modulus, "wrong coefficient bound"
    rows = cert["intervals"]
    assert isinstance(rows, list) and len(rows) == (cap + 1) // 2
    for index, row in enumerate(rows):
        beta = 2 * index + 1
        assert isinstance(row, list) and len(row) == 2
        lower, upper, impossible = [], [], False
        for fi, gi, interval in zip(f, g, row):
            constant = beta * gi
            if fi == 0:
                assert interval is None, "zero coordinate needs constant check"
                impossible |= not -bound <= constant <= bound
                continue
            assert isinstance(interval, list) and len(interval) == 2
            lo, hi = map(integer, interval)
            # Normalize the coefficient sign; verify tight endpoints directly
            # rather than recomputing division using the producer's formula.
            if fi < 0:
                constant = -constant
            divisor = abs(fi)
            assert (lo - 1) * divisor + constant < -bound <= lo * divisor + constant
            assert hi * divisor + constant <= bound < (hi + 1) * divisor + constant
            lower.append(lo)
            upper.append(hi)
        assert lower, "singular basis"
        assert impossible or max(lower) > min(upper), "smaller-height vector exists"
    return True


def verify_integer_record(record, bits=None):
    """Also accepts the historical integer records for regression checking."""
    n = record["N"]
    assert type(n) is int and 0 <= n <= MAX_BITS
    a, h, p, q = (integer(record[k]) for k in ("A", "H", "p", "q"))
    modulus = 1 << n
    assert 0 <= a < modulus and 1 <= h <= modulus
    assert q > 0 and q & 1 and gcd(p, q) == 1
    assert max(abs(p), q) == h and (p - a * q) % modulus == 0
    if bits is not None:
        assert len(bits) == n and all(b in (0, 1) for b in bits)
        assert inverse_residue(bits) == a, "reverse-branch residue differs"
        value = p
        for bit in bits:
            assert value % 2 == bit, "actual numerator parity differs"
            value = (3 * value + q) // 2 if bit else value // 2
    cert = record["minimality"]
    bound = h - 1
    assert integer(cert["bound"]) == bound
    if cert["type"] == "odd-box-floor-sum-v1":
        terms = (bound + 1) // 2
        upper = checked_sum(cert["upper"], (terms, modulus, 2 * a, a + bound))
        lower = checked_sum(cert["lower"], (terms, modulus, 2 * a, a - bound - 1))
        assert upper == integer(cert["upper_sum"]) and lower == integer(cert["lower_sum"])
        assert upper - lower == 0, "smaller-height vector exists"
        if "basis" in record:
            checked_basis(record["basis"], n, a)
    else:
        checked_basis_box(cert, record["basis"], n, a, bound)
    return {"N": n, "height_bits": h.bit_length()}


def verify_record(record):
    assert record["format"] == "phase13-overnight-height-v1"
    assert all(isinstance(record[k], str) for k in ("A", "H", "p", "q"))
    assert type(record["N"]) is int and 16384 < record["N"] <= MAX_BITS
    bits = literal_prefix(record["N"])
    assert hashlib.sha256(bytes(bits)).hexdigest() == record["parity_sha256"]
    return verify_integer_record(record, bits)


def expired(_signum, _frame):
    raise TimeoutError("independent per-record verification exceeded 180 seconds")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", required=True)
    args = parser.parse_args()
    path = ROOT / "heights.jsonl"
    assert path.exists(), "missing overnight height evidence"
    assert path.stat().st_size <= MAX_FILE_BYTES
    raw = path.read_bytes()
    assert raw.endswith(b"\n")
    seen = set()
    signal.signal(signal.SIGALRM, expired)
    for line in raw.splitlines():
        signal.alarm(180)
        record = json.loads(line)
        assert record["N"] not in seen, "duplicate sample"
        seen.add(record["N"])
        result = verify_record(record)
        signal.alarm(0)
        print(f"VERIFIED N={result['N']} height_bits={result['height_bits']}", flush=True)
    assert seen
    print(f"PASS: {len(seen)} independent primitive witnesses, actual parity prefixes, "
          "and zero box counts at H-1")


if __name__ == "__main__":
    main()
