#!/usr/bin/env python3
"""Independent bounded witness and no-smaller-height certificate verifier.

Imports no project implementation or optimizer. Literal substitution and
reverse inverse branches independently reconstruct the requested cylinder.
Python exact arithmetic and the written floor-sum identities are the trust
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
    assert cert["type"] == "odd-box-floor-sum-v1" and integer(cert["bound"]) == bound
    terms = (bound + 1) // 2
    upper = checked_sum(cert["upper"], (terms, modulus, 2 * a, a + bound))
    lower = checked_sum(cert["lower"], (terms, modulus, 2 * a, a - bound - 1))
    assert upper == integer(cert["upper_sum"]) and lower == integer(cert["lower_sum"])
    assert upper - lower == 0, "smaller-height vector exists"
    if "basis" in record:
        (u, v), (r, s) = ([integer(x) for x in row] for row in record["basis"])
        assert abs(u * s - v * r) == modulus
        assert (u - a * v) % modulus == 0 and (r - a * s) % modulus == 0
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
