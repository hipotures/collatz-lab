#!/usr/bin/env python3
"""Reproduce exact finite certificates without enumerating seed intervals.

These finite tests are independent evidence; the infinite results are proved
in Lean. Run --write to regenerate the deterministic JSON, --check in CI.
"""

import argparse
import itertools
import json
from pathlib import Path


ONE = (1, 0, 0)
ZERO = (1, 1, 0)
REPORT = Path(__file__).with_name("unequal-certificate.json")


def substitute(xs, one=ONE, zero=ZERO):
    return tuple(bit for b in xs for bit in (one if b else zero))


def indexed_bit(n):
    if n == 0:
        return 1
    parent, column = divmod(n, 3)
    return (1, 1 - indexed_bit(parent), 0)[column]


def affine(xs):
    odd, offset = 0, 0
    for i, b in enumerate(xs):
        assert b in (0, 1)
        if b:
            odd += 1
            offset = 3 * offset + 2**i
    return odd, offset


def orbit_prefix(p, q, size):
    parity, states = [], [p]
    for _ in range(size):
        b = p % 2
        parity.append(b)
        numerator = 3 * p + q if b else p
        assert numerator % 2 == 0
        p = numerator // 2
        states.append(p)
    return tuple(parity), states


def build_report():
    word = (1,)
    lengths = []
    for _ in range(4):
        word = substitute(word)
        lengths.append(len(word))
        assert word == tuple(indexed_bit(n) for n in range(len(word)))
    assert lengths == [3, 9, 27, 81]
    assert sum(ONE) == 1 and sum(ZERO) == 2
    assert ONE[0] == 1 and ONE != ZERO
    # Every two-image concatenation has no 000, including the boundary.
    for a, b in itertools.product((0, 1), repeat=2):
        expanded = substitute((a, b))
        assert all(expanded[j:j + 3] != (0, 0, 0) for j in range(4))

    rows = []
    for source in itertools.product((0, 1), repeat=3):
        if source == (0, 0, 0):
            continue
        expanded = substitute(source)
        r, c = affine(expanded)
        assert r == sum(sum(ONE if b else ZERO) for b in source)
        assert r <= 5 and 3**r <= 243 < 512 == 2**9
        assert 0 <= c <= 3**9 - 2**9 == 19171
        rows.append({"source": "".join(map(str, source)),
                     "expanded": "".join(map(str, expanded)),
                     "odd_count": r, "multiplier": 3**r, "offset": c})
    assert max(row["offset"] for row in rows) == 761
    assert 3**sum(ZERO) == 9 > 8 == 2**3

    r, c = affine(word)
    modulus = 2**81
    p_pos = (-c * pow(3**r, -1, modulus)) % modulus
    p_neg = (-5 * c * pow(3**r, -1, modulus)) % modulus - modulus
    assert p_pos == 2301021985950669302953629
    assert p_neg == -584148266392945232293615
    witnesses = []
    for p, q in ((p_pos, 1), (p_neg, 5), (3 * p_neg, 15), (-p_neg, -5)):
        parity, states = orbit_prefix(p, q, 81)
        assert parity == word
        assert 2**81 * states[-1] == 3**r * p + c * q
        for n in range(9):
            chunk = word[9 * n:9 * (n + 1)]
            rn, cn = affine(chunk)
            assert rn <= 5
            assert 512 * states[9 * (n + 1)] == 3**rn * states[9 * n] + cn * q
        witnesses.append({"p": str(p), "q": q, "steps": 81, "end": str(states[-1])})

    # The unequal rational control remains periodic and realized by the seed 1.
    control = (1,)
    for _ in range(4):
        control = substitute(control, (1, 0, 1), (0, 1, 0))
    assert control == tuple(1 - n % 2 for n in range(81))
    assert orbit_prefix(1, 1, 81)[0] == control
    return {"one": "100", "zero": "110", "literal_lengths": lengths,
            "literal_prefix_81": "".join(map(str, word)),
            "source_windows_without_000": rows,
            "uniform_multiplier_cap": 243, "chunk_denominator": 512,
            "safe_offset_cap": 19171, "finite_offset_cap": 761,
            "finite_realization_witnesses": witnesses,
            "rational_control": {"one": "101", "zero": "010", "p": 1, "q": 1},
            "status": "Finite checks; infinite exclusion and aperiodicity are Lean theorems."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    action = parser.add_mutually_exclusive_group()
    action.add_argument("--check", action="store_true")
    action.add_argument("--write", action="store_true")
    args = parser.parse_args()
    report = build_report()
    rendered = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.write:
        REPORT.write_text(rendered)
    if args.check:
        assert REPORT.read_text() == rendered, "certificate differs; review before regenerating"
    print("100/110: seven exact nine-step rows, 243 < 512; offset caps 19171 and 761")
    print("Literal iterates through 81 bits; positive, negative, unreduced and sign-normalized prefixes")
    print("Rational 101/010 control preserved; no seed interval enumerated")


if __name__ == "__main__":
    main()
