#!/usr/bin/env python3
"""Independent exact literal, incidence, signed-balance and prefix checks.

Bounds are fixed: four substitutions, levels 0..5, prefix length 81. Larger
images are counted by a two-entry recurrence, not materialized or seed-scanned.
"""

import argparse
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
from verify_unequal import affine, orbit_prefix, substitute


REPORT = Path(__file__).with_name("spectral-certificate.json")


def build_report():
    cases = []
    for one_text, zero_text, closing_level, bound in (
        ("100", "110", 2, 5), ("110", "100", 2, 5),
        ("1000", "1110", 2, 10), ("10000", "11110", 3, 76),
    ):
        one, zero = tuple(map(int, one_text)), tuple(map(int, zero_text))
        length, r0, r1 = len(one), sum(zero), sum(one)
        delta, denominator = r1 - r0, len(one) - r1 + r0
        counts, levels = [0, 1], []
        images = [(0,), (1,)]
        for k in range(6):
            size = length**k
            for b in (0, 1):
                assert denominator * counts[b] - r0 * size == delta**k * (denominator * b - r0)
            if k <= 3:
                assert list(map(sum, images)) == counts
                images = [substitute(xs, one, zero) for xs in images]
            maximum = max(counts)
            levels.append({"level": k, "length": size, "zero_count": counts[0],
                           "one_count": counts[1], "max_count": maximum,
                           "contracts": 3**maximum < 2**size})
            # Count mu^(k+1)(b) by the actual letters in mu(b).
            counts = [(length - r0) * counts[0] + r0 * counts[1],
                      (length - r1) * counts[0] + r1 * counts[1]]
        closing = levels[closing_level]
        assert closing["max_count"] == bound and closing["contracts"]
        word = (1,)
        while len(word) < 81:
            word = substitute(word, one, zero)
        word = word[:81]
        r, c = affine(word)
        modulus = 2**81
        p = (-c * pow(3**r, -1, modulus)) % modulus
        parity, states = orbit_prefix(p, 1, 81)
        assert parity == word
        assert 2**81 * states[-1] == 3**r * p + c
        # Sign/reduction checks use the same finite word and one modular inverse.
        negative = (-5 * c * pow(3**r, -1, modulus)) % modulus - modulus
        assert orbit_prefix(negative, 5, 81)[0] == word
        assert orbit_prefix(3 * negative, 15, 81)[0] == word
        cases.append({"one": one_text, "zero": zero_text, "delta": delta,
                      "frequency_denominator": denominator, "levels": levels,
                      "closing_level": closing_level, "R": bound,
                      "positive_prefix_81": {"p": str(p), "end": str(states[-1])},
                      "negative_prefix_81": {"p": str(negative), "q": 5},
                      "status": "Aperiodicity and exclusion kernel-proved; finite checks independent."})
    return {"bounds": {"cases": 4, "max_level": 5, "prefix_length": 81}, "cases": cases}


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
        assert REPORT.read_text() == rendered, "spectral finite certificate differs"
    print("Four exact spectral certificates; literal counts and signed balances at levels 0..5")
    print("1000/1110: 3^10 < 2^16; 10000/11110: 3^76 < 2^125; signed 81-bit witnesses")


if __name__ == "__main__":
    main()
