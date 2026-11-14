#!/usr/bin/env python3
"""Bounded exact language search: binary uniform lengths 2..6, h=1..8.

No seed search, random sampling, external workers, or floating-point tests.
Finite certificates for other substitutions are not reported as Lean theorems.
"""

import argparse
from collections import Counter
from fractions import Fraction
import itertools
import json
from pathlib import Path


REPORT = Path(__file__).with_name("search-summary.json")
LEAN_PROVED = {("100", "110"), ("110", "100")}


def substitute(xs, one, zero):
    return tuple(b for a in xs for b in (one if a else zero))


def prefix(one, zero, size):
    xs = (1,)
    while len(xs) < size:
        xs = substitute(xs, one, zero)
    return xs[:size]


def closed_language(one, zero, h):
    """Least finite closure of the actual initial window under child offsets.

    Each new row occurs by substitution of its parent occurrence; strong
    induction on the starting index gives the reverse inclusion. The matching
    generic coverage theorem and two concrete certificates are in Lean.
    """
    length = len(one)
    initial = prefix(one, zero, h)
    language, pending = {initial}, [initial]
    while pending:
        xs = pending.pop()
        expanded = substitute(xs, one, zero)
        for r in range(length):
            child = expanded[r:r + h]
            assert len(child) == h
            if child not in language:
                language.add(child)
                pending.append(child)
    assert len(language) <= 2**h
    for xs in language:
        expanded = substitute(xs, one, zero)
        assert all(expanded[r:r + h] in language for r in range(length))
    return sorted(language)


def matrix_product(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(2)) for j in range(2)] for i in range(2)]


def primitive_witness(length, r0, r1):
    matrix = [[length - r0, length - r1], [r0, r1]]
    power = [[1, 0], [0, 1]]
    for exponent in range(1, 5):
        power = matrix_product(power, matrix)
        if all(x > 0 for row in power for x in row):
            return exponent
    return None


def analyze(one, zero):
    length, r0, r1 = len(one), sum(zero), sum(one)
    rows, first = [], None
    for h in range(1, 9):
        language = closed_language(one, zero, h)
        maximum = max(sum(r1 if b else r0 for b in xs) for xs in language)
        contracts = 3**maximum < 2**(length * h)
        if contracts and first is None:
            first = h
        rows.append({"h": h, "windows": len(language), "R": maximum, "contracts": contracts})
    return first, rows


def build_report():
    summaries, selected, totals = [], [], Counter()
    for length in range(2, 7):
        counts, firsts = Counter(), Counter()
        one_images = [(1,) + tail for tail in itertools.product((0, 1), repeat=length - 1)]
        zero_images = list(itertools.product((0, 1), repeat=length))
        for one, zero in itertools.product(one_images, zero_images):
            r0, r1 = sum(zero), sum(one)
            if r0 == r1:
                counts["equal_weight_skipped"] += 1
                continue
            counts["unequal_pairs_tested"] += 1
            first, rows = analyze(one, zero)
            counts["languages_tested"] += 8
            if first is not None:
                counts["pairs_with_contraction"] += 1
                firsts[first] += 1
                if max(3**r0, 3**r1) > 2**length:
                    counts["contracting_with_expanding_image"] += 1
            else:
                counts["no_certificate_at_h_le_8"] += 1
            text_one, text_zero = "".join(map(str, one)), "".join(map(str, zero))
            # Keep a small deterministic selection, not a huge catalogue.
            chosen = ((text_one, text_zero) in LEAN_PROVED or
                      (text_one, text_zero) in {("1000", "1110"), ("1100", "1110"),
                                               ("10000", "11110"), ("101", "010")})
            if chosen:
                denominator = length - r1 + r0
                frequency = Fraction(r0, denominator) if denominator else None
                selected.append({"one": text_one, "zero": text_zero, "length": length,
                                 "r0": r0, "r1": r1, "first_h": first, "rows": rows,
                                 "primitive_power_witness": primitive_witness(length, r0, r1),
                                 "incidence_eigenvalues": [length, r1 - r0],
                                 "candidate_one_frequency": str(frequency),
                                 "aperiodicity_lean_proved": (text_one, text_zero) in LEAN_PROVED,
                                 "rational_exclusion_lean_proved": (text_one, text_zero) in LEAN_PROVED})
        totals.update(counts)
        summaries.append({"length": length, **dict(sorted(counts.items())),
                          "first_contracting_h_counts": {str(h): firsts[h] for h in sorted(firsts)}})
    return {"bounds": {"length_min": 2, "length_max": 6, "h_min": 1, "h_max": 8,
                       "max_windows_per_language": 256},
            "totals": dict(sorted(totals.items())), "by_length": summaries,
            "selected": selected,
            "kernel_proved_exclusions": [list(pair) for pair in sorted(LEAN_PROVED)],
            "scope": "Finite-language contraction data for other pairs do not certify aperiodicity or rational exclusion."}


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
        assert REPORT.read_text() == rendered, "bounded search output differs"
    print(json.dumps(report["totals"], sort_keys=True))
    for case in report["selected"]:
        print(f"1->{case['one']}, 0->{case['zero']}: first h={case['first_h']}, "
              f"Lean exclusion={case['rational_exclusion_lean_proved']}")


if __name__ == "__main__":
    main()
