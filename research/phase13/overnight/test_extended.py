#!/usr/bin/env python3
"""Regress extended arithmetic against brute force and all baseline records."""

import argparse
from copy import deepcopy
import gzip
import json
from pathlib import Path
import sys

from extended_height import candidates, certify, frontier_prefix, residue
from verify_results import inverse_residue, literal_prefix, verify_integer_record


def main():
    # Historical certificates contain decimal integers through 16,384 bits.
    # Keep the conversion limit finite; new evidence uses hexadecimal instead.
    sys.set_int_max_str_digits(20000)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--quick", action="store_true",
                        help="check the first and final baseline record in every family")
    args = parser.parse_args()
    count = 0
    for n in range(9):
        modulus = 1 << n
        for a in range(modulus):
            candidate = next(candidates(a, n, [n]))
            brute = min(max(min(a * q % modulus, (-a * q) % modulus), q)
                        for q in range(1, max(2, modulus // 2 + 1), 2))
            assert candidate["H"] == max(1, brute)
            verify_integer_record(certify(candidate, []))
            count += 1
    root = Path(__file__).resolve().parents[1]
    baseline = json.loads(gzip.decompress((root / "heights.json.gz").read_bytes()))
    regressions = 0
    for family in baseline["families"]:
        records = family["records"]
        if args.quick:
            records = [records[0], records[-1]]
        final = records[-1]
        produced = list(candidates(final["A"], final["N"], [r["N"] for r in records]))
        assert len(records) == len(produced)
        for old, new in zip(records, produced):
            assert (old["N"], old["A"], old["H"]) == (new["N"], new["A"], new["H"])
            verify_integer_record(old)
            verify_integer_record(certify(new, []))
            regressions += 1
    for n in (11, 12, 403, 16384):
        bits = frontier_prefix(n)
        assert bits == literal_prefix(n)
        a = residue(bits)
        assert a == inverse_residue(bits)
        candidate = next(candidates(a, n, [n]))
        verify_integer_record(certify(candidate, bits), bits)
        if n in (11, 12):
            assert candidate["H"] == {11: 3, 12: 513}[n]
    bits = frontier_prefix(12)
    good = certify(next(candidates(residue(bits), 12, [12])), bits, method="floor")
    corruptions = []
    for key in ("H", "A", "p", "q"):
        bad = deepcopy(good)
        bad[key] = hex(int(bad[key], 16) + 1)
        corruptions.append(bad)
    bad = deepcopy(good)
    bad["minimality"]["upper"] = bad["minimality"]["upper"][:-2]
    corruptions.append(bad)
    bad = deepcopy(good)
    bad["minimality"]["lower"][0] = hex(int(bad["minimality"]["lower"][0], 16) + 1)
    corruptions.append(bad)
    bad = deepcopy(good)
    bad["minimality"]["lower_sum"] = hex(int(bad["minimality"]["lower_sum"], 16) + 1)
    corruptions.append(bad)
    for bad in corruptions:
        try:
            verify_integer_record(bad, bits)
        except (AssertionError, ValueError):
            continue
        raise AssertionError("corrupt extended certificate accepted")
    print(f"PASS: {count} brute-force residues; {regressions} baseline minima and certificates; "
          f"four independent prefix/residue controls; {len(corruptions)} rejected corruptions; "
          "H_11=3, H_12=513")


if __name__ == "__main__":
    main()
