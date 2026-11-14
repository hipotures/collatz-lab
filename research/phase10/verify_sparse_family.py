#!/usr/bin/env python3
"""Small exact regressions for the symbolic all-length sparse-family proof.

Lengths 3..16, levels 0..L. No seed intervals, real logarithms, or enormous
Collatz powers are evaluated. The generic infinite-family theorem is in Lean.
"""

import argparse
import json
from pathlib import Path


REPORT = Path(__file__).with_name("sparse-family-certificate.json")


def build_report():
    rows = []
    for length in range(3, 17):
        r0, r1, delta = length - 1, 1, 2 - length
        denominator = 2 * (length - 1)
        counts = [0, 1]
        for k in range(length + 1):
            size, transient = length**k, (length - 2)**k
            for b in (0, 1):
                assert 2 * counts[b] - size == delta**k * (2 * b - 1)
                assert counts[b] <= (size + transient) // 2
                assert denominator * counts[b] - r0 * size == delta**k * (denominator * b - r0)
            if k == length:
                assert max(counts) == (size + transient) // 2
                assert 4 * transient <= size
                assert 8 * max(counts) <= 5 * size
                # 3^5 < 2^8 and the preceding integer margin certify the gap.
                assert 3**5 < 2**8
                rows.append({"L": length, "level": k, "chunk_length": str(size),
                             "transient": str(transient), "odd_count_cap": str(max(counts)),
                             "four_transient_le_length": True, "eight_R_le_five_S": True})
            counts = [(length - r0) * counts[0] + r0 * counts[1],
                      (length - r1) * counts[0] + r1 * counts[1]]
    return {"bounds": {"length_min": 3, "length_max": 16, "max_level": "L"},
            "rows": rows,
            "theorem": "no_rational_seed_realizes_unequalSparse: every L>=3, every integer p,q",
            "scope": "The finite checks are regressions for the generic kernel proof, not a search-based extension."}


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
        assert REPORT.read_text() == rendered, "sparse-family regressions differ"
    print("Sparse family L=3..16: exact signed balances, binomial gap and uniform 5/8 margin")
    print("All L>=3 are covered by the symbolic Lean theorem; no huge Collatz powers evaluated")


if __name__ == "__main__":
    main()
