#!/usr/bin/env python3
"""Adversarial finite checks of the independent compact box certificate.

Direct cylinder enumeration includes nonempty boxes. Fraction endpoints in
this test construct transcripts even when the producer correctly refuses
them, so the independent checker's rejection is exercised separately.
"""

import argparse
from copy import deepcopy
from fractions import Fraction
import gzip
import hashlib
import json
from math import ceil, floor
from pathlib import Path
import sys

from extended_height import (BasisLimitError, MAX_COEFFICIENT_BOUND,
                             basis_certificate, candidates, certify)
from verify_results import checked_basis_box, integer, verify_integer_record


ROOT = Path(__file__).resolve().parent


def accepted(action):
    try:
        action()
    except (AssertionError, ValueError):
        return False
    return True


def unchecked_transcript(basis, n, bound):
    """Use rational endpoints to make valid intervals, including nonempty ones."""
    f, g = basis
    cap = bound * sum(map(abs, f)) // (1 << n)
    rows = []
    for beta in range(1, cap + 1, 2):
        row = []
        for fi, gi in zip(f, g):
            if fi == 0:
                row.append(None)
            else:
                ends = sorted((Fraction(-bound - beta * gi, fi),
                               Fraction(bound - beta * gi, fi)))
                row.append([hex(ceil(ends[0])), hex(floor(ends[1]))])
        rows.append(row)
    return {"type": "odd-box-basis-interval-v1", "bound": hex(bound),
            "coefficient_bound": hex(cap), "intervals": rows}


def exhaustive():
    boxes = empty = nonempty = 0
    signs, zeros = set(), set()
    largest_cap = 0
    for n in range(8):
        modulus = 1 << n
        for a in range(modulus):
            f, g = next(candidates(a, n, [n]))["basis"]
            bases = []
            for shear in (-1, 0, 1):
                ff = [x + 2 * shear * y for x, y in zip(f, g)]
                for shift in (-1, 0, 1):
                    bases.append([ff, [y + shift * x for x, y in zip(ff, g)]])
            bases.extend([[[-x for x in f], g], [f, [-x for x in g]],
                          [[-x for x in f], [-x for x in g]]])
            for bound in range(9):
                is_empty = not any((p - a * q) % modulus == 0
                                   for q in range(1, bound + 1, 2)
                                   for p in range(-bound, bound + 1))
                for basis in bases:
                    for i, vector in enumerate(basis):
                        for j, value in enumerate(vector):
                            signs.add((value > 0) - (value < 0))
                            if value == 0:
                                zeros.add((i, j))
                    cert = unchecked_transcript(basis, n, bound)
                    largest_cap = max(largest_cap, integer(cert["coefficient_bound"]))
                    assert accepted(lambda: checked_basis_box(cert, basis, n, a, bound)) == is_empty
                    assert accepted(lambda: basis_certificate(basis, n, bound)) == is_empty
                    if is_empty:
                        produced = basis_certificate(basis, n, bound)
                        assert produced == cert
                        checked_basis_box(produced, basis, n, a, bound)
                        empty += 1
                    else:
                        nonempty += 1
                    boxes += 1
    assert signs == {-1, 0, 1} and zeros == {(0, 0), (0, 1), (1, 0)}
    assert empty and nonempty and largest_cap > 1
    return {"boxes": boxes, "empty": empty, "nonempty": nonempty,
            "largest_coefficient_bound": largest_cap,
            "all_coordinate_signs": sorted(signs),
            "zero_coordinate_positions": [list(x) for x in sorted(zeros)]}


def corruptions():
    n, a = 12, 253
    candidate = next(candidates(a, n, [n]))
    good = certify(candidate, [], method="basis")
    assert good["minimality"]["intervals"]
    verify_integer_record(good)
    bad_records = []
    for key in ("bound", "coefficient_bound"):
        bad = deepcopy(good)
        bad["minimality"][key] = hex(integer(bad["minimality"][key]) + 1)
        bad_records.append(bad)
    bad = deepcopy(good)
    bad["minimality"]["intervals"] = []
    bad_records.append(bad)
    bad = deepcopy(good)
    bad["minimality"]["intervals"].append(deepcopy(bad["minimality"]["intervals"][0]))
    bad_records.append(bad)
    for endpoint in (0, 1):
        bad = deepcopy(good)
        interval = next(x for row in bad["minimality"]["intervals"] for x in row if x is not None)
        interval[endpoint] = hex(integer(interval[endpoint]) + 1)
        bad_records.append(bad)
    bad = deepcopy(good)
    bad["basis"][0][0] = hex(integer(bad["basis"][0][0]) + 1)
    bad_records.append(bad)
    bad = deepcopy(good)
    bad["basis"] = bad["basis"][::-1]
    bad_records.append(bad)
    bad = deepcopy(good)
    bad["minimality"]["type"] = "unknown-box-proof"
    bad_records.append(bad)
    for bad in bad_records:
        assert not accepted(lambda: verify_integer_record(bad)), "corrupt basis certificate accepted"

    # Valid index, invalid membership or odd-coset parity; isolate these checks.
    assert not accepted(lambda: checked_basis_box(good["minimality"], candidate["basis"],
                                                n, a ^ 1, candidate["H"] - 1))
    f, g = candidate["basis"]
    odd_f = [[x + y for x, y in zip(f, g)], g]
    assert not accepted(lambda: checked_basis_box(good["minimality"], odd_f,
                                                n, a, candidate["H"] - 1))
    zero_basis = [[16, 0], [8, 1]]
    zero_cert = unchecked_transcript(zero_basis, 4, 1)
    checked_basis_box(zero_cert, zero_basis, 4, 8, 1)
    assert zero_cert["intervals"][0][1] is None
    zero_cert["intervals"][0][1] = ["0x0", "0x0"]
    assert not accepted(lambda: checked_basis_box(zero_cert, zero_basis, 4, 8, 1))

    # Oversized enumeration is rejected before allocating rows; auto falls
    # back to the preserved floor-sum certificate instead of omitting beta.
    large = deepcopy(candidate)
    large["basis"][0] = [x + 2 * (MAX_COEFFICIENT_BOUND + 1) * y for x, y in zip(f, g)]
    try:
        certify(large, [], method="basis")
    except BasisLimitError:
        pass
    else:
        raise AssertionError("explicit compact mode did not enforce enumeration cap")
    fallback = certify(large, [], method="auto")
    assert fallback["minimality"]["type"] == "odd-box-floor-sum-v1"
    verify_integer_record(fallback)
    oversized = unchecked_transcript([[1, 0], [0, 1]], 0, 0)
    oversized["coefficient_bound"] = hex(MAX_COEFFICIENT_BOUND + 1)
    assert not accepted(lambda: checked_basis_box(oversized, [[1, 0], [0, 1]], 0, 0, 0))
    return {"rejected_malformed_cases": len(bad_records) + 4,
            "explicit_cap_rejection": True, "floor_sum_fallback_verified": True}


def regressions(quick):
    baseline_raw = (ROOT.parent / "heights.json.gz").read_bytes()
    baseline = json.loads(gzip.decompress(baseline_raw))
    count, largest_cap = 0, 0
    for family in baseline["families"]:
        records = family["records"]
        if quick:
            records = [records[0], records[-1]]
        for old in records:
            cert = basis_certificate(old["basis"], old["N"], old["H"] - 1)
            compact = {**old, "minimality": cert}
            verify_integer_record(compact)
            largest_cap = max(largest_cap, integer(cert["coefficient_bound"]))
            count += 1
    source = ROOT / "heights.jsonl"
    raw = source.read_bytes()
    overnight = []
    for line in raw.splitlines():
        old = json.loads(line)
        basis = [[integer(x) for x in row] for row in old["basis"]]
        cert = basis_certificate(basis, old["N"], integer(old["H"]) - 1)
        verify_integer_record({**old, "minimality": cert})
        overnight.append(old["N"])
    return {"historical_records": count, "historical_source_sha256": hashlib.sha256(baseline_raw).hexdigest(),
            "largest_historical_coefficient_bound": largest_cap,
            "overnight_sample_ids": sorted(overnight),
            "overnight_source_sha256": hashlib.sha256(raw).hexdigest(),
            "note": "Alternative compact proofs of the stored exact minima; no sample recomputed."}


def main():
    sys.set_int_max_str_digits(20000)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--quick", action="store_true")
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    result = {"format": "phase13-overnight-basis-tests-v1",
              "classification": "finite exact regression, not a universal formal proof",
              "exhaustive": exhaustive(), "adversarial": corruptions(),
              "regression": regressions(args.quick)}
    if args.write:
        assert not args.quick, "do not replace full evidence with a quick run"
        (ROOT / "basis-validation.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, sort_keys=True), flush=True)
    print("PASS: independent compact-box exclusions, direct nonempty/empty boxes, "
          "signed/zero coordinates, adversarial mutations, cap/fallback, stored minima")


if __name__ == "__main__":
    main()
