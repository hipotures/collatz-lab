#!/usr/bin/env python3
"""Compact deterministic inventory of the independently checked height file.

This is derived metadata, not a second minimality proof. The separate
verify_results.py checks all witnesses and no-smaller-height certificates.
No floating-point comparisons or experimental recomputation are used here.
"""

import argparse
import hashlib
import json
from math import gcd
from pathlib import Path


ROOT = Path(__file__).resolve().parent


def digest(value):
    value = abs(value)
    return hashlib.sha256(value.to_bytes((value.bit_length() + 7) // 8, "big")).hexdigest()


def inventory():
    raw = (ROOT / "heights.jsonl").read_bytes()
    assert 0 < len(raw) <= 8 * 1024 * 1024 and raw.endswith(b"\n")
    rows = sorted((json.loads(line) for line in raw.splitlines()), key=lambda r: r["N"])
    assert len({r["N"] for r in rows}) == len(rows)
    baseline = json.loads((ROOT.parent / "modular.json").read_text())["integer_levels"]
    samples, comparisons = [], []
    previous = None
    for row in rows:
        n = row["N"]
        h, p, q = (int(row[k], 16) for k in ("H", "p", "q"))
        f = [int(x, 16) for x in row["basis"][0]]
        assert h == max(abs(p), q) and q > 0 and q % 2 and gcd(p, q) == 1
        entry = {"N": n, "height_bits": h.bit_length(),
                 "numerator_sign": (p > 0) - (p < 0),
                 "numerator_abs_sha256": digest(p), "denominator_sha256": digest(q),
                 "parity_sha256": row["parity_sha256"],
                 "nonhold_updates": row["nonhold_updates"],
                 "strict_witness_separation": 2 * h * (h - 1) < (1 << n),
                 "even_basis_denominator": f[1] % 2 == 0,
                 "box_basis_coefficient_bound": hex((h - 1) * (abs(f[0]) + abs(f[1])) // (1 << n)),
                 "upper_steps": len(row["minimality"]["upper"]) // 2,
                 "lower_steps": len(row["minimality"]["lower"]) // 2}
        for known in baseline:
            if known["L"] == n:
                factor = known["raw_gcd"]
                assert p < 0
                assert digest(p * factor) == known["raw_numerator_abs_sha256"]
                assert digest(q * factor) == known["raw_denominator_sha256"]
                assert h.bit_length() == known["reduced_height_bits"]
                entry["matches_inherited_shadow_level"] = known["k"]
        samples.append(entry)
        if previous is not None:
            old_n, old_h, old_p, old_q = previous
            assert h >= old_h
            exponent = (h // old_h).bit_length() - 1
            assert (old_h << exponent) <= h < (old_h << (exponent + 1))
            comparisons.append({"from_N": old_n, "to_N": n,
                                "same_primitive_witness": (p, q) == (old_p, old_q),
                                "same_height": h == old_h,
                                "height_ratio_floor_log2": exponent})
        previous = n, h, p, q
    return {"format": "phase13-overnight-inventory-v1",
            "classification": "derived exact finite metadata; not an asymptotic result",
            "source": "heights.jsonl", "source_bytes": len(raw),
            "source_sha256": hashlib.sha256(raw).hexdigest(),
            "samples": samples, "comparisons": comparisons}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    result = inventory()
    target = ROOT / "height-inventory.json"
    if args.write:
        target.write_text(json.dumps(result, indent=2) + "\n")
    else:
        assert json.loads(target.read_text()) == result, "derived inventory differs"
    print(f"PASS: {len(result['samples'])} height inventory entries; exact witness and jump "
          "comparisons; inherited shadow hashes at sampled boundaries")


if __name__ == "__main__":
    main()
