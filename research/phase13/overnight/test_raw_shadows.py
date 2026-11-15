#!/usr/bin/env python3
"""Small semantic, gcd, corruption, and resumable-state controls."""

from copy import deepcopy
import json
from math import gcd
from pathlib import Path
import tempfile

import raw_shadows as producer
import verify_raw_shadows as checker


def rejected(action):
    try:
        action()
    except (AssertionError, KeyError, ValueError):
        return
    raise AssertionError("malformed evidence was accepted")


def main():
    assert checker.literal_controls() == 10
    zero, one = ((2, 0), (0, 1)), ((2, -1), (0, 3))
    c0, c1 = 0, 1
    inherited = json.loads((producer.ROOT.parent / "modular.json").read_bytes())["integer_levels"]
    for k in range(5):
        row = producer.record(k, zero, one)
        checker.verify_row(row, k, c0, c1, inherited)
        assert producer.coordinates(zero, one) == checker.shadow(k, c0, c1)[:2]
        if k == 1:
            assert one == ((64, -179), (0, 81))
            assert zero == ((64, -211), (0, 243))
            assert producer.multiply(one, zero) != producer.multiply(zero, one)
            control = deepcopy(row), c0, c1
        if k < 4:
            _, _, _, m, a, b = checker.scalars(k)
            c0, c1 = checker.offsets_next(c0, c1, m, a, b)
            zero, one = producer.advance(zero, one)

    cases = 0
    for exponent in range(6):
        for delta in range(1, 64, 2):
            if delta % 3 == 0:
                continue
            for p in range(-150, 151):
                if p:
                    assert checker.split_gcd(p, delta, exponent) == gcd(p, 3 ** exponent * delta)
                    cases += 1

    row, c0, c1 = control
    mutations = {"raw_gcd": "0x2", "numerator_sign": 1, "denominator_sign": -1,
                 "denominator_odd": False, "k": 0, "S": 7, "L": 68,
                 "raw_numerator_bits": 0, "raw_denominator_bits": 0,
                 "reduced_numerator_bits": 0, "reduced_denominator_bits": 0,
                 "reduced_height_bits": 0, "raw_numerator_abs_sha256": "0" * 64,
                 "raw_denominator_sha256": "0" * 64,
                 "reduced_numerator_abs_sha256": "0" * 64,
                 "reduced_denominator_sha256": "0" * 64,
                 "strict_uniqueness": False, "format": "wrong", "extra": 1}
    for key, value in mutations.items():
        bad = {**row, key: value}
        rejected(lambda: checker.verify_row(bad, 1, c0, c1, inherited))
    noncanonical = {**row, "raw_gcd": "0X1"}
    rejected(lambda: checker.verify_row(noncanonical, 1, c0, c1, inherited))

    # Check that both pre-publication and post-publication states can resume.
    original_root, original_checkpoint = producer.ROOT, producer.CHECKPOINT
    try:
        with tempfile.TemporaryDirectory(dir=producer.ROOT, prefix="raw-shadow-test-") as directory:
            producer.ROOT = Path(directory)
            producer.CHECKPOINT = producer.ROOT / "checkpoint.json"
            producer.save_checkpoint(4, zero, one)
            assert producer.load_checkpoint(4) == (4, zero, one)
            assert producer.load_checkpoint(5) == (4, zero, one)
            rejected(lambda: producer.load_checkpoint(3))
            saved = json.loads(producer.CHECKPOINT.read_bytes())
            saved["matrices"][0][0][0] = "0X1"
            producer.CHECKPOINT.write_text(json.dumps(saved))
            rejected(lambda: producer.load_checkpoint(4))
    finally:
        producer.ROOT, producer.CHECKPOINT = original_root, original_checkpoint
    print(f"PASS: 10 literal inverse maps; 5 matrix/offset shadow controls; {cases} split gcds; "
          f"{len(mutations) + 1} corruptions rejected; resumable checkpoint controls")


if __name__ == "__main__":
    main()
