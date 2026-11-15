#!/usr/bin/env python3
"""Reproduce bounded exact profiles and certificates. No third-party packages.

--write replaces only generated Phase 13 JSON files. --check recomputes exact
evidence, excluding machine-dependent timing/memory observations. Completed
families can be reused with --resume; all reused certificates are rechecked.
"""

import argparse
import hashlib
import json
from math import log2
from pathlib import Path
import time
import tracemalloc

from height_lattice import VERSION, profile
from height_reference import MAX_BITS, minimality_certificate
from verify_certificates import verify


ROOT = Path(__file__).resolve().parent


def word(spec, count):
    if spec["kind"] == "morphism":
        images = [spec["zero"], spec["one"]]
        length = len(images[0])
        def at(n):
            digits = []
            while n:
                digits.append(n % length)
                n //= length
            b = 1
            for j in reversed(digits):
                b = int(images[b][j])
            return b
        return [at(j) for j in range(count)]
    if spec["kind"] == "periodic":
        return [int(spec["period"][j % len(spec["period"])]) for j in range(count)]
    return [int(b) for b in spec["bits"][:count]]


def residue(bits):
    c, power, three = 0, 1, 1
    for b in bits:
        if b:
            c = 3 * c + power
            three *= 3
        power *= 2
    return -c * pow(three, -1, power) % power


def specifications(count):
    # SHA-256 counter stream: fixed bytes, independent of Python PRNG versions.
    synthetic = "".join(f"{b:08b}" for j in range((count + 255) // 256)
                        for b in hashlib.sha256(f"phase13-control-v1:{j}".encode()).digest())[:count]
    thue = [int(j.bit_count() % 2 == 0) for j in range(count)]
    return [
        ("frontierSix", {"kind": "morphism", "one": "100111", "zero": "111110"}),
        ("phase11-110", {"kind": "morphism", "one": "110", "zero": "111"}),
        ("phase11-1011", {"kind": "morphism", "one": "1011", "zero": "1111"}),
        ("phase8-110", {"kind": "morphism", "one": "110", "zero": "011"}),
        ("thue-morse-10", {"kind": "morphism", "one": "10", "zero": "01"}),
        ("alternating", {"kind": "periodic", "period": "10"}),
        ("all-one", {"kind": "periodic", "period": "1"}),
        ("all-zero", {"kind": "periodic", "period": "0"}),
        ("sha256-control", {"kind": "explicit", "bits": synthetic}),
        ("near-rational", {"kind": "explicit", "bits": "10" * 64 + "".join(map(str, thue))[:max(0, count - 128)]}),
    ]


def compute(name, spec, count):
    bits = word(spec, count)
    assert len(bits) == count
    a = residue(bits)
    checkpoints = set(range(1, min(128, count) + 1)) | {count}
    for base in (2, 3, 4, 6):
        k = base
        while k <= count:
            checkpoints.add(k)
            k *= base
    records, metrics = [], []
    old_h, plateau, last_jump, largest_jump = 1, 0, 0, (1, 1)
    minimum, maximum = (float("inf"), 0), (0.0, 0)
    jumps = 0
    tracemalloc.start()
    started = time.perf_counter()
    for n, h, p, q, f, g, transition in profile(a, count):
        if h == old_h:
            plateau += 1
        else:
            jumps += 1
            if h * largest_jump[1] > largest_jump[0] * old_h:
                largest_jump = h, old_h
            last_jump, plateau = n, 1
        ratio = log2(h) / n
        if n >= 128:
            minimum, maximum = min(minimum, (ratio, n)), max(maximum, (ratio, n))
        if n in checkpoints:
            r = {"N": n, "A": a % (1 << n), "H": h, "p": p, "q": q,
                 "gcd": 1, "q_parity": 1, "log2H_over_N": ratio,
                 "algorithm": VERSION, "basis": [list(f), list(g)],
                 "transition": transition, "plateau_age": plateau,
                 "last_height_jump": last_jump,
                 "jump_ratio": [h, old_h] if h != old_h else [1, 1],
                 "minimality": minimality_certificate(a % (1 << n), n, h)}
            # Independent reverse branches, actual parities and proof transcript.
            verify(r, bits)
            records.append(r)
            current, peak = tracemalloc.get_traced_memory()
            metrics.append({"N": n, "elapsed_seconds_including_certification": time.perf_counter() - started,
                            "python_current_bytes": current, "python_peak_bytes": peak})
        old_h = h
    tracemalloc.stop()
    summary = {"jumps": jumps, "largest_jump_ratio": list(largest_jump),
               "minimum_ratio_from_128": list(minimum) if count >= 128 else None,
               "maximum_ratio_from_128": list(maximum) if count >= 128 else None,
               "parity_sha256": hashlib.sha256(bytes(bits)).hexdigest()}
    return {"name": name, "spec": spec, "records": records, "summary": summary}, metrics


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-bits", type=int, default=1024)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    parser.add_argument("--resume", action="store_true")
    args = parser.parse_args()
    if not 1 <= args.max_bits <= MAX_BITS:
        parser.error(f"max-bits must be in 1..{MAX_BITS}")
    target = ROOT / "heights.json"
    if args.check:
        saved = json.loads(target.read_text())
        args.max_bits = saved["max_bits"]
    families, observations = [], []
    partial = ROOT / "resume.json"
    resumed = json.loads(partial.read_text()) if args.resume and partial.exists() else {}
    for name, spec in specifications(args.max_bits):
        if (resumed.get("max_bits") == args.max_bits and name in resumed.get("done", {})):
            family = resumed["done"][name]
            assert family["spec"] == spec
            bits = word(spec, args.max_bits)
            for record in family["records"]:
                verify(record, bits)
            metrics = []
        else:
            family, metrics = compute(name, spec, args.max_bits)
        families.append(family)
        observations.append({"name": name, "records": metrics})
        print(name, "N", args.max_bits, "height bits", family["records"][-1]["H"].bit_length(), flush=True)
        if args.write:
            partial.write_text(json.dumps({"max_bits": args.max_bits,
                                          "done": {f["name"]: f for f in families}}, indent=2) + "\n")
    result = {"format": "phase13-certified-height-v1", "max_bits": args.max_bits, "families": families}
    if args.check:
        assert result == saved, "deterministic height evidence differs"
        print("Exact height evidence reproduced")
    else:
        target.write_text(json.dumps(result, indent=2) + "\n")
        (ROOT / "benchmark.json").write_text(json.dumps({"note": "machine-dependent observations, not proof",
                                                        "families": observations}, indent=2) + "\n")
        partial.unlink(missing_ok=True)


if __name__ == "__main__":
    main()
